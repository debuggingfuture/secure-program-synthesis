/-
  Postern — verified access-policy core for an agentic-context data
  gateway. Single-file Lean 4 artifact paired with a Rust impl that
  is differentially tested against the reference behaviour defined
  here.

  Surface kept deliberately narrow:
    * Plans are single-relation `Scan` / `Project` / `Filter` trees.
    * Policy is a list of (principal, relation, columns) grants.
    * The rewriter returns `Option Plan` — `none` is an explicit
      refusal (unknown relation, or filter on a forbidden column);
      `some q'` is a plan whose **output schema** *and*
      **predicate-column read-set** are both contained in the
      policy's allowed set.

  Headline theorems (all `sorry`-free, see `CheckAxioms.lean` for
  the audited axiom set):

    `rewrite_touched`             touched relation preserved
    `rewrite_schema_subset`       output schema ⊆ input schema
    `rewrite_sound`               output columns ⊆ policy-allowed
    `rewrite_filter_sound`        predicate columns ⊆ policy-allowed
    `rewrite_no_new_columns`      contrapositive of schema-subset
    `rewrite_idempotent`          rewriting twice ≡ once (set-eq)
    `rewrite_monotone`            P ⊆ P' ⇒ output(P) ⊆ output(P')
    `rewrite_refuses_unknown`     unknown relation ⇒ `none`
    `rewrite_refuses_forbidden_filter`
                                  filter on forbidden col ⇒ `none`

  The Rust prototype mirrors `Plan`, `Policy`, and `rewrite` byte-
  for-byte; `Main` (the `postern-corpus` exe) emits a JSON corpus
  the Rust harness consumes to assert behavioural equivalence.
-/

namespace Postern

/-! ## Names -/

abbrev Principal := String
abbrev Relation  := String
abbrev Column    := String

/-! ## Catalog

  A catalog records the columns of each relation in the universe.
  Modelled as a total function so the schema computation has no
  partiality to reason about. An empty column list signals
  "relation unknown to the gateway" — the rewriter refuses such
  plans rather than collapsing them to an empty schema, which would
  be silently vacuous if the executor resolves the scan against a
  real Parquet file. -/

abbrev Catalog := Relation → List Column

/-! ## Plan IR -/

inductive Plan where
  | scan    (rel  : Relation)
  | project (sub  : Plan) (cols : List Column)
  | filter  (sub  : Plan) (col  : Column)
  deriving Repr, DecidableEq, Inhabited

/-- The single relation a plan reads from. -/
def Plan.touched : Plan → Relation
  | .scan r      => r
  | .project p _ => p.touched
  | .filter  p _ => p.touched

/-- Output schema. `Project` keeps only listed columns (intersection
    with sub-schema — projects cannot conjure columns by IR
    construction); `Filter` is row-only. -/
def Plan.schema (cat : Catalog) : Plan → List Column
  | .scan r        => cat r
  | .project p cs  => (p.schema cat).filter (cs.contains ·)
  | .filter  p _   => p.schema cat

/-- Columns read by `Filter` predicates anywhere in the plan — the
    read-set the row-selection logic depends on, distinct from the
    output schema. `rewrite_filter_sound` asserts every member is
    policy-allowed. -/
def Plan.filterCols : Plan → List Column
  | .scan _       => []
  | .project p _  => p.filterCols
  | .filter  p c  => c :: p.filterCols

/-! ## Policy

  Column-grants — "principal `p` may read columns `C` on relation
  `r`". Multiple grants for the same `(p, r)` flat-union. Duplicates
  and insertion order preserved so the Rust mirror matches byte-for-
  byte. Deny-lists are deliberately out of scope (paper §6); the
  policy language is monotone grant-only. -/

structure Grant where
  principal : Principal
  relation  : Relation
  columns   : List Column
  deriving Repr, DecidableEq, Inhabited

abbrev Policy := List Grant

def Policy.allowed (P : Policy) (prin : Principal) (rel : Relation) : List Column :=
  (P.filter (fun g => g.principal = prin ∧ g.relation = rel)).flatMap Grant.columns

/-! ## Rewriter

  Two refusal conditions, both expressed as inline `if`s so that
  `unfold rewrite` produces a shape `split` can decide cleanly:

    1. `cat q.touched = []`               — unknown / un-attested relation.
    2. some col in `q.filterCols` is not allowed — closes the
                                             filter side-channel.

  On accept, the rewriter wraps the plan in a `Project` whose column
  list is `q.schema cat ∩ P.allowed prin q.touched`. -/

def rewrite (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) : Option Plan :=
  if (cat q.touched).isEmpty then
    none
  else if q.filterCols.all ((P.allowed prin q.touched).contains ·) then
    some (Plan.project q ((q.schema cat).filter ((P.allowed prin q.touched).contains ·)))
  else
    none

/-! ## Soundness — `by_cases` + `if_pos`/`if_neg` for the refusals,
    then `List.mem_filter.mp` / `List.contains_iff_mem.mp` as
    function-projections on `Iff` (structure field accesses, not
    `simp`-driven rewrites). The resulting axiom set is audited by
    `CheckAxioms.lean`.

    Because `Plan.schema` for `Project p cs` is itself
    `(p.schema cat).filter (cs.contains ·)`, the rewriter's output
    `Plan.project q ((q.schema cat).filter (allow.contains ·))`
    yields a *double-filtered* schema. The helper `memSelfFilter`
    walks the two filters in one direction; soundness chains
    through it. -/

private theorem memSelfFilter {α : Type _} {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ l.filter p) : p a = true :=
  (List.mem_filter.mp h).2

theorem rewrite_touched
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' → q'.touched = q.touched := by
  intro h
  unfold rewrite at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq; rfl
    · rw [if_neg hAll] at h; cases h

theorem rewrite_schema_subset
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ q.schema cat := by
  intro h c hc
  unfold rewrite at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      exact (List.mem_filter.mp hc).1
    · rw [if_neg hAll] at h; cases h

/-- **Output-column soundness.** Every column in the rewritten plan's
    output schema is one the policy permits for `prin` on the
    relation the plan reads from. -/
theorem rewrite_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ P.allowed prin q.touched := by
  intro h c hc
  unfold rewrite at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      -- hc : c ∈ (q.schema cat).filter (cs.contains ·)
      --       where cs = (q.schema cat).filter (allow.contains ·)
      -- Step 1: outer filter ⇒ cs.contains c = true
      have h1 : ((q.schema cat).filter
                  ((P.allowed prin q.touched).contains ·)).contains c = true :=
        memSelfFilter hc
      -- Step 2: contains ⇒ membership in cs
      have h2 : c ∈ (q.schema cat).filter
                      ((P.allowed prin q.touched).contains ·) :=
        List.contains_iff_mem.mp h1
      -- Step 3: inner filter ⇒ allow.contains c = true
      have h3 : (P.allowed prin q.touched).contains c = true :=
        memSelfFilter h2
      -- Step 4: contains ⇒ membership in allow
      exact List.contains_iff_mem.mp h3
    · rw [if_neg hAll] at h; cases h

/-- **Filter-predicate soundness.** Every column read by a `Filter`
    predicate in the rewritten plan is policy-allowed. Closes the
    side-channel where an agent who cannot *read* a column could
    still use it as a row-selection predicate (`WHERE ssn = ?`). -/
theorem rewrite_filter_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.filterCols → c ∈ P.allowed prin q.touched := by
  intro h c hc
  unfold rewrite at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      -- (Plan.project q _).filterCols = q.filterCols by defn.
      have hc' : c ∈ q.filterCols := by
        unfold Plan.filterCols at hc
        exact hc
      have hAllMem := List.all_eq_true.mp hAll
      exact List.contains_iff_mem.mp (hAllMem c hc')
    · rw [if_neg hAll] at h; cases h

/-- Contrapositive of `rewrite_schema_subset`: a column outside the
    input schema cannot appear in the rewritten output. -/
theorem rewrite_no_new_columns
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) (c : Column) :
    rewrite cat P prin q = some q' →
    c ∉ q.schema cat → c ∉ q'.schema cat := by
  intro h hNot hc
  exact hNot (rewrite_schema_subset cat P prin q q' h c hc)

/-- Rewriting is a closure operator on the output schema: a second
    rewrite admits exactly the same columns as the first. -/
theorem rewrite_idempotent
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' q'' : Plan) :
    rewrite cat P prin q  = some q'  →
    rewrite cat P prin q' = some q'' →
    ∀ c, c ∈ q''.schema cat ↔ c ∈ q'.schema cat := by
  intro h1 h2 c
  refine ⟨rewrite_schema_subset cat P prin q' q'' h2 c, ?_⟩
  intro hc
  have ht := rewrite_touched cat P prin q q' h1
  have hAllowed : c ∈ P.allowed prin q'.touched := by
    have hs : c ∈ P.allowed prin q.touched :=
      rewrite_sound cat P prin q q' h1 c hc
    simpa [ht] using hs
  unfold rewrite at h2
  by_cases hEmpty : (cat q'.touched).isEmpty = true
  · rw [if_pos hEmpty] at h2; cases h2
  · rw [if_neg hEmpty] at h2
    by_cases hAll :
        (q'.filterCols.all ((P.allowed prin q'.touched).contains ·)) = true
    · rw [if_pos hAll] at h2
      injection h2 with hq; subst hq
      -- Goal: c ∈ (q'.schema cat).filter (cs.contains ·)
      --       where cs = (q'.schema cat).filter (allow.contains ·)
      refine List.mem_filter.mpr ⟨hc, ?_⟩
      -- Need: cs.contains c = true
      have h_in_cs : c ∈ (q'.schema cat).filter
                          ((P.allowed prin q'.touched).contains ·) :=
        List.mem_filter.mpr ⟨hc, List.contains_iff_mem.mpr hAllowed⟩
      exact List.contains_iff_mem.mpr h_in_cs
    · rw [if_neg hAll] at h2; cases h2

/-- **Monotonicity in the policy.** Adding grants can only *widen*
    the rewritten output. Captures the "more permissions ⇒ more
    visible" invariant — a reviewer's natural sanity check. -/
theorem rewrite_monotone
    (cat : Catalog) (P P' : Policy) (prin : Principal) (q q1 q2 : Plan) :
    (∀ p r c, c ∈ P.allowed p r → c ∈ P'.allowed p r) →
    rewrite cat P  prin q = some q1 →
    rewrite cat P' prin q = some q2 →
    ∀ c, c ∈ q1.schema cat → c ∈ q2.schema cat := by
  intro hSub h1 h2 c hc
  have hcOrig : c ∈ q.schema cat :=
    rewrite_schema_subset cat P prin q q1 h1 c hc
  have hAllow  : c ∈ P.allowed  prin q.touched :=
    rewrite_sound cat P prin q q1 h1 c hc
  have hAllow' : c ∈ P'.allowed prin q.touched := hSub _ _ _ hAllow
  unfold rewrite at h2
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h2; cases h2
  · rw [if_neg hEmpty] at h2
    by_cases hAll :
        (q.filterCols.all ((P'.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h2
      injection h2 with hq; subst hq
      -- Goal: c ∈ (q.schema cat).filter (cs'.contains ·)
      --       where cs' = (q.schema cat).filter (P'.allowed.contains ·)
      refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
      have h_in_cs' : c ∈ (q.schema cat).filter
                            ((P'.allowed prin q.touched).contains ·) :=
        List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
      exact List.contains_iff_mem.mpr h_in_cs'
    · rw [if_neg hAll] at h2; cases h2

/-- **Unknown-relation refusal.** Empty catalog entry ⇒ `none`. -/
theorem rewrite_refuses_unknown
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) :
    cat q.touched = [] → rewrite cat P prin q = none := by
  intro hEmpty
  unfold rewrite
  have hBool : (cat q.touched).isEmpty = true := by rw [hEmpty]; rfl
  rw [if_pos hBool]

/-- **Forbidden-filter refusal.** A `Filter` reading a column the
    principal can't access ⇒ `none`. Companion to
    `rewrite_filter_sound`. -/
theorem rewrite_refuses_forbidden_filter
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) (c : Column) :
    cat q.touched ≠ [] →
    c ∈ q.filterCols →
    c ∉ P.allowed prin q.touched →
    rewrite cat P prin q = none := by
  intro hCat hMem hNotAllow
  unfold rewrite
  have hNotEmpty : ¬ (cat q.touched).isEmpty = true := by
    intro hBool
    apply hCat
    cases hCase : cat q.touched with
    | nil      => rfl
    | cons _ _ => rw [hCase] at hBool; cases hBool
  rw [if_neg hNotEmpty]
  have hNotAll :
      ¬ (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true := by
    intro hAll
    have hAllMem := List.all_eq_true.mp hAll
    have hContains := hAllMem c hMem
    exact hNotAllow (List.contains_iff_mem.mp hContains)
  rw [if_neg hNotAll]

/-! ## Demonstration -/

namespace Demo

/-- Three relations modelled on the Kaggle financial-transactions
    schema. Unknown relations ⇒ empty list ⇒ refusal. -/
def cat : Catalog
  | "users_data"        => ["id", "name", "email", "ssn", "region", "age"]
  | "cards_data"        => ["card_id", "user_id", "card_number", "card_type", "limit", "activated"]
  | "transactions_data" => ["txn_id", "card_id", "amount", "merchant", "timestamp"]
  | _                    => []

def pol : Policy := [
  { principal := "CRM",       relation := "users_data",
    columns := ["id", "name", "region", "age"] },
  { principal := "CardOps",   relation := "cards_data",
    columns := ["card_id", "card_type", "limit", "activated"] },
  { principal := "FraudRisk", relation := "transactions_data",
    columns := ["txn_id", "card_id", "amount", "merchant", "timestamp"] },
  { principal := "FraudRisk", relation := "users_data",
    columns := ["id", "region"] }
]

#eval (rewrite cat pol "CRM" (.filter (.scan "users_data") "region")).map (·.schema cat)
-- expected: some ["id", "name", "region", "age"]

#eval rewrite cat pol "CRM" (.filter (.scan "users_data") "ssn")
-- expected: none  -- filter on forbidden column ⇒ refuse

#eval rewrite cat pol "CRM" (.scan "credit_bureau_imports")
-- expected: none  -- unknown relation ⇒ refuse

end Demo

end Postern
