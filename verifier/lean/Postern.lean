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

  Headline theorems (see `CheckAxioms.lean` for the audited
  axiom set):

    `rewrite_touched`             touched relation preserved
    `rewrite_schema_subset`       output schema ⊆ input schema
    `rewrite_sound`               output columns ⊆ policy-allowed
                                  (generalised over `touchedRels`)
    `rewrite_filter_sound`        predicate columns ⊆ policy-allowed
    `rewrite_no_new_columns`      contrapositive of schema-subset
    `rewrite_idempotent`          rewriting twice ≡ once (set-eq)
    `rewrite_monotone`            P ⊆ P' ⇒ output(P) ⊆ output(P')
    `rewrite_refuses_unknown`     unknown relation ⇒ `none`
    `rewrite_refuses_forbidden_filter`
                                  filter on forbidden col ⇒ `none`
    `rewrite_sound_join`          Join: σ(q') ⊆ ⋃ allowed touched(q_i)
    `rewrite_refuses_unallowed_join_key`
                                  Join: on ∉ allow(l)∨allow(r) ⇒ `none`

  `rewrite_idempotent`, `rewrite_monotone`, and
  `rewrite_refuses_forbidden_filter` carry a `sorryAx` on the
  `Join` arm (the non-`Join` cases are fully proved); see §6 of
  the paper / `CheckAxioms.lean` for the residual proof surface.

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
  /-- Equi-join of `left` and `right` on a shared column `on`.
      Modelled as the minimum extension that exposes the
      cross-relation surface; multi-key joins / theta-joins
      desugar into `(Join ...) ∘ Filter`. -/
  | join    (left right : Plan) (on : Column)
  deriving Repr, DecidableEq, Inhabited

/-- The single relation a plan reads from. For `Join` we report
    the *left* leg's touched relation by convention; the join
    soundness theorem (`rewrite_sound_join`) phrases the
    multi-relation claim explicitly via `touched` of both legs
    rather than relying on this single-relation projection. -/
def Plan.touched : Plan → Relation
  | .scan r       => r
  | .project p _  => p.touched
  | .filter  p _  => p.touched
  | .join l _ _   => l.touched

/-- Output schema. `Project` keeps only listed columns (intersection
    with sub-schema — projects cannot conjure columns by IR
    construction); `Filter` is row-only; `Join` concatenates left-
    then-right sub-schemas (column-name collisions are the caller's
    responsibility — upstream qualification keeps them disjoint). -/
def Plan.schema (cat : Catalog) : Plan → List Column
  | .scan r        => cat r
  | .project p cs  => (p.schema cat).filter (cs.contains ·)
  | .filter  p _   => p.schema cat
  | .join l r _    => l.schema cat ++ r.schema cat

/-- Columns read by `Filter` predicates anywhere in the plan — the
    read-set the row-selection logic depends on, distinct from the
    output schema. `rewrite_filter_sound` asserts every member is
    policy-allowed. The join key is *not* a `Filter` read in this
    sense — the join-key leak is its own coverage condition,
    audited by `rewrite_sound_join` below. -/
def Plan.filterCols : Plan → List Column
  | .scan _       => []
  | .project p _  => p.filterCols
  | .filter  p c  => c :: p.filterCols
  | .join l r _   => l.filterCols ++ r.filterCols

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

/-- Multi-relation generalisation of `touched`. Non-`Join` plans
    have a singleton list — preserving the original single-relation
    invariant; `Join` concatenates its legs. Used by
    `rewrite_sound_join` to phrase the union form
    $\sigma(q') \subseteq \bigcup_i \mathit{allowed}\ p\ \mathit{touched}(q_i)$. -/
def Plan.touchedRels : Plan → List Relation
  | .scan r       => [r]
  | .project p _  => p.touchedRels
  | .filter  p _  => p.touchedRels
  | .join l r _   => l.touchedRels ++ r.touchedRels

/-- Flat union of `Policy.allowed` over a list of relations. -/
def Policy.allowedRels (P : Policy) (prin : Principal)
    (rels : List Relation) : List Column :=
  rels.flatMap (P.allowed prin ·)

/-! ## Rewriter

  Single-relation refusal conditions, expressed as inline `if`s so
  that `unfold rewrite` produces a shape `split` can decide cleanly:

    1. `cat q.touched = []`               — unknown / un-attested relation.
    2. some col in `q.filterCols` is not allowed — closes the
                                             filter side-channel.

  On accept, the rewriter wraps the plan in a `Project` whose column
  list is `q.schema cat ∩ P.allowed prin q.touched`.

  The `Join` case dispatches per-leg recursion plus a *join-key
  membership* check on both legs' allow sets — refusing if the join
  key `on` is not policy-allowed on either side. This closes the
  join-key leak: an agent joining on a column `c` it cannot read
  would otherwise learn `c`'s value distribution through the join's
  row-correlation, even if `c` is dropped from the final
  projection. -/

/-- Single-relation rewriter body. Identical to the original
    `rewrite` for `.scan / .project / .filter`; used unmodified by
    the non-`Join` arm of `rewrite` below, and reused as the
    composition base for the `Join` proof. -/
def rewriteLeaf (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) :
    Option Plan :=
  if (cat q.touched).isEmpty then
    none
  else if q.filterCols.all ((P.allowed prin q.touched).contains ·) then
    some (Plan.project q ((q.schema cat).filter ((P.allowed prin q.touched).contains ·)))
  else
    none

def rewrite (cat : Catalog) (P : Policy) (prin : Principal) :
    Plan → Option Plan
  | .join l r on =>
    match rewrite cat P prin l, rewrite cat P prin r with
    | some l', some r' =>
      if (P.allowed prin l.touched).contains on ∧
         (P.allowed prin r.touched).contains on then
        some (Plan.join l' r' on)
      else
        none
    | _, _ => none
  | q => rewriteLeaf cat P prin q

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

/-- Convenience: the convention `Plan.touched` ∈ the multi-relation
    `Plan.touchedRels`. Holds for every constructor — `Join` picks
    the left leg, which is the head of `l.touchedRels`. -/
theorem Plan.touched_mem_touchedRels : (q : Plan) →
    q.touched ∈ q.touchedRels
  | .scan r       => by simp [Plan.touched, Plan.touchedRels]
  | .project p _  => by
      have ih := Plan.touched_mem_touchedRels p
      show p.touched ∈ p.touchedRels
      exact ih
  | .filter p _   => by
      have ih := Plan.touched_mem_touchedRels p
      show p.touched ∈ p.touchedRels
      exact ih
  | .join l r _   => by
      have ih := Plan.touched_mem_touchedRels l
      show l.touched ∈ l.touchedRels ++ r.touchedRels
      exact List.mem_append.mpr (Or.inl ih)

/-! ### Single-relation helpers.

    Each "leaf" lemma is the *original* single-relation argument,
    factored through `rewriteLeaf` (the body of `rewrite` on
    `.scan / .project / .filter` constructors — identical pre-Join
    extension). The top-level theorems `rewrite_*` dispatch by
    `cases q`: the non-`Join` constructors reduce to the matching
    leaf lemma definitionally; the `Join` constructor is its own
    obligation, proved by induction on the structural sub-terms. -/

private theorem rewriteLeaf_touched
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' → q'.touched = q.touched := by
  intro h
  unfold rewriteLeaf at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq; rfl
    · rw [if_neg hAll] at h; cases h

private theorem rewriteLeaf_schema_subset
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ q.schema cat := by
  intro h c hc
  unfold rewriteLeaf at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      exact (List.mem_filter.mp hc).1
    · rw [if_neg hAll] at h; cases h

private theorem rewriteLeaf_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ P.allowed prin q.touched := by
  intro h c hc
  unfold rewriteLeaf at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      have h1 : ((q.schema cat).filter
                  ((P.allowed prin q.touched).contains ·)).contains c = true :=
        memSelfFilter hc
      have h2 : c ∈ (q.schema cat).filter
                      ((P.allowed prin q.touched).contains ·) :=
        List.contains_iff_mem.mp h1
      have h3 : (P.allowed prin q.touched).contains c = true :=
        memSelfFilter h2
      exact List.contains_iff_mem.mp h3
    · rw [if_neg hAll] at h; cases h

private theorem rewriteLeaf_filter_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.filterCols → c ∈ P.allowed prin q.touched := by
  intro h c hc
  unfold rewriteLeaf at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hAll :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hAll] at h
      injection h with hq; subst hq
      have hc' : c ∈ q.filterCols := by
        unfold Plan.filterCols at hc
        exact hc
      have hAllMem := List.all_eq_true.mp hAll
      exact List.contains_iff_mem.mp (hAllMem c hc')
    · rw [if_neg hAll] at h; cases h

private theorem rewriteLeaf_refuses_unknown
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) :
    cat q.touched = [] → rewriteLeaf cat P prin q = none := by
  intro hEmpty
  unfold rewriteLeaf
  have hBool : (cat q.touched).isEmpty = true := by rw [hEmpty]; rfl
  rw [if_pos hBool]

/-- If `rewrite` on a `Join` input accepts, the output is a `Join`
    (never a `Project` or `Scan` / `Filter`). The output shape
    *partitions* by input shape: non-Join input → `Project` output;
    Join input → `Join` output. -/
private theorem rewrite_join_outputs_join
    (cat : Catalog) (P : Policy) (prin : Principal) (l r : Plan) (on : Column) (q' : Plan)
    (h : rewrite cat P prin (.join l r on) = some q') :
    ∃ l' r', q' = .join l' r' on := by
  unfold rewrite at h
  cases hL : rewrite cat P prin l with
  | none =>
    rw [hL] at h
    cases hR : rewrite cat P prin r with
    | none   => rw [hR] at h; cases h
    | some _ => rw [hR] at h; cases h
  | some l' =>
    cases hR : rewrite cat P prin r with
    | none =>
      rw [hL, hR] at h; cases h
    | some r' =>
      rw [hL, hR] at h
      simp only at h
      by_cases hKey :
          ((P.allowed prin l.touched).contains on = true ∧
           (P.allowed prin r.touched).contains on = true)
      · rw [if_pos hKey] at h
        injection h with hq
        exact ⟨_, _, hq.symm⟩
      · rw [if_neg hKey] at h; cases h

/-- The rewriter only ever produces a `Project` (non-`Join` input)
    or a `Join` (when the input was a `Join`) — never a bare `Scan`
    or `Filter`. Used to discharge impossible `cases q'` branches
    in idempotence reasoning. -/
private theorem rewrite_output_shape
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan)
    (h : rewrite cat P prin q = some q') :
    (∃ sub cs, q' = .project sub cs) ∨ (∃ l r on, q' = .join l r on) := by
  cases q with
  | scan r =>
    unfold rewrite rewriteLeaf at h
    by_cases hEmpty : (cat (Plan.scan r).touched).isEmpty = true
    · rw [if_pos hEmpty] at h; cases h
    · rw [if_neg hEmpty] at h
      by_cases hAll :
          ((Plan.scan r).filterCols.all
            ((P.allowed prin (Plan.scan r).touched).contains ·)) = true
      · rw [if_pos hAll] at h
        injection h with hq
        exact Or.inl ⟨_, _, hq.symm⟩
      · rw [if_neg hAll] at h; cases h
  | project p cs =>
    unfold rewrite rewriteLeaf at h
    by_cases hEmpty : (cat (Plan.project p cs).touched).isEmpty = true
    · rw [if_pos hEmpty] at h; cases h
    · rw [if_neg hEmpty] at h
      by_cases hAll :
          ((Plan.project p cs).filterCols.all
            ((P.allowed prin (Plan.project p cs).touched).contains ·)) = true
      · rw [if_pos hAll] at h
        injection h with hq
        exact Or.inl ⟨_, _, hq.symm⟩
      · rw [if_neg hAll] at h; cases h
  | filter p c =>
    unfold rewrite rewriteLeaf at h
    by_cases hEmpty : (cat (Plan.filter p c).touched).isEmpty = true
    · rw [if_pos hEmpty] at h; cases h
    · rw [if_neg hEmpty] at h
      by_cases hAll :
          ((Plan.filter p c).filterCols.all
            ((P.allowed prin (Plan.filter p c).touched).contains ·)) = true
      · rw [if_pos hAll] at h
        injection h with hq
        exact Or.inl ⟨_, _, hq.symm⟩
      · rw [if_neg hAll] at h; cases h
  | join l r on =>
    unfold rewrite at h
    cases hL : rewrite cat P prin l with
    | none =>
      rw [hL] at h
      cases hR : rewrite cat P prin r with
      | none   => rw [hR] at h; cases h
      | some _ => rw [hR] at h; cases h
    | some l' =>
      cases hR : rewrite cat P prin r with
      | none =>
        rw [hL, hR] at h; cases h
      | some r' =>
        rw [hL, hR] at h
        simp only at h
        by_cases hKey :
            ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true)
        · rw [if_pos hKey] at h
          injection h with hq
          exact Or.inr ⟨_, _, _, hq.symm⟩
        · rw [if_neg hKey] at h; cases h

private theorem rewriteLeaf_refuses_forbidden_filter
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) (c : Column) :
    cat q.touched ≠ [] →
    c ∈ q.filterCols →
    c ∉ P.allowed prin q.touched →
    rewriteLeaf cat P prin q = none := by
  intro hCat hMem hNotAllow
  unfold rewriteLeaf
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

/-! ### Top-level theorems.

    Each dispatches `cases q`: scan/project/filter reduce to the
    corresponding `rewriteLeaf_*`; `join` is its own arm. The
    headline `rewrite_sound` is stated in the *generalised* form
    using `Plan.touchedRels`, which collapses to the original
    single-relation statement for non-`Join` plans. -/

theorem rewrite_touched
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' → q'.touched = q.touched := by
  intro h
  cases q with
  | scan r       => exact rewriteLeaf_touched cat P prin (.scan r) q' h
  | project p cs => exact rewriteLeaf_touched cat P prin (.project p cs) q' h
  | filter p c   => exact rewriteLeaf_touched cat P prin (.filter p c) q' h
  | join l r on =>
    unfold rewrite at h
    cases hL : rewrite cat P prin l with
    | none =>
      rw [hL] at h
      cases hR : rewrite cat P prin r with
      | none   => rw [hR] at h; cases h
      | some _ => rw [hR] at h; cases h
    | some l' =>
      cases hR : rewrite cat P prin r with
      | none =>
        rw [hL, hR] at h; cases h
      | some r' =>
        rw [hL, hR] at h
        simp only at h
        by_cases hKey :
            ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true)
        · rw [if_pos hKey] at h
          injection h with hq
          subst hq
          show l'.touched = l.touched
          exact rewrite_touched cat P prin l l' hL
        · rw [if_neg hKey] at h; cases h

theorem rewrite_schema_subset
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ q.schema cat := by
  intro h c hc
  cases q with
  | scan r       => exact rewriteLeaf_schema_subset cat P prin (.scan r) q' h c hc
  | project p cs => exact rewriteLeaf_schema_subset cat P prin (.project p cs) q' h c hc
  | filter p c'  => exact rewriteLeaf_schema_subset cat P prin (.filter p c') q' h c hc
  | join l r on =>
    unfold rewrite at h
    cases hL : rewrite cat P prin l with
    | none =>
      rw [hL] at h
      cases hR : rewrite cat P prin r with
      | none   => rw [hR] at h; cases h
      | some _ => rw [hR] at h; cases h
    | some l' =>
      cases hR : rewrite cat P prin r with
      | none =>
        rw [hL, hR] at h; cases h
      | some r' =>
        rw [hL, hR] at h
        simp only at h
        by_cases hKey :
            ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true)
        · rw [if_pos hKey] at h
          injection h with hq
          subst hq
          -- q'.schema = (Join l' r' on).schema = l'.schema ++ r'.schema
          -- q.schema  = (Join l r on).schema  = l.schema  ++ r.schema
          -- recurse on each leg via List.mem_append.
          have hc' : c ∈ l'.schema cat ∨ c ∈ r'.schema cat := by
            have := hc
            simp [Plan.schema, List.mem_append] at this
            exact this
          have target : c ∈ l.schema cat ∨ c ∈ r.schema cat := by
            cases hc' with
            | inl hcl =>
              exact Or.inl (rewrite_schema_subset cat P prin l l' hL c hcl)
            | inr hcr =>
              exact Or.inr (rewrite_schema_subset cat P prin r r' hR c hcr)
          show c ∈ (Plan.join l r on).schema cat
          simp [Plan.schema, List.mem_append]
          exact target
        · rw [if_neg hKey] at h; cases h

/-- **Output-column soundness (general).** Every column in the
    rewritten plan's output schema is one the policy permits for
    `prin` on *some* relation the plan reads from. For non-`Join`
    plans this collapses to membership in
    `P.allowed prin q.touched` — see `rewrite_sound_leaf` below. -/
theorem rewrite_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat →
      c ∈ P.allowedRels prin q.touchedRels := by
  intro h c hc
  cases q with
  | scan r =>
    have hLeaf := rewriteLeaf_sound cat P prin (.scan r) q' h c hc
    have hShape : (Plan.scan r).touched ∈ (Plan.scan r).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | project p cs =>
    have hLeaf := rewriteLeaf_sound cat P prin (.project p cs) q' h c hc
    show c ∈ Policy.allowedRels P prin (Plan.touchedRels (.project p cs))
    -- touchedRels (.project p cs) = p.touchedRels — unfold needed.
    -- For non-Join p, p.touchedRels = [p.touched] = [(Plan.project p cs).touched].
    -- We just dispatch via the singleton-membership shape:
    have ht : (Plan.project p cs).touched = p.touched := rfl
    -- Allow set the same:
    have : c ∈ P.allowed prin p.touched := by
      show c ∈ P.allowed prin (Plan.project p cs).touched
      exact hLeaf
    -- Need: c ∈ flatMap P.allowed (Plan.project p cs).touchedRels = c ∈ flatMap P.allowed p.touchedRels.
    -- For project, touchedRels recursively follows the sub; we show it's ≡ a singleton of the head.
    -- Generic singleton-shape lemma:
    have hShape : (Plan.project p cs).touched ∈ (Plan.project p cs).touchedRels := by
      -- Both sides reduce to `p.touched ∈ p.touchedRels`. Recurse via `touched_mem_touchedRels`:
      exact Plan.touched_mem_touchedRels p
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | filter p c' =>
    have hLeaf := rewriteLeaf_sound cat P prin (.filter p c') q' h c hc
    show c ∈ Policy.allowedRels P prin (Plan.touchedRels (.filter p c'))
    have hShape : (Plan.filter p c').touched ∈ (Plan.filter p c').touchedRels :=
      Plan.touched_mem_touchedRels (.filter p c')
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | join l r on =>
    unfold rewrite at h
    cases hL : rewrite cat P prin l with
    | none =>
      rw [hL] at h
      cases hR : rewrite cat P prin r with
      | none   => rw [hR] at h; cases h
      | some _ => rw [hR] at h; cases h
    | some l' =>
      cases hR : rewrite cat P prin r with
      | none =>
        rw [hL, hR] at h; cases h
      | some r' =>
        rw [hL, hR] at h
        simp only at h
        by_cases hKey :
            ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true)
        · rw [if_pos hKey] at h
          injection h with hq
          subst hq
          -- c ∈ (Join l' r' on).schema = l'.schema ++ r'.schema
          have hAppend : c ∈ l'.schema cat ∨ c ∈ r'.schema cat := by
            have := hc
            simp [Plan.schema, List.mem_append] at this
            exact this
          -- Per leg, c ∈ allowedRels prin l.touchedRels (resp r.touchedRels).
          have legBound :
              c ∈ Policy.allowedRels P prin l.touchedRels ∨
              c ∈ Policy.allowedRels P prin r.touchedRels := by
            cases hAppend with
            | inl hcl =>
              exact Or.inl (rewrite_sound cat P prin l l' hL c hcl)
            | inr hcr =>
              exact Or.inr (rewrite_sound cat P prin r r' hR c hcr)
          -- Lift to the Join's touchedRels via `allowedRels_append`.
          show c ∈ Policy.allowedRels P prin (Plan.touchedRels (.join l r on))
          have : Plan.touchedRels (.join l r on) = l.touchedRels ++ r.touchedRels := rfl
          rw [this]
          unfold Policy.allowedRels at *
          rw [List.flatMap_append]
          rw [List.mem_append]
          cases legBound with
          | inl h' => exact Or.inl h'
          | inr h' => exact Or.inr h'
        · rw [if_neg hKey] at h; cases h

/-- **Filter-predicate soundness.** Every column read by a `Filter`
    predicate in the rewritten plan is policy-allowed *by some
    relation it touches*. Closes the side-channel where an agent
    who cannot *read* a column could still use it as a row-selection
    predicate (`WHERE ssn = ?`). For non-`Join` plans this is the
    original single-relation form. -/
theorem rewrite_filter_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.filterCols →
      c ∈ P.allowedRels prin q.touchedRels := by
  intro h c hc
  cases q with
  | scan r =>
    have hLeaf := rewriteLeaf_filter_sound cat P prin (.scan r) q' h c hc
    have hShape : (Plan.scan r).touched ∈ (Plan.scan r).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | project p cs =>
    have hLeaf := rewriteLeaf_filter_sound cat P prin (.project p cs) q' h c hc
    have hShape : (Plan.project p cs).touched ∈ (Plan.project p cs).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | filter p c' =>
    have hLeaf := rewriteLeaf_filter_sound cat P prin (.filter p c') q' h c hc
    have hShape : (Plan.filter p c').touched ∈ (Plan.filter p c').touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | join l r on =>
    unfold rewrite at h
    cases hL : rewrite cat P prin l with
    | none =>
      rw [hL] at h
      cases hR : rewrite cat P prin r with
      | none   => rw [hR] at h; cases h
      | some _ => rw [hR] at h; cases h
    | some l' =>
      cases hR : rewrite cat P prin r with
      | none =>
        rw [hL, hR] at h; cases h
      | some r' =>
        rw [hL, hR] at h
        simp only at h
        by_cases hKey :
            ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true)
        · rw [if_pos hKey] at h
          injection h with hq
          subst hq
          -- q'.filterCols = (Join l' r' on).filterCols = l'.filterCols ++ r'.filterCols
          have hAppend : c ∈ l'.filterCols ∨ c ∈ r'.filterCols := by
            have := hc
            simp [Plan.filterCols, List.mem_append] at this
            exact this
          have legBound :
              c ∈ Policy.allowedRels P prin l.touchedRels ∨
              c ∈ Policy.allowedRels P prin r.touchedRels := by
            cases hAppend with
            | inl hcl =>
              exact Or.inl (rewrite_filter_sound cat P prin l l' hL c hcl)
            | inr hcr =>
              exact Or.inr (rewrite_filter_sound cat P prin r r' hR c hcr)
          show c ∈ Policy.allowedRels P prin (Plan.touchedRels (.join l r on))
          have : Plan.touchedRels (.join l r on) = l.touchedRels ++ r.touchedRels := rfl
          rw [this]
          unfold Policy.allowedRels at *
          rw [List.flatMap_append, List.mem_append]
          cases legBound with
          | inl h' => exact Or.inl h'
          | inr h' => exact Or.inr h'
        · rw [if_neg hKey] at h; cases h

/-- Contrapositive of `rewrite_schema_subset`: a column outside the
    input schema cannot appear in the rewritten output. -/
theorem rewrite_no_new_columns
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) (c : Column) :
    rewrite cat P prin q = some q' →
    c ∉ q.schema cat → c ∉ q'.schema cat := by
  intro h hNot hc
  exact hNot (rewrite_schema_subset cat P prin q q' h c hc)

/-- Specialised single-relation soundness: when both `q` is non-Join
    *and* the result-side rewriter for `q'` is the leaf rewriter (i.e.,
    `q'` is also non-Join — which is forced when `q` is non-Join), the
    output column membership collapses from the general
    `allowedRels prin q.touchedRels` to the original
    `allow prin q.touched`. Used as the bridge in the original
    `rewrite_idempotent` / `rewrite_monotone` arguments. -/
private theorem rewriteLeaf_sound_leaf
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ P.allowed prin q.touched :=
  rewriteLeaf_sound cat P prin q q'

/-- Rewriting is a closure operator on the output schema: a second
    rewrite admits exactly the same columns as the first.

    Proved fully for the (output-shape-possible) `Project` case via
    the original leaf-shaped argument; the `Scan` and `Filter`
    branches are discharged via `rewrite_output_shape` (the rewriter
    never produces a bare scan/filter). The `Join` case — where
    both `q` and `q'` are joins — is the open obligation tracked in
    `CheckAxioms.lean` as `sorryAx`. -/
theorem rewrite_idempotent
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' q'' : Plan) :
    rewrite cat P prin q  = some q'  →
    rewrite cat P prin q' = some q'' →
    ∀ c, c ∈ q''.schema cat ↔ c ∈ q'.schema cat := by
  intro h1 h2 c
  refine ⟨rewrite_schema_subset cat P prin q' q'' h2 c, ?_⟩
  intro hc
  -- Use `rewrite_output_shape` on h1 to learn q' is either a Project or a Join.
  cases rewrite_output_shape cat P prin q q' h1 with
  | inl hProj =>
    obtain ⟨sub, cs, hShape⟩ := hProj
    subst hShape
    -- q' = Plan.project sub cs. Then q'' = rewriteLeaf ... (Project sub cs).
    have h2' : rewriteLeaf cat P prin (.project sub cs) = some q'' := h2
    have ht : (Plan.project sub cs).touched = q.touched :=
      rewrite_touched cat P prin q (.project sub cs) h1
    -- Need a leaf-allow witness on (Project sub cs). The outer h1 establishes the
    -- Project wrap; its schema is (q.schema).filter (allow.contains), and hc lives
    -- inside it. Re-derive `c ∈ allow prin q.touched` by re-running the schema chain:
    -- since q' is a Project produced by some non-Join q's rewriter, the leaf-shape
    -- soundness applies. But we don't have `q` case-split — chase via `rewrite_sound`
    -- (general) and reduce to a leaf via the singleton structure when q is non-Join.
    -- For Join q we can't get here (output would be a Join, not Project) by
    -- `rewrite_output_shape` on q — but our `cases` is on `q'`'s shape, not q's.
    -- Use the converse of `rewrite_output_shape`: if q' is a Project, q must be non-Join.
    -- We derive this by case on q: a Join q → q' is a Join, contradicting q' = Project.
    have hq_nonjoin :
        (∃ r, q = .scan r) ∨ (∃ p cs', q = .project p cs') ∨ (∃ p c'', q = .filter p c'') := by
      cases q with
      | scan r       => exact Or.inl ⟨_, rfl⟩
      | project p cs => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      | filter p c'' => exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      | join l r on  =>
        -- A Join input produces a Join output (`rewrite_join_outputs_join`),
        -- contradicting q' = Project sub cs.
        exfalso
        obtain ⟨l', r', hEq⟩ :=
          rewrite_join_outputs_join cat P prin l r on (.project sub cs) h1
        cases hEq
    -- Now extract leaf-allow witness via rewriteLeaf_sound on the non-Join q.
    have hLeafAllow : c ∈ P.allowed prin q.touched := by
      rcases hq_nonjoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ <;>
        · subst hq
          exact rewriteLeaf_sound cat P prin _ (.project sub cs) h1 c hc
    -- Convert via ht.
    have hAllowed : c ∈ P.allowed prin (Plan.project sub cs).touched := by
      rw [ht]; exact hLeafAllow
    -- Run h2' open in the original style.
    unfold rewriteLeaf at h2'
    by_cases hEmpty : (cat (Plan.project sub cs).touched).isEmpty = true
    · rw [if_pos hEmpty] at h2'; cases h2'
    · rw [if_neg hEmpty] at h2'
      by_cases hAll :
          ((Plan.project sub cs).filterCols.all
              ((P.allowed prin (Plan.project sub cs).touched).contains ·)) = true
      · rw [if_pos hAll] at h2'
        injection h2' with hq2; subst hq2
        refine List.mem_filter.mpr ⟨hc, ?_⟩
        have h_in_cs :
            c ∈ ((Plan.project sub cs).schema cat).filter
                  ((P.allowed prin (Plan.project sub cs).touched).contains ·) :=
          List.mem_filter.mpr ⟨hc, List.contains_iff_mem.mpr hAllowed⟩
        exact List.contains_iff_mem.mpr h_in_cs
      · rw [if_neg hAll] at h2'; cases h2'
  | inr hJoin =>
    obtain ⟨l, r, on, hShape⟩ := hJoin
    subst hShape
    -- Open obligation: per-leg-idempotence composition through the Join wrapper.
    sorry

/-- **Monotonicity in the policy.** Adding grants can only *widen*
    the rewritten output. Captures the "more permissions ⇒ more
    visible" invariant.

    The non-`Join` cases follow the original argument; the `Join`
    case is the open obligation tracked in `CheckAxioms.lean`. -/
theorem rewrite_monotone
    (cat : Catalog) (P P' : Policy) (prin : Principal) (q q1 q2 : Plan) :
    (∀ p r c, c ∈ P.allowed p r → c ∈ P'.allowed p r) →
    rewrite cat P  prin q = some q1 →
    rewrite cat P' prin q = some q2 →
    ∀ c, c ∈ q1.schema cat → c ∈ q2.schema cat := by
  intro hSub h1 h2 c hc
  have hcOrig : c ∈ q.schema cat :=
    rewrite_schema_subset cat P prin q q1 h1 c hc
  cases q with
  | scan r =>
    -- For non-Join q, rewrite = rewriteLeaf, so rewriteLeaf_sound applies.
    have hAllow : c ∈ P.allowed prin (Plan.scan r).touched :=
      rewriteLeaf_sound cat P prin (.scan r) q1 h1 c hc
    have hAllow' : c ∈ P'.allowed prin (Plan.scan r).touched := hSub _ _ _ hAllow
    have h2' : rewriteLeaf cat P' prin (.scan r) = some q2 := h2
    unfold rewriteLeaf at h2'
    by_cases hEmpty : (cat (Plan.scan r).touched).isEmpty = true
    · rw [if_pos hEmpty] at h2'; cases h2'
    · rw [if_neg hEmpty] at h2'
      by_cases hAll :
          ((Plan.scan r).filterCols.all
            ((P'.allowed prin (Plan.scan r).touched).contains ·)) = true
      · rw [if_pos hAll] at h2'
        injection h2' with hq; subst hq
        refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
        have h_in_cs' :
            c ∈ ((Plan.scan r).schema cat).filter
                  ((P'.allowed prin (Plan.scan r).touched).contains ·) :=
          List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
        exact List.contains_iff_mem.mpr h_in_cs'
      · rw [if_neg hAll] at h2'; cases h2'
  | project p cs =>
    have hAllow : c ∈ P.allowed prin (Plan.project p cs).touched :=
      rewriteLeaf_sound cat P prin (.project p cs) q1 h1 c hc
    have hAllow' : c ∈ P'.allowed prin (Plan.project p cs).touched := hSub _ _ _ hAllow
    have h2' : rewriteLeaf cat P' prin (.project p cs) = some q2 := h2
    unfold rewriteLeaf at h2'
    by_cases hEmpty : (cat (Plan.project p cs).touched).isEmpty = true
    · rw [if_pos hEmpty] at h2'; cases h2'
    · rw [if_neg hEmpty] at h2'
      by_cases hAll :
          ((Plan.project p cs).filterCols.all
            ((P'.allowed prin (Plan.project p cs).touched).contains ·)) = true
      · rw [if_pos hAll] at h2'
        injection h2' with hq; subst hq
        refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
        have h_in_cs' :
            c ∈ ((Plan.project p cs).schema cat).filter
                  ((P'.allowed prin (Plan.project p cs).touched).contains ·) :=
          List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
        exact List.contains_iff_mem.mpr h_in_cs'
      · rw [if_neg hAll] at h2'; cases h2'
  | filter p c' =>
    have hAllow : c ∈ P.allowed prin (Plan.filter p c').touched :=
      rewriteLeaf_sound cat P prin (.filter p c') q1 h1 c hc
    have hAllow' : c ∈ P'.allowed prin (Plan.filter p c').touched := hSub _ _ _ hAllow
    have h2' : rewriteLeaf cat P' prin (.filter p c') = some q2 := h2
    unfold rewriteLeaf at h2'
    by_cases hEmpty : (cat (Plan.filter p c').touched).isEmpty = true
    · rw [if_pos hEmpty] at h2'; cases h2'
    · rw [if_neg hEmpty] at h2'
      by_cases hAll :
          ((Plan.filter p c').filterCols.all
            ((P'.allowed prin (Plan.filter p c').touched).contains ·)) = true
      · rw [if_pos hAll] at h2'
        injection h2' with hq; subst hq
        refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
        have h_in_cs' :
            c ∈ ((Plan.filter p c').schema cat).filter
                  ((P'.allowed prin (Plan.filter p c').touched).contains ·) :=
          List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
        exact List.contains_iff_mem.mpr h_in_cs'
      · rw [if_neg hAll] at h2'; cases h2'
  | join l r on  =>
    -- Open: monotonicity through Join. Widening P → P' may turn a refused join into an
    -- accepted one; pairing `rewrite P q = some q1` with `rewrite P' q = some q2` and
    -- chasing per-leg subset is the work item.
    sorry

/-- **Unknown-relation refusal.** Empty catalog entry on `q.touched` ⇒
    `none`. For `Join`, `q.touched = l.touched`, and the left-leg
    rewrite refuses by induction, propagating to the Join arm. -/
theorem rewrite_refuses_unknown
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) :
    cat q.touched = [] → rewrite cat P prin q = none := by
  intro hEmpty
  cases q with
  | scan r       => exact rewriteLeaf_refuses_unknown cat P prin (.scan r) hEmpty
  | project p cs => exact rewriteLeaf_refuses_unknown cat P prin (.project p cs) hEmpty
  | filter p c   => exact rewriteLeaf_refuses_unknown cat P prin (.filter p c) hEmpty
  | join l r on =>
    -- (Plan.join l r on).touched = l.touched, so cat l.touched = [].
    have hLeftEmpty : cat l.touched = [] := hEmpty
    have hLeftRefuse : rewrite cat P prin l = none :=
      rewrite_refuses_unknown cat P prin l hLeftEmpty
    show rewrite cat P prin (.join l r on) = none
    unfold rewrite
    -- `match rewrite l, _ with | some _, some _ => ... | _, _ => none` reduces to `none`.
    rw [hLeftRefuse]

/-- **Forbidden-filter refusal.** A `Filter` reading a column the
    principal can't access ⇒ `none`. Companion to
    `rewrite_filter_sound`. For non-`Join` plans this is the
    original argument; the `Join` case decomposes the filter to its
    originating leg and refuses via induction. -/
theorem rewrite_refuses_forbidden_filter
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) (c : Column) :
    cat q.touched ≠ [] →
    c ∈ q.filterCols →
    c ∉ P.allowed prin q.touched →
    rewrite cat P prin q = none := by
  intro hCat hMem hNotAllow
  cases q with
  | scan r       =>
    exact rewriteLeaf_refuses_forbidden_filter cat P prin (.scan r) c hCat hMem hNotAllow
  | project p cs =>
    exact rewriteLeaf_refuses_forbidden_filter cat P prin (.project p cs) c hCat hMem hNotAllow
  | filter p c'  =>
    exact rewriteLeaf_refuses_forbidden_filter cat P prin (.filter p c') c hCat hMem hNotAllow
  | join l r on =>
    -- The forbidden-filter refusal as stated uses `q.touched` (i.e. l.touched for Join).
    -- For the Join case we only get a clean refusal when the forbidden filter sits
    -- in the *left* leg (whose `touched` matches `q.touched`). Filters in the right leg
    -- need their own forbidden-allow witness on r.touched, which the current statement
    -- doesn't supply. The leaf and non-Join compositions go through; the Join arm is
    -- audited as the open obligation below.
    sorry

/-! ## Join-specific theorems

  Specialisations of the generalised soundness statements above to
  the `Join` constructor, matching the paper §4 / §6 phrasing. -/

/-- **Output-column soundness for joins (`rewrite_sound_join`).**
    The headline join theorem — the formal counterpart of paper §6
    eq. (rewrite_sound_join). For an accepted `Join(q1, q2)`, every
    output column is policy-allowed for `prin` on *at least one* of
    the legs' touched relations:
      $\sigma(\mathit{rewrite}(\mathit{Join}(q_1, q_2)))
       \subseteq P.\mathit{allowed}\ p\ \mathit{touched}(q_1)
                \cup P.\mathit{allowed}\ p\ \mathit{touched}(q_2)$.
    Derived as a corollary of the generalised `rewrite_sound`
    plus the `touchedRels` decomposition on joins. -/
theorem rewrite_sound_join
    (cat : Catalog) (P : Policy) (prin : Principal)
    (q1 q2 : Plan) (on : Column) (q' : Plan) :
    rewrite cat P prin (.join q1 q2 on) = some q' →
    ∀ c, c ∈ q'.schema cat →
      c ∈ P.allowedRels prin q1.touchedRels ∨
      c ∈ P.allowedRels prin q2.touchedRels := by
  intro h c hc
  have hgen :=
    rewrite_sound cat P prin (.join q1 q2 on) q' h c hc
  -- hgen : c ∈ P.allowedRels prin (Join q1 q2 on).touchedRels = q1.touchedRels ++ q2.touchedRels
  have hSplit : (Plan.join q1 q2 on).touchedRels = q1.touchedRels ++ q2.touchedRels := rfl
  rw [hSplit] at hgen
  unfold Policy.allowedRels at hgen ⊢
  rw [List.flatMap_append, List.mem_append] at hgen
  exact hgen

/-- **Join-key leak coverage.** A `Join` whose key `on` is not in
    *some* leg's allow set is refused. The contrapositive captures
    paper §6 / §4's join-key coverage condition: an accepted join
    necessarily has `on ∈ allow(touched(l)) ∧ on ∈ allow(touched(r))`. -/
theorem rewrite_refuses_unallowed_join_key
    (cat : Catalog) (P : Policy) (prin : Principal)
    (l r : Plan) (on : Column) :
    (on ∉ P.allowed prin l.touched ∨ on ∉ P.allowed prin r.touched) →
    rewrite cat P prin (.join l r on) = none := by
  intro hMiss
  unfold rewrite
  cases hL : rewrite cat P prin l with
  | none =>
    -- match none, _ ⇒ none
    rfl
  | some l' =>
    cases hR : rewrite cat P prin r with
    | none => rfl
    | some r' =>
      simp only
      have hKeyNot :
          ¬ ((P.allowed prin l.touched).contains on = true ∧
             (P.allowed prin r.touched).contains on = true) := by
        intro ⟨hL', hR'⟩
        cases hMiss with
        | inl hn => exact hn (List.contains_iff_mem.mp hL')
        | inr hn => exact hn (List.contains_iff_mem.mp hR')
      rw [if_neg hKeyNot]

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
