/-
  Postern — verified access-policy core for an agentic-context data
  gateway. Single-file Lean 4 artifact paired with a Rust impl that
  is differentially tested against the reference behaviour defined
  here.

  Surface kept deliberately narrow:
    * Plans are single-relation `Scan` / `Project` / `Filter` /
      `Aggregate` trees, plus binary equi-`Join`.
    * `Filter` carries a *predicate term* `Pred`, an ADT with a
      column-reference constructor, a literal constructor, and a
      generic operator/application constructor. `Pred.freeCols`
      computes the free column-reference set of the predicate; the
      rewriter's coverage condition is that every member of this set
      is policy-allowed (paper §4 Theorem 13).
    * Policy carries both column grants and aggregate-only grants
      (`AggGrant`), the latter parameterising the abstract
      differential-privacy boundary `Policy.aggAllowed`.
    * The rewriter returns `Option Plan` — `none` is an explicit
      refusal (unknown relation, predicate references a forbidden
      column, forbidden group-by, or aggregate without admissible
      coverage); `some q'` is a plan whose **output schema** *and*
      **predicate free-column set** are both contained in the
      policy's allowed set (extended with synthesized aggregate
      output-column names admitted via the DP boundary).

  Headline theorems (see `CheckAxioms.lean` for the audited
  axiom set):

    `rewrite_touched`             touched relation preserved
    `rewrite_schema_subset`       output schema ⊆ input schema
    `rewrite_sound`               output columns ⊆ policy-allowedOutputs
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
    `rewrite_sound_aggregate`     Aggregate: each output column is
                                  either directly allowed or a
                                  synthesized aggregate column whose
                                  `(op, col)` is `aggAdmissible`
    `rewrite_groupBy_sound`       Aggregate: every groupBy key is
                                  policy-allowed under the standard
                                  column-grant rule
    `rewrite_refuses_forbidden_aggregate`
                                  aggregate `(op, col)` with neither
                                  column-grant nor AggGrant ⇒ `none`
    `rewrite_filter_coverage`     every free col of every Filter
                                  predicate ⊆ policy-allowed
                                  (Theorem 13 — pointwise restatement
                                  of `rewrite_filter_sound` at the
                                  φ level)

  `rewrite_idempotent`, `rewrite_monotone`, and
  `rewrite_refuses_forbidden_filter` carry a `sorryAx` on the
  `Join` arm (the non-`Join` cases are fully proved); see §6 of
  the paper / `CheckAxioms.lean` for the residual proof surface.

  **What this development does NOT close.** The coverage condition
  controls direct column references in filter predicates. It does
  *not* control inferences an agent can draw from the *values* of
  allowed columns whose distribution is mutually informative with a
  forbidden column (the "probe-one-region-at-a-time" attack of paper
  §6). That half remains the open research question explicitly
  punted in §6.

  The Rust prototype mirrors `Plan`, `Policy`, and `rewrite` byte-
  for-byte; `Main` (the `postern-corpus` exe) emits a JSON corpus
  the Rust harness consumes to assert behavioural equivalence.
-/

namespace Postern

/-! ## Names -/

abbrev Principal := String
abbrev Relation  := String
abbrev Column    := String

/-- Literal values appearing in predicate terms. Strings cover both
    user-supplied constants and (post-tokenization) operator names;
    we keep the type narrow because the rewriter never inspects
    literal values, only the free-column set. -/
abbrev Value := String

/-- Operator label inside `Pred.app` — e.g. `"="`, `"and"`, `"or"`,
    `"not"`, `"lt"`. The rewriter is operator-agnostic; only
    `Pred.ref` contributes to `freeCols`. -/
abbrev Op := String

/-! ## Predicate terms

  A `Pred` is the abstract syntax tree of a filter predicate. The
  rewriter only inspects its *free-column set* (the columns it
  references); operator semantics is the executor's concern. -/

inductive Pred where
  | ref   (col : Column)
  | lit   (val : Value)
  | app   (op  : Op) (args : List Pred)
  deriving Repr, Inhabited

/-- Free-column set of a predicate — every `ref` reachable. Order
    and duplicates are preserved (matching the recursive
    `flatMap`-like fold so the Rust mirror is byte-equal). Nested
    `List Pred` recursion is handled via `attach`, which exposes
    the strict-subterm proof to Lean's termination checker. The
    rewriter's coverage condition is
    `Pred.freeCols φ ⊆ P.allowed p (touched q)`. -/
def Pred.freeCols : Pred → List Column
  | .ref c       => [c]
  | .lit _       => []
  | .app _ args  =>
    args.attach.flatMap (fun ⟨p, _⟩ => p.freeCols)
decreasing_by
  -- `p ∈ args` ⇒ `sizeOf p < sizeOf args`; the `.app` wrapper adds
  -- a constructor's worth on top, so the strict decrease lifts to
  -- the whole term.
  have h := List.sizeOf_lt_of_mem (by assumption)
  simp_wf
  omega

/-! ## Catalog

  A catalog records the columns of each relation in the universe.
  Modelled as a total function so the schema computation has no
  partiality to reason about. An empty column list signals
  "relation unknown to the gateway" — the rewriter refuses such
  plans rather than collapsing them to an empty schema, which would
  be silently vacuous if the executor resolves the scan against a
  real Parquet file. -/

abbrev Catalog := Relation → List Column

/-! ## Aggregation operators

  Closed enumeration matching the SQL standard's core aggregate
  set. The DP-boundary work (paper §6, follow-up) parameterises
  the soundness statement over `AggOp` so that any specific
  mechanism (ε-DP additive noise, k-anonymity, etc.) can be
  bolted on via a refinement of the abstract `aggAllowed` predicate
  without re-mechanising the rewriter. -/

inductive AggOp where
  | sum | count | min | max | avg
  deriving Repr, DecidableEq, Inhabited

/-- The synthesized output-column name for an aggregate result, e.g.
    `Sum_amount`. Kept deterministic so the Rust mirror produces the
    same byte sequence. -/
def AggOp.label : AggOp → String
  | .sum   => "Sum"
  | .count => "Count"
  | .min   => "Min"
  | .max   => "Max"
  | .avg   => "Avg"

def AggOp.outputColumn (op : AggOp) (col : Column) : Column :=
  op.label ++ "_" ++ col

/-! ## Plan IR -/

inductive Plan where
  | scan      (rel  : Relation)
  | project   (sub  : Plan) (cols : List Column)
  /-- Row-only predicate filter. `φ : Pred` is a predicate term; the
      rewriter's coverage condition is `φ.freeCols ⊆ allowed`. -/
  | filter    (sub  : Plan) (φ    : Pred)
  /-- Equi-join of `left` and `right` on a shared column `on`.
      Modelled as the minimum extension that exposes the
      cross-relation surface; multi-key joins / theta-joins
      desugar into `(Join ...) ∘ Filter`. -/
  | join      (left right : Plan) (on : Column)
  /-- Aggregate `op(col)` over `inner`, grouped by `groupBy`. The
      output schema is `groupBy ++ [op.outputColumn col]`. Soundness
      is parameterised over the abstract DP boundary
      (`Policy.aggAllowed`) — see `rewrite_sound_aggregate`. -/
  | aggregate (op : AggOp) (col : Column) (groupBy : List Column) (inner : Plan)
  deriving Repr, Inhabited

/-- The single relation a plan reads from. For `Join` we report
    the *left* leg's touched relation by convention; the join
    soundness theorem (`rewrite_sound_join`) phrases the
    multi-relation claim explicitly via `touched` of both legs
    rather than relying on this single-relation projection. -/
def Plan.touched : Plan → Relation
  | .scan r            => r
  | .project p _       => p.touched
  | .filter  p _       => p.touched
  | .join l _ _        => l.touched
  | .aggregate _ _ _ p => p.touched

/-- Output schema. `Project` keeps only listed columns (intersection
    with sub-schema — projects cannot conjure columns by IR
    construction); `Filter` is row-only; `Join` concatenates left-
    then-right sub-schemas (column-name collisions are the caller's
    responsibility — upstream qualification keeps them disjoint).
    `Aggregate` exposes the group-by columns plus a single
    synthesized result column (`op.outputColumn col`). -/
def Plan.schema (cat : Catalog) : Plan → List Column
  | .scan r                => cat r
  | .project p cs          => (p.schema cat).filter (cs.contains ·)
  | .filter  p _           => p.schema cat
  | .join l r _            => l.schema cat ++ r.schema cat
  | .aggregate op col gb _ => gb ++ [op.outputColumn col]

/-- Columns read by `Filter` predicates anywhere in the plan — the
    union of `Pred.freeCols` over every `Filter` node, distinct from
    the output schema. `rewrite_filter_sound` asserts every member
    is policy-allowed; the predicate-level pointwise restatement is
    `rewrite_filter_coverage` (Theorem 13). The join key is *not* a
    `Filter` read in this sense — the join-key leak is its own
    coverage condition, audited by `rewrite_sound_join` below.

    `Aggregate` recurses into `inner` so filters underneath an
    aggregate are still policed; aggregates themselves are not
    row-selection. -/
def Plan.filterCols : Plan → List Column
  | .scan _            => []
  | .project p _       => p.filterCols
  | .filter  p φ       => φ.freeCols ++ p.filterCols
  | .join l r _        => l.filterCols ++ r.filterCols
  | .aggregate _ _ _ p => p.filterCols

/-- Read-set of every `Aggregate` operator in the plan: the
    `(op, col)` pair drives the DP-boundary side relation. -/
def Plan.aggregates : Plan → List (AggOp × Column)
  | .scan _                => []
  | .project p _           => p.aggregates
  | .filter  p _           => p.aggregates
  | .join l r _            => l.aggregates ++ r.aggregates
  | .aggregate op col _ p  => (op, col) :: p.aggregates

/-- Read-set of every `Aggregate`'s `groupBy` columns. These are
    visible in the output and must be policy-allowed (the standard
    column-grant suffices, no DP boundary needed). -/
def Plan.groupByCols : Plan → List Column
  | .scan _              => []
  | .project p _         => p.groupByCols
  | .filter  p _         => p.groupByCols
  | .join l r _          => l.groupByCols ++ r.groupByCols
  | .aggregate _ _ gb p  => gb ++ p.groupByCols

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

/-- *Aggregate-only* capability — "principal `p` may compute
    `op(col)` over relation `r` even when `col` itself is not in
    `Policy.allowed p r`". The DP boundary (paper §6) refines what
    "may compute" semantically means — bounded noise, ε-budget,
    k-anonymity, etc. We keep that boundary **abstract**: any
    concrete DP mechanism is a refinement of the `AggGrant`
    predicate's runtime check at the executor; the rewriter only
    relies on the grant existing. The soundness theorem is
    correspondingly parameterised — see `rewrite_sound_aggregate`. -/
structure AggGrant where
  principal : Principal
  relation  : Relation
  op        : AggOp
  column    : Column
  deriving Repr, DecidableEq, Inhabited

structure Policy where
  grants    : List Grant
  aggGrants : List AggGrant := []
  deriving Repr, DecidableEq, Inhabited

def Policy.allowed (P : Policy) (prin : Principal) (rel : Relation) : List Column :=
  (P.grants.filter (fun g => g.principal = prin ∧ g.relation = rel)).flatMap Grant.columns

/-- The **abstract DP boundary**: does the policy grant `prin` an
    aggregate-only capability `op(col)` on `rel`? The current
    artifact answers this by checking for a matching `AggGrant`
    (effectively a coarse-grained role gate). A future refinement
    can replace this with a richer predicate (ε-budget remaining,
    k-anonymity threshold met, noise-mechanism parameters present)
    without re-stating the soundness theorem — the rewriter and
    `rewrite_sound_aggregate` are written against this predicate,
    not against any specific DP mechanism. -/
def Policy.aggAllowed (P : Policy) (prin : Principal) (rel : Relation)
    (op : AggOp) (col : Column) : Bool :=
  P.aggGrants.any (fun g =>
    g.principal = prin ∧ g.relation = rel ∧ g.op = op ∧ g.column = col)

/-- Multi-relation generalisation of `touched`. Non-`Join` plans
    have a singleton list — preserving the original single-relation
    invariant; `Join` concatenates its legs. Used by
    `rewrite_sound_join` to phrase the union form
    $\sigma(q') \subseteq \bigcup_i \mathit{allowed}\ p\ \mathit{touched}(q_i)$. -/
def Plan.touchedRels : Plan → List Relation
  | .scan r            => [r]
  | .project p _       => p.touchedRels
  | .filter  p _       => p.touchedRels
  | .join l r _        => l.touchedRels ++ r.touchedRels
  | .aggregate _ _ _ p => p.touchedRels

/-- Flat union of `Policy.allowed` over a list of relations. -/
def Policy.allowedRels (P : Policy) (prin : Principal)
    (rels : List Relation) : List Column :=
  rels.flatMap (P.allowed prin ·)

/-- Predicate driving aggregate admissibility: the aggregate
    `(op, col)` over `rel` for principal `prin` is admissible iff
    either `col` is in the principal's standard column-grant set,
    **or** the policy carries an `AggGrant` (the abstract DP
    boundary `Policy.aggAllowed`). -/
def aggAdmissible (P : Policy) (prin : Principal) (rel : Relation)
    (oc : AggOp × Column) : Bool :=
  (P.allowed prin rel).contains oc.2 || P.aggAllowed prin rel oc.1 oc.2

/-- The set of *output* columns the rewriter will let through on the
    `touched` relation. Extends `Policy.allowed` with one synthesized
    name per admissible aggregate appearing in the plan (a
    `Sum_amount`-style label). The DP boundary lives entirely inside
    `aggAdmissible`; once that returns `true` the synthesized column
    is treated as an ordinary visible column in the output
    projection. -/
def Policy.allowedOutputs (P : Policy) (prin : Principal) (rel : Relation)
    (q : Plan) : List Column :=
  P.allowed prin rel ++
    (q.aggregates.filterMap (fun oc =>
      if aggAdmissible P prin rel oc then some (oc.1.outputColumn oc.2) else none))

/-- Multi-relation lift of `Policy.allowedOutputs`. Flat-unions the
    per-relation allowed-outputs sets over `q.touchedRels`; the
    headline `rewrite_sound` ranges over this for plans of any shape
    (collapses to single-relation `allowedOutputs` for non-`Join`
    plans because their `touchedRels` is a singleton). -/
def Policy.allowedOutputsRels (P : Policy) (prin : Principal)
    (rels : List Relation) (q : Plan) : List Column :=
  rels.flatMap (fun r => P.allowedOutputs prin r q)

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

/-- Single-relation rewriter body. Used by the non-`Join` arm of
    `rewrite` below, and reused as the composition base for the
    `Join` proof. Four nested refusal guards (catalog non-empty;
    filterCols all column-allowed; groupByCols all column-allowed;
    every aggregate `(op, col)` admissible under the abstract DP
    boundary). On accept the schema is filtered by
    `Policy.allowedOutputs`, which equals `allowed` extended with
    synthesized aggregate columns admitted via the boundary. -/
def rewriteLeaf (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) :
    Option Plan :=
  if (cat q.touched).isEmpty then
    none
  else if q.filterCols.all ((P.allowed prin q.touched).contains ·) then
    if q.groupByCols.all ((P.allowed prin q.touched).contains ·) then
      if q.aggregates.all (aggAdmissible P prin q.touched) then
        some (Plan.project q
          ((q.schema cat).filter ((P.allowedOutputs prin q.touched q).contains ·)))
      else
        none
    else
      none
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
  | .aggregate _ _ _ p => by
      have ih := Plan.touched_mem_touchedRels p
      show p.touched ∈ p.touchedRels
      exact ih

/-- Bundled refusal-guard inversion for `rewriteLeaf`: a successful
    leaf rewrite implies catalog non-empty, filter cols all allowed,
    groupBy cols all allowed, all aggregates admissible, and the
    output is the canonical `Project` wrapping. Lets every
    leaf-level proof skip the four nested `by_cases` and just
    `obtain` the four guards plus the shape equality. -/
private theorem rewriteLeaf_accept_inversion
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan)
    (h : rewriteLeaf cat P prin q = some q') :
    (cat q.touched).isEmpty = false ∧
    (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true ∧
    (q.groupByCols.all ((P.allowed prin q.touched).contains ·)) = true ∧
    (q.aggregates.all (aggAdmissible P prin q.touched)) = true ∧
    q' = Plan.project q
          ((q.schema cat).filter ((P.allowedOutputs prin q.touched q).contains ·)) := by
  unfold rewriteLeaf at h
  by_cases hEmpty : (cat q.touched).isEmpty = true
  · rw [if_pos hEmpty] at h; cases h
  · rw [if_neg hEmpty] at h
    by_cases hFilt :
        (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hFilt] at h
      by_cases hGB :
          (q.groupByCols.all ((P.allowed prin q.touched).contains ·)) = true
      · rw [if_pos hGB] at h
        by_cases hAgg :
            (q.aggregates.all (aggAdmissible P prin q.touched)) = true
        · rw [if_pos hAgg] at h
          injection h with hq
          refine ⟨?_, hFilt, hGB, hAgg, hq.symm⟩
          cases hCase : (cat q.touched).isEmpty with
          | false => rfl
          | true  => exact (hEmpty hCase).elim
        · rw [if_neg hAgg] at h; cases h
      · rw [if_neg hGB] at h; cases h
    · rw [if_neg hFilt] at h; cases h

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
  obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin q q' h
  subst hq; rfl

private theorem rewriteLeaf_schema_subset
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ q.schema cat := by
  intro h c hc
  obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin q q' h
  subst hq
  exact (List.mem_filter.mp hc).1

/-- Leaf-level output soundness, generalised to `allowedOutputs`
    (covers the DP-boundary case). The original column-grant form is
    recovered through `rewrite_sound_aggregate` for the no-aggregate
    case (output set ∪ ∅ = standard `allowed`). -/
private theorem rewriteLeaf_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat → c ∈ P.allowedOutputs prin q.touched q := by
  intro h c hc
  obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin q q' h
  subst hq
  have h1 : ((q.schema cat).filter
              ((P.allowedOutputs prin q.touched q).contains ·)).contains c = true :=
    memSelfFilter hc
  have h2 : c ∈ (q.schema cat).filter
                  ((P.allowedOutputs prin q.touched q).contains ·) :=
    List.contains_iff_mem.mp h1
  have h3 : (P.allowedOutputs prin q.touched q).contains c = true :=
    memSelfFilter h2
  exact List.contains_iff_mem.mp h3

private theorem rewriteLeaf_filter_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.filterCols → c ∈ P.allowed prin q.touched := by
  intro h c hc
  obtain ⟨_, hAll, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin q q' h
  subst hq
  have hc' : c ∈ q.filterCols := by
    unfold Plan.filterCols at hc
    exact hc
  have hAllMem := List.all_eq_true.mp hAll
  exact List.contains_iff_mem.mp (hAllMem c hc')

/-- Leaf-level groupBy soundness — each `groupBy` key appears in
    `Plan.groupByCols` and is column-grant-allowed by the leaf's
    refusal guard. -/
private theorem rewriteLeaf_groupBy_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewriteLeaf cat P prin q = some q' →
    ∀ c, c ∈ q'.groupByCols → c ∈ P.allowed prin q.touched := by
  intro h c hc
  obtain ⟨_, _, hGB, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin q q' h
  subst hq
  have hc' : c ∈ q.groupByCols := by
    unfold Plan.groupByCols at hc
    exact hc
  have hGBMem := List.all_eq_true.mp hGB
  exact List.contains_iff_mem.mp (hGBMem c hc')

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
    / `Filter` / `Aggregate`. Used to discharge impossible
    `cases q'` branches in idempotence reasoning. The non-`Join`
    arms are discharged in one line via `rewriteLeaf_accept_inversion`
    — which carries the canonical-`Project` shape directly. -/
private theorem rewrite_output_shape
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan)
    (h : rewrite cat P prin q = some q') :
    (∃ sub cs, q' = .project sub cs) ∨ (∃ l r on, q' = .join l r on) := by
  cases q with
  | scan r =>
    have hLeaf : rewriteLeaf cat P prin (.scan r) = some q' := h
    obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin (.scan r) q' hLeaf
    exact Or.inl ⟨_, _, hq⟩
  | project p cs =>
    have hLeaf : rewriteLeaf cat P prin (.project p cs) = some q' := h
    obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin (.project p cs) q' hLeaf
    exact Or.inl ⟨_, _, hq⟩
  | filter p φ =>
    have hLeaf : rewriteLeaf cat P prin (.filter p φ) = some q' := h
    obtain ⟨_, _, _, _, hq⟩ := rewriteLeaf_accept_inversion cat P prin (.filter p φ) q' hLeaf
    exact Or.inl ⟨_, _, hq⟩
  | aggregate op col gb inner =>
    have hLeaf : rewriteLeaf cat P prin (.aggregate op col gb inner) = some q' := h
    obtain ⟨_, _, _, _, hq⟩ :=
      rewriteLeaf_accept_inversion cat P prin (.aggregate op col gb inner) q' hLeaf
    exact Or.inl ⟨_, _, hq⟩
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

/-- Leaf-level forbidden-aggregate refusal — an aggregate `(op, col)`
    over `q.touched` whose `(op, col)` is *not* `aggAdmissible`
    (i.e. neither column-allowed nor covered by an `AggGrant`)
    forces `rewriteLeaf` to refuse. Used to discharge the top-level
    `rewrite_refuses_forbidden_aggregate` on non-Join inputs. -/
private theorem rewriteLeaf_refuses_forbidden_aggregate
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) (op : AggOp) (col : Column) :
    cat q.touched ≠ [] →
    (op, col) ∈ q.aggregates →
    aggAdmissible P prin q.touched (op, col) = false →
    rewriteLeaf cat P prin q = none := by
  intro hCat hMem hNotAdm
  unfold rewriteLeaf
  have hNotEmpty : ¬ (cat q.touched).isEmpty = true := by
    intro hBool
    apply hCat
    cases hCase : cat q.touched with
    | nil      => rfl
    | cons _ _ => rw [hCase] at hBool; cases hBool
  rw [if_neg hNotEmpty]
  by_cases hFilt :
      (q.filterCols.all ((P.allowed prin q.touched).contains ·)) = true
  · rw [if_pos hFilt]
    by_cases hGB :
        (q.groupByCols.all ((P.allowed prin q.touched).contains ·)) = true
    · rw [if_pos hGB]
      have hNotAll : ¬ (q.aggregates.all (aggAdmissible P prin q.touched)) = true := by
        intro hAll
        have hAllMem := List.all_eq_true.mp hAll
        have := hAllMem (op, col) hMem
        rw [hNotAdm] at this
        cases this
      rw [if_neg hNotAll]
    · rw [if_neg hGB]
  · rw [if_neg hFilt]

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
  | filter p φ   => exact rewriteLeaf_touched cat P prin (.filter p φ) q' h
  | aggregate op col gb inner =>
    exact rewriteLeaf_touched cat P prin (.aggregate op col gb inner) q' h
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
  | filter p φ   => exact rewriteLeaf_schema_subset cat P prin (.filter p φ) q' h c hc
  | aggregate op col gb inner =>
    exact rewriteLeaf_schema_subset cat P prin (.aggregate op col gb inner) q' h c hc
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
    `prin` on *some* relation the plan reads from — either as a
    standard column grant, or as a synthesized aggregate-result
    column whose underlying `(op, col)` is `aggAdmissible` (the
    abstract DP boundary). The statement ranges over the
    multi-relation `allowedOutputsRels` so it covers Joins
    uniformly; non-`Join` plans have a singleton `touchedRels` and
    the claim collapses to `allowedOutputs`. -/
theorem rewrite_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat →
      c ∈ P.allowedOutputsRels prin q.touchedRels q := by
  intro h c hc
  cases q with
  | scan r =>
    have hLeaf := rewriteLeaf_sound cat P prin (.scan r) q' h c hc
    have hShape : (Plan.scan r).touched ∈ (Plan.scan r).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedOutputsRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | project p cs =>
    have hLeaf := rewriteLeaf_sound cat P prin (.project p cs) q' h c hc
    show c ∈ Policy.allowedOutputsRels P prin (Plan.touchedRels (.project p cs)) _
    have hShape : (Plan.project p cs).touched ∈ (Plan.project p cs).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedOutputsRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | filter p φ =>
    have hLeaf := rewriteLeaf_sound cat P prin (.filter p φ) q' h c hc
    show c ∈ Policy.allowedOutputsRels P prin (Plan.touchedRels (.filter p φ)) _
    have hShape : (Plan.filter p φ).touched ∈ (Plan.filter p φ).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedOutputsRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | aggregate op col gb inner =>
    have hLeaf := rewriteLeaf_sound cat P prin (.aggregate op col gb inner) q' h c hc
    show c ∈ Policy.allowedOutputsRels P prin
              (Plan.touchedRels (.aggregate op col gb inner)) _
    have hShape : (Plan.aggregate op col gb inner).touched ∈
                  (Plan.aggregate op col gb inner).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedOutputsRels
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
          -- Per leg, c ∈ allowedOutputsRels prin l.touchedRels l (resp r).
          -- The `Plan.aggregates` of `Join l r on` equals `l.aggregates ++ r.aggregates`,
          -- so each leg's `allowedOutputs` is contained in the Join's per-relation
          -- `allowedOutputs` (since `q.aggregates` for q = Join only adds extra agg
          -- entries, which `filterMap` filters on). For our weaker statement
          -- (membership in `allowedOutputsRels prin (Join.touchedRels) (Join)`), the
          -- per-leg bound suffices since the per-leg `aggregates` is a sublist of
          -- `(Join l r on).aggregates`. Reduce to that via per-leg recursion plus an
          -- `allowedOutputs_sub_of_aggregates_sub` shape (proven below as
          -- `allowedOutputs_mono_aggregates`).
          have legBound :
              c ∈ Policy.allowedOutputsRels P prin l.touchedRels l ∨
              c ∈ Policy.allowedOutputsRels P prin r.touchedRels r := by
            cases hAppend with
            | inl hcl =>
              exact Or.inl (rewrite_sound cat P prin l l' hL c hcl)
            | inr hcr =>
              exact Or.inr (rewrite_sound cat P prin r r' hR c hcr)
          -- Lift to the Join's touchedRels: aggregates of Join include both legs'.
          show c ∈ Policy.allowedOutputsRels P prin (Plan.touchedRels (.join l r on)) _
          have htRels : Plan.touchedRels (.join l r on) = l.touchedRels ++ r.touchedRels := rfl
          rw [htRels]
          unfold Policy.allowedOutputsRels at *
          rw [List.flatMap_append, List.mem_append]
          -- Within each leg's branch, we need to upgrade
          -- `c ∈ allowedOutputs prin <rel> l` to `c ∈ allowedOutputs prin <rel> (Join l r on)`.
          -- The Join's `aggregates` is `l.aggregates ++ r.aggregates`, which is a superset.
          -- We invoke the monotonicity helper below.
          cases legBound with
          | inl h' =>
            apply Or.inl
            rw [List.mem_flatMap] at h' ⊢
            obtain ⟨rel, hRel, hMemOut⟩ := h'
            refine ⟨rel, hRel, ?_⟩
            -- c ∈ allowedOutputs prin rel l ⇒ c ∈ allowedOutputs prin rel (Join l r on)
            unfold Policy.allowedOutputs at hMemOut ⊢
            rw [List.mem_append] at hMemOut ⊢
            cases hMemOut with
            | inl hAllow => exact Or.inl hAllow
            | inr hAgg   =>
              apply Or.inr
              rw [List.mem_filterMap] at hAgg ⊢
              obtain ⟨oc, hocMem, hocSome⟩ := hAgg
              refine ⟨oc, ?_, hocSome⟩
              show oc ∈ (Plan.join l r on).aggregates
              have : (Plan.join l r on).aggregates = l.aggregates ++ r.aggregates := rfl
              rw [this, List.mem_append]
              exact Or.inl hocMem
          | inr h' =>
            apply Or.inr
            rw [List.mem_flatMap] at h' ⊢
            obtain ⟨rel, hRel, hMemOut⟩ := h'
            refine ⟨rel, hRel, ?_⟩
            unfold Policy.allowedOutputs at hMemOut ⊢
            rw [List.mem_append] at hMemOut ⊢
            cases hMemOut with
            | inl hAllow => exact Or.inl hAllow
            | inr hAgg   =>
              apply Or.inr
              rw [List.mem_filterMap] at hAgg ⊢
              obtain ⟨oc, hocMem, hocSome⟩ := hAgg
              refine ⟨oc, ?_, hocSome⟩
              show oc ∈ (Plan.join l r on).aggregates
              have : (Plan.join l r on).aggregates = l.aggregates ++ r.aggregates := rfl
              rw [this, List.mem_append]
              exact Or.inr hocMem
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
  | filter p φ =>
    have hLeaf := rewriteLeaf_filter_sound cat P prin (.filter p φ) q' h c hc
    have hShape : (Plan.filter p φ).touched ∈ (Plan.filter p φ).touchedRels :=
      Plan.touched_mem_touchedRels _
    unfold Policy.allowedRels
    rw [List.mem_flatMap]
    exact ⟨_, hShape, hLeaf⟩
  | aggregate op col gb inner =>
    have hLeaf := rewriteLeaf_filter_sound cat P prin (.aggregate op col gb inner) q' h c hc
    have hShape : (Plan.aggregate op col gb inner).touched ∈
                  (Plan.aggregate op col gb inner).touchedRels :=
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

/-- Rewriting is a closure operator on the output schema: a second
    rewrite admits exactly the same columns as the first.

    Proved fully for the (output-shape-possible) `Project` case via
    the original leaf-shaped argument; the `Scan` / `Filter` /
    `Aggregate` branches are discharged via `rewrite_output_shape`
    (the rewriter never produces a bare scan/filter/aggregate). The
    `Join` case — where both `q` and `q'` are joins — is the open
    obligation tracked in `CheckAxioms.lean` as `sorryAx`. -/
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
    -- Use the converse of `rewrite_output_shape`: if q' is a Project, q must be non-Join.
    have hq_nonjoin :
        (∃ r, q = .scan r) ∨ (∃ p cs', q = .project p cs') ∨
        (∃ p c'', q = .filter p c'') ∨
        (∃ op col gb inner, q = .aggregate op col gb inner) := by
      cases q with
      | scan r       => exact Or.inl ⟨_, rfl⟩
      | project p cs => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      | filter p c'' => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
      | aggregate op col gb inner =>
        exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl⟩))
      | join l r on  =>
        -- A Join input produces a Join output (`rewrite_join_outputs_join`),
        -- contradicting q' = Project sub cs.
        exfalso
        obtain ⟨l', r', hEq⟩ :=
          rewrite_join_outputs_join cat P prin l r on (.project sub cs) h1
        cases hEq
    -- Extract leaf-allowed-output witness via rewriteLeaf_sound on the non-Join q.
    -- `c ∈ P.allowedOutputs prin q.touched q` is what soundness gives us.
    have hLeafOut : c ∈ P.allowedOutputs prin q.touched q := by
      rcases hq_nonjoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, _, _, hq⟩ <;>
        · subst hq
          exact rewriteLeaf_sound cat P prin _ (.project sub cs) h1 c hc
    -- For idempotence, we need `c ∈ P.allowedOutputs prin q'.touched q'`. We get
    -- this by observing q' = project sub cs is the canonical wrapping; its
    -- `aggregates` equal `sub.aggregates`, and `sub` for the wrapped Project is
    -- the *original* q (so q'.aggregates = q.aggregates). Combined with ht the
    -- two allowedOutputs sets are equal.
    have hSubEqQ : sub = q := by
      -- The Project wrapping uses `q` itself as the inner plan.
      -- For non-Join q, `rewrite` reduces to `rewriteLeaf` definitionally.
      have h1Leaf : rewriteLeaf cat P prin q = some (.project sub cs) := by
        rcases hq_nonjoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, _, _, hq⟩ <;>
          · subst hq; exact h1
      have ⟨_, _, _, _, hq⟩ :=
        rewriteLeaf_accept_inversion cat P prin q (.project sub cs) h1Leaf
      -- hq : Plan.project sub cs = Plan.project q (...)
      have hEq : sub = q ∧ cs = (q.schema cat).filter
                    ((P.allowedOutputs prin q.touched q).contains ·) :=
        (Plan.project.injEq _ _ _ _).mp hq
      exact hEq.1
    have hAggEq : (Plan.project sub cs).aggregates = q.aggregates := by
      show sub.aggregates = q.aggregates
      rw [hSubEqQ]
    have hOutEq : P.allowedOutputs prin (Plan.project sub cs).touched (.project sub cs)
                = P.allowedOutputs prin q.touched q := by
      rw [ht]
      unfold Policy.allowedOutputs
      rw [hAggEq]
    have hAllowed : c ∈ P.allowedOutputs prin (Plan.project sub cs).touched
                          (.project sub cs) := by
      rw [hOutEq]; exact hLeafOut
    -- Run h2' through the inversion helper.
    obtain ⟨_, _, _, _, hq2⟩ := rewriteLeaf_accept_inversion cat P prin
                                 (.project sub cs) q'' h2'
    subst hq2
    refine List.mem_filter.mpr ⟨hc, ?_⟩
    have h_in_cs :
        c ∈ ((Plan.project sub cs).schema cat).filter
              ((P.allowedOutputs prin (Plan.project sub cs).touched
                  (.project sub cs)).contains ·) :=
      List.mem_filter.mpr ⟨hc, List.contains_iff_mem.mpr hAllowed⟩
    exact List.contains_iff_mem.mpr h_in_cs
  | inr hJoin =>
    obtain ⟨l, r, on, hShape⟩ := hJoin
    subst hShape
    -- Open obligation: per-leg-idempotence composition through the Join wrapper.
    sorry

/-- **Monotonicity in the policy.** Adding grants — column or
    aggregate — can only *widen* the rewritten output. Captures the
    "more permissions ⇒ more visible" invariant. The hypothesis is
    stated over `allowedOutputs` so it covers both grant kinds in
    one go (column grants strengthen `allowed`; agg grants
    strengthen the `aggAdmissible` branch).

    The non-`Join` cases follow the original argument, recast via the
    inversion helper; the `Join` case is the open obligation tracked
    in `CheckAxioms.lean`. -/
theorem rewrite_monotone
    (cat : Catalog) (P P' : Policy) (prin : Principal) (q q1 q2 : Plan) :
    (∀ p r q0 c, c ∈ P.allowedOutputs p r q0 → c ∈ P'.allowedOutputs p r q0) →
    rewrite cat P  prin q = some q1 →
    rewrite cat P' prin q = some q2 →
    ∀ c, c ∈ q1.schema cat → c ∈ q2.schema cat := by
  intro hSub h1 h2 c hc
  have hcOrig : c ∈ q.schema cat :=
    rewrite_schema_subset cat P prin q q1 h1 c hc
  cases q with
  | scan r =>
    have hAllow  : c ∈ P.allowedOutputs  prin (Plan.scan r).touched (.scan r) :=
      rewriteLeaf_sound cat P prin (.scan r) q1 h1 c hc
    have hAllow' : c ∈ P'.allowedOutputs prin (Plan.scan r).touched (.scan r) :=
      hSub _ _ _ _ hAllow
    obtain ⟨_, _, _, _, hq2⟩ := rewriteLeaf_accept_inversion cat P' prin
                                  (.scan r) q2 h2
    subst hq2
    refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
    have h_in_cs' :
        c ∈ ((Plan.scan r).schema cat).filter
              ((P'.allowedOutputs prin (Plan.scan r).touched (.scan r)).contains ·) :=
      List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
    exact List.contains_iff_mem.mpr h_in_cs'
  | project p cs =>
    have hAllow  : c ∈ P.allowedOutputs  prin (Plan.project p cs).touched
                          (.project p cs) :=
      rewriteLeaf_sound cat P prin (.project p cs) q1 h1 c hc
    have hAllow' : c ∈ P'.allowedOutputs prin (Plan.project p cs).touched
                          (.project p cs) := hSub _ _ _ _ hAllow
    obtain ⟨_, _, _, _, hq2⟩ := rewriteLeaf_accept_inversion cat P' prin
                                  (.project p cs) q2 h2
    subst hq2
    refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
    have h_in_cs' :
        c ∈ ((Plan.project p cs).schema cat).filter
              ((P'.allowedOutputs prin (Plan.project p cs).touched
                  (.project p cs)).contains ·) :=
      List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
    exact List.contains_iff_mem.mpr h_in_cs'
  | filter p φ =>
    have hAllow  : c ∈ P.allowedOutputs  prin (Plan.filter p φ).touched
                          (.filter p φ) :=
      rewriteLeaf_sound cat P prin (.filter p φ) q1 h1 c hc
    have hAllow' : c ∈ P'.allowedOutputs prin (Plan.filter p φ).touched
                          (.filter p φ) := hSub _ _ _ _ hAllow
    obtain ⟨_, _, _, _, hq2⟩ := rewriteLeaf_accept_inversion cat P' prin
                                  (.filter p φ) q2 h2
    subst hq2
    refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
    have h_in_cs' :
        c ∈ ((Plan.filter p φ).schema cat).filter
              ((P'.allowedOutputs prin (Plan.filter p φ).touched
                  (.filter p φ)).contains ·) :=
      List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
    exact List.contains_iff_mem.mpr h_in_cs'
  | aggregate op col gb inner =>
    have hAllow  : c ∈ P.allowedOutputs  prin
                          (Plan.aggregate op col gb inner).touched
                          (.aggregate op col gb inner) :=
      rewriteLeaf_sound cat P prin (.aggregate op col gb inner) q1 h1 c hc
    have hAllow' : c ∈ P'.allowedOutputs prin
                          (Plan.aggregate op col gb inner).touched
                          (.aggregate op col gb inner) := hSub _ _ _ _ hAllow
    obtain ⟨_, _, _, _, hq2⟩ := rewriteLeaf_accept_inversion cat P' prin
                                  (.aggregate op col gb inner) q2 h2
    subst hq2
    refine List.mem_filter.mpr ⟨hcOrig, ?_⟩
    have h_in_cs' :
        c ∈ ((Plan.aggregate op col gb inner).schema cat).filter
              ((P'.allowedOutputs prin (Plan.aggregate op col gb inner).touched
                  (.aggregate op col gb inner)).contains ·) :=
      List.mem_filter.mpr ⟨hcOrig, List.contains_iff_mem.mpr hAllow'⟩
    exact List.contains_iff_mem.mpr h_in_cs'
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
  | filter p φ   => exact rewriteLeaf_refuses_unknown cat P prin (.filter p φ) hEmpty
  | aggregate op col gb inner =>
    exact rewriteLeaf_refuses_unknown cat P prin (.aggregate op col gb inner) hEmpty
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
  | filter p φ   =>
    exact rewriteLeaf_refuses_forbidden_filter cat P prin (.filter p φ) c hCat hMem hNotAllow
  | aggregate op col gb inner =>
    exact rewriteLeaf_refuses_forbidden_filter cat P prin
            (.aggregate op col gb inner) c hCat hMem hNotAllow
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
    the legs' touched relations (extended with synthesized
    aggregate-output columns admitted by the DP boundary):
      $\sigma(\mathit{rewrite}(\mathit{Join}(q_1, q_2)))
       \subseteq P.\mathit{allowedOutputs}\ p\ \mathit{touched}(q_1)\ q
                \cup P.\mathit{allowedOutputs}\ p\ \mathit{touched}(q_2)\ q$.
    Derived as a corollary of the generalised `rewrite_sound`
    plus the `touchedRels` decomposition on joins. -/
theorem rewrite_sound_join
    (cat : Catalog) (P : Policy) (prin : Principal)
    (q1 q2 : Plan) (on : Column) (q' : Plan) :
    rewrite cat P prin (.join q1 q2 on) = some q' →
    ∀ c, c ∈ q'.schema cat →
      c ∈ P.allowedOutputsRels prin q1.touchedRels (.join q1 q2 on) ∨
      c ∈ P.allowedOutputsRels prin q2.touchedRels (.join q1 q2 on) := by
  intro h c hc
  have hgen :=
    rewrite_sound cat P prin (.join q1 q2 on) q' h c hc
  have hSplit : (Plan.join q1 q2 on).touchedRels = q1.touchedRels ++ q2.touchedRels := rfl
  rw [hSplit] at hgen
  unfold Policy.allowedOutputsRels at hgen ⊢
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

/-! ## Aggregation-specific theorems (paper §4 Theorem 12 / §6 C3).

  These theorems mirror the join-arm specialisations above but for
  the abstract DP-boundary surface introduced by `AggGrant` /
  `Policy.aggAllowed`. Each is `sorry`-free and audited in
  `CheckAxioms.lean`. -/

/-- **Aggregate output soundness — the abstract DP boundary in
    action (`rewrite_sound_aggregate`).** For a plan that contains
    aggregates, every column in the rewritten output is **either** a
    standard column-grant on the touched relation **or** a
    synthesized aggregate-result column `op.outputColumn col` whose
    underlying `(op, col)` is `aggAdmissible` — i.e. either `col` is
    itself in `P.allowed` or the policy carries an `AggGrant` (the
    parameterised DP predicate). The boundary is intentionally
    **abstract**: `aggAdmissible` is the seam at which a concrete
    DP mechanism (ε-budget bookkeeping, noise injection, k-anonymity
    threshold) would be wired in by refining `Policy.aggAllowed`
    without re-stating this theorem.

    Stated for the single-relation case (`Scan/Project/Filter/
    Aggregate` inputs — i.e. non-`Join` plans). The proof is direct
    from `rewriteLeaf_sound` (output ⊆ `allowedOutputs`) and the
    definitional unfold of `allowedOutputs` into the union shape. -/
theorem rewrite_sound_aggregate
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    (∃ r, q = .scan r) ∨ (∃ p cs, q = .project p cs) ∨
    (∃ p c, q = .filter p c) ∨
    (∃ op col gb inner, q = .aggregate op col gb inner) →
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.schema cat →
      c ∈ P.allowed prin q.touched ∨
      ∃ op col, (op, col) ∈ q.aggregates ∧
                aggAdmissible P prin q.touched (op, col) = true ∧
                c = op.outputColumn col := by
  intro hNonJoin h c hc
  -- For non-Join q, `rewrite` reduces to `rewriteLeaf`.
  have hLeaf : rewriteLeaf cat P prin q = some q' := by
    rcases hNonJoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, _, _, hq⟩ <;>
      · subst hq; exact h
  have hOut : c ∈ P.allowedOutputs prin q.touched q :=
    rewriteLeaf_sound cat P prin q q' hLeaf c hc
  unfold Policy.allowedOutputs at hOut
  rw [List.mem_append] at hOut
  cases hOut with
  | inl hAllow => exact Or.inl hAllow
  | inr hAgg   =>
      rw [List.mem_filterMap] at hAgg
      obtain ⟨oc, hocMem, hocSome⟩ := hAgg
      by_cases hAdm : aggAdmissible P prin q.touched oc
      · rw [if_pos hAdm] at hocSome
        injection hocSome with hEq
        exact Or.inr ⟨oc.1, oc.2, hocMem, hAdm, hEq.symm⟩
      · rw [if_neg hAdm] at hocSome
        cases hocSome

/-- **Group-by soundness (`rewrite_groupBy_sound`).** Every column
    appearing as a `groupBy` in any aggregate node of the rewritten
    plan is policy-allowed under the standard column-grant rule (no
    DP boundary — group keys appear in the output verbatim). Stated
    for non-`Join` inputs; lifts to `Join` via per-leg recursion. -/
theorem rewrite_groupBy_sound
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    (∃ r, q = .scan r) ∨ (∃ p cs, q = .project p cs) ∨
    (∃ p c, q = .filter p c) ∨
    (∃ op col gb inner, q = .aggregate op col gb inner) →
    rewrite cat P prin q = some q' →
    ∀ c, c ∈ q'.groupByCols → c ∈ P.allowed prin q.touched := by
  intro hNonJoin h c hc
  have hLeaf : rewriteLeaf cat P prin q = some q' := by
    rcases hNonJoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, _, _, hq⟩ <;>
      · subst hq; exact h
  exact rewriteLeaf_groupBy_sound cat P prin q q' hLeaf c hc

/-- **Forbidden-aggregate refusal (`rewrite_refuses_forbidden_aggregate`).**
    An aggregate `(op, col)` over a column the principal can read
    neither directly nor via an `AggGrant` ⇒ `none`. Companion to
    `rewrite_sound_aggregate`. Stated for non-`Join` inputs. -/
theorem rewrite_refuses_forbidden_aggregate
    (cat : Catalog) (P : Policy) (prin : Principal) (q : Plan) (op : AggOp) (col : Column) :
    (∃ r, q = .scan r) ∨ (∃ p cs, q = .project p cs) ∨
    (∃ p c, q = .filter p c) ∨
    (∃ op' col' gb inner, q = .aggregate op' col' gb inner) →
    cat q.touched ≠ [] →
    (op, col) ∈ q.aggregates →
    aggAdmissible P prin q.touched (op, col) = false →
    rewrite cat P prin q = none := by
  intro hNonJoin hCat hMem hNotAdm
  rcases hNonJoin with ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, hq⟩ | ⟨_, _, _, _, hq⟩ <;>
    · subst hq
      exact rewriteLeaf_refuses_forbidden_aggregate cat P prin _ op col hCat hMem hNotAdm

/-! ## Predicate-level coverage condition (paper §4 Theorem 13)

  Pointwise restatement of `rewrite_filter_sound` at the `Pred`
  level. The two are inter-derivable: every column read by a
  `Filter` predicate appears in `Plan.filterCols`, and conversely
  every `c ∈ Plan.filterCols` is the free-column of some predicate
  reachable in the plan. Stated at the φ level so the coverage
  condition reads as a property of *every individual predicate term*
  rather than of the aggregated column list. -/

/-- `Plan.preds q` — every `Pred` term appearing at a `Filter` node
    inside `q`. Outer-to-inner order, no dedup. -/
def Plan.preds : Plan → List Pred
  | .scan _            => []
  | .project p _       => p.preds
  | .filter  p φ       => φ :: p.preds
  | .join l r _        => l.preds ++ r.preds
  | .aggregate _ _ _ p => p.preds

/-- Connection between `Plan.preds` and `Plan.filterCols`: the
    filterCols of `q` are exactly the concatenation of `freeCols`
    over every predicate in `q.preds`. Proved by induction on the
    plan structure. -/
private theorem filterCols_eq_flatMap_preds (q : Plan) :
    q.filterCols = q.preds.flatMap Pred.freeCols := by
  induction q with
  | scan _      => simp [Plan.filterCols, Plan.preds, List.flatMap]
  | project _ _ ih => simp [Plan.filterCols, Plan.preds, ih]
  | filter  _ φ ih =>
    simp [Plan.filterCols, Plan.preds, List.flatMap, ih]
  | join l r _ ihL ihR =>
    simp [Plan.filterCols, Plan.preds, List.flatMap_append, ihL, ihR]
  | aggregate _ _ _ _ ih =>
    simp [Plan.filterCols, Plan.preds, ih]

/-- If `φ ∈ q.preds` then every free column of `φ` is in
    `q.filterCols`. Mechanical consequence of the equation above. -/
private theorem freeCols_subset_filterCols
    (q : Plan) (φ : Pred) (hφ : φ ∈ q.preds)
    (c : Column) (hc : c ∈ φ.freeCols) :
    c ∈ q.filterCols := by
  rw [filterCols_eq_flatMap_preds]
  exact List.mem_flatMap.mpr ⟨φ, hφ, hc⟩

/-- **Theorem 13 — predicate-level coverage condition
    (`rewrite_filter_coverage`).** For every accepted plan, for every
    `Filter` predicate `φ` that appears in the rewritten plan, every
    free column of `φ` lies in the principal's allowed set (extended
    over the plan's `touchedRels`). Pointwise restatement of
    `rewrite_filter_sound` (Theorem 2); closes the side-channel where
    a compound predicate `f(x_1, …, x_n)` is rejected iff *any one*
    `x_i` references a forbidden column, even if every other
    reference is allowed. -/
theorem rewrite_filter_coverage
    (cat : Catalog) (P : Policy) (prin : Principal) (q q' : Plan) :
    rewrite cat P prin q = some q' →
    ∀ φ, φ ∈ q'.preds →
    ∀ c, c ∈ φ.freeCols →
    c ∈ P.allowedRels prin q.touchedRels := by
  intro h φ hφ c hc
  exact rewrite_filter_sound cat P prin q q' h c
    (freeCols_subset_filterCols q' φ hφ c hc)

/-! ## Demonstration -/

namespace Demo

/-- Three relations modelled on the Kaggle financial-transactions
    schema. Unknown relations ⇒ empty list ⇒ refusal. -/
def cat : Catalog
  | "users_data"        => ["id", "name", "email", "ssn", "region", "age"]
  | "cards_data"        => ["card_id", "user_id", "card_number", "card_type", "limit", "activated"]
  | "transactions_data" => ["txn_id", "card_id", "amount", "merchant", "timestamp"]
  | _                    => []

def pol : Policy := {
  grants := [
    { principal := "CRM",       relation := "users_data",
      columns := ["id", "name", "region", "age"] },
    { principal := "CardOps",   relation := "cards_data",
      columns := ["card_id", "card_type", "limit", "activated"] },
    { principal := "FraudRisk", relation := "transactions_data",
      columns := ["txn_id", "card_id", "amount", "merchant", "timestamp"] },
    { principal := "FraudRisk", relation := "users_data",
      columns := ["id", "region"] }
  ],
  aggGrants := [
    -- Analytics is an aggregate-only role: no row-level grants on
    -- `transactions_data`, but may compute `Sum(amount)` and
    -- `Count(txn_id)`. The DP boundary at execution time would
    -- wrap each aggregate in noise / k-anonymity; the rewriter
    -- only inspects the grant.
    { principal := "Analytics", relation := "transactions_data",
      op := .sum, column := "amount" },
    { principal := "Analytics", relation := "transactions_data",
      op := .count, column := "txn_id" }
  ]
}

/-- `region = "EU"` — predicate references only the `region` column. -/
private def regionEU : Pred :=
  .app "=" [.ref "region", .lit "EU"]

/-- `ssn = "..."` — references the forbidden `ssn` column directly. -/
private def ssnEq : Pred :=
  .app "=" [.ref "ssn", .lit "REDACTED"]

/-- `region = "EU" ∧ ssn = "..."` — compound predicate touching one
    allowed and one forbidden column. The coverage condition rejects
    the whole predicate even though `region` alone would be fine. -/
private def regionAndSsn : Pred :=
  .app "and" [regionEU, ssnEq]

#eval (rewrite cat pol "CRM" (.filter (.scan "users_data") regionEU)).map (·.schema cat)
-- expected: some ["id", "name", "region", "age"]

#eval rewrite cat pol "CRM" (.filter (.scan "users_data") ssnEq)
-- expected: none  -- predicate refs forbidden column ⇒ refuse

#eval rewrite cat pol "CRM" (.filter (.scan "users_data") regionAndSsn)
-- expected: none  -- compound predicate with one forbidden ref ⇒ refuse

#eval rewrite cat pol "CRM" (.scan "credit_bureau_imports")
-- expected: none  -- unknown relation ⇒ refuse

-- §C3 — aggregation cases.
#eval (rewrite cat pol "Analytics"
        (.aggregate .sum "amount" [] (.scan "transactions_data"))).map (·.schema cat)
-- expected: some ["Sum_amount"]  -- DP-boundary grant admits Sum(amount)

#eval rewrite cat pol "Analytics"
        (.aggregate .avg "amount" [] (.scan "transactions_data"))
-- expected: none  -- no AggGrant for Avg(amount) and amount ∉ allowed("Analytics", ...)

#eval (rewrite cat pol "FraudRisk"
        (.aggregate .sum "amount" [] (.scan "transactions_data"))).map (·.schema cat)
-- expected: some ["Sum_amount"]  -- amount is directly allowed for FraudRisk

end Demo

end Postern
