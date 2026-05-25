import Postern
import Datalog
import Bridge

/-
  Compile-time check that every theorem carrying the artifact's
  correctness claim depends only on Lean's built-in axioms — no
  user-supplied `axiom`. `sorry` would surface here too; any
  `sorry`-marked obligation is named explicitly below so the
  artifact's open work is auditable in one place.

  Expected output (Lean 4.29.1, no Mathlib):

    rewriter (Postern.lean):
      'rewrite_touched'                       depends on [propext, Quot.sound]
      'rewrite_schema_subset'                 depends on [propext, Quot.sound]
      'rewrite_sound'                         depends on [propext, Quot.sound]
                                              -- generalised statement using
                                                 `Plan.touchedRels` + `Policy.allowedOutputsRels`;
                                                 collapses to single-relation form
                                                 for non-`Join` plans, and to the
                                                 standard column-grant form when no
                                                 aggregates are present.
      'rewrite_filter_sound'                  depends on [propext, Quot.sound]
      'rewrite_no_new_columns'                depends on [propext, Quot.sound]
      'rewrite_idempotent'                    depends on [propext, sorryAx, Quot.sound]
                                              -- non-`Join` arm fully proved
                                                 (including the new `Aggregate`
                                                  constructor); `Join` per-leg
                                                 composition open.
      'rewrite_monotone'                      depends on [propext, sorryAx, Quot.sound]
                                              -- non-`Join` arm fully proved
                                                 (including `Aggregate`); `Join`
                                                 widening composition open.
                                              -- hypothesis upgraded to range over
                                                 `Policy.allowedOutputs` so it covers
                                                 both column grants and AggGrants.
      'rewrite_refuses_unknown'               depends on [propext, Quot.sound]
      'rewrite_refuses_forbidden_filter'      depends on [propext, sorryAx, Quot.sound]
                                              -- non-`Join` arm fully proved;
                                                 `Join` cross-leg forbidden-filter open.
      'rewrite_sound_join'                    depends on [propext, Quot.sound]
                                              -- corollary of `rewrite_sound`
                                                 restricted to `Join` inputs, now
                                                 phrased over `allowedOutputsRels`.
      'rewrite_refuses_unallowed_join_key'    depends on [propext, Quot.sound]
                                              -- pure case-analysis on the `Join`
                                                 rewriter's key-membership branch.
                                              -- (Was axiom-free pre-C2; the
                                                 `Pred.freeCols` `attach` recursion
                                                 introduces `Quot.sound` into every
                                                 theorem that unfolds the rewriter.)
      'rewrite_filter_coverage'               depends on [propext, Quot.sound]
                                              -- Theorem 13 — predicate-level
                                                 pointwise restatement of
                                                 `rewrite_filter_sound`. For every
                                                 accepted plan and every Filter
                                                 predicate φ in the rewrite,
                                                 `free(φ) ⊆ allowedRels prin touchedRels`.
                                                 Closes the compound-predicate side
                                                 channel: one forbidden ref taints
                                                 the whole predicate.

    aggregation (Postern.lean — paper §4 Theorem 12 / §6 C3):
      'rewrite_sound_aggregate'               depends on [propext, Quot.sound]
                                              -- abstract DP-boundary soundness for
                                                 non-`Join` plans. Every output column
                                                 is either column-allowed or a
                                                 synthesized `op.outputColumn col`
                                                 whose `(op, col)` is `aggAdmissible`
                                                 (column-grant OR `AggGrant`).
                                                 No specific DP mechanism (ε-DP,
                                                 Laplace, Gaussian, k-anonymity) is
                                                 picked here — a concrete refinement
                                                 replaces `Policy.aggAllowed` without
                                                 re-proving anything.
      'rewrite_groupBy_sound'                 depends on [propext, Quot.sound]
                                              -- groupBy keys are column-grant-allowed
                                                 (no DP boundary, since group keys
                                                  appear verbatim in the output).
      'rewrite_refuses_forbidden_aggregate'   does not depend on any axioms
                                              -- aggregate `(op, col)` with neither
                                                 column-grant nor AggGrant ⇒ `none`.

    Datalog evaluator support lemmas (Datalog.lean — all `sorry`-free):
      'step_extensive'                        depends on [propext]
      'allMatches_subset_facts'               depends on [propext, Quot.sound]
      'step_subset_facts'                     depends on [propext, Quot.sound]
      'step_subset_rules'                     depends on [propext, Quot.sound]
      'step_subset'                           depends on [propext, Quot.sound]
      'iterate_succ_extensive'                depends on [propext]
      'iterate_subset_le'                     depends on [propext]
      'iterate_subset_program'                depends on [propext, Quot.sound]

    Datalog rule-free specialisation (Datalog.lean — all `sorry`-free):
      'eval_fact_mem'                         depends on [propext]
      'step_no_rules'                         depends on [propext]
      'iterate_no_rules'                      depends on [propext]
      'eval_no_rules'                         depends on [propext]

    Combinatorial helpers for `herbrandBound_mono` (Datalog.lean — all proved):
      'length_eraseDups_le'                   depends on [propext, Quot.sound]
      'nodup_eraseDups'                       depends on [propext, Quot.sound]
      'length_le_eraseDups_of_nodup_subset'   depends on [propext, Quot.sound]
      'length_eraseDups_le_of_subset'         depends on [propext, Quot.sound]
      'maxArity_mono'                         depends on [propext, Quot.sound]

    Saturation helper for `eval_terminates` (Datalog.lean — proved):
      'iterate_stable_of_step_stable'         depends on [propext, Quot.sound]

    These four cover the motivating-examples regime (financial-
    institution scenario uses ground `right(_,_,_)` facts only,
    no derivation rules). For that regime `eval P` is mem-set-
    equivalent to `P.facts`, which gives the soundness direction
    unconditionally — a useful baseline pending the full proofs.

    Bridge (Bridge.lean — all `sorry`-free):
      'bridge_allowed'        depends on [propext, Quot.sound]
                              -- closes the column-grant / Datalog gap:
                              -- `Policy.allowed = (Policy.toProgram).allowed`
                              -- as a List Column equality. The translation
                              -- compiles a column-grant Policy to a rule-free
                              -- Program of ground `right(_,_,_)` facts.

    Datalog headline theorems:
      'eval_monotone'        depends on [propext, Quot.sound]
                             -- fully proved; no sorryAx.
      'herbrandBound_mono'   depends on [propext, Quot.sound]
                             -- fully proved; the cardinality obligation
                             -- (`length_le_eraseDups_of_nodup_subset` +
                             -- foldl-max monotonicity) is derived from
                             -- Init stdlib, no Mathlib.
      'eval_sound'           depends on [propext, sorryAx]
                             -- iteration-trace induction; tracked in §6 follow-up.
      'eval_terminates'      depends on [propext, sorryAx]
                             -- Statement *corrected* to membership form
                             -- (the previous list-equality form was
                             -- literally false because `step` appends
                             -- duplicate rule heads). One direction
                             -- (extension via `iterate_subset_le`) is
                             -- proved; the saturation direction is the
                             -- residual sorry. The auxiliary
                             -- `iterate_stable_of_step_stable` reduces
                             -- it to step-stability at the Herbrand
                             -- depth, which still needs the finite-
                             -- Herbrand-base pigeonhole argument.

  `propext` and `Quot.sound` are foundational Lean axioms (the
  third is `Classical.choice`, which we avoid). `sorry` lines are
  the artifact's *open* obligations — they make the residual proof
  surface explicit rather than hiding it inside arbitrary tactic
  black boxes.
-/

-- Rewriter — Postern.lean
#print axioms Postern.rewrite_touched
#print axioms Postern.rewrite_schema_subset
#print axioms Postern.rewrite_sound
#print axioms Postern.rewrite_filter_sound
#print axioms Postern.rewrite_no_new_columns
#print axioms Postern.rewrite_idempotent
#print axioms Postern.rewrite_monotone
#print axioms Postern.rewrite_refuses_unknown
#print axioms Postern.rewrite_refuses_forbidden_filter
-- Join-specific (Plan IR extended with `Join` constructor).
#print axioms Postern.rewrite_sound_join
#print axioms Postern.rewrite_refuses_unallowed_join_key
-- Aggregation-specific (Plan IR extended with `Aggregate` constructor; paper §4 Theorem 12, §6 C3).
-- All three are `sorry`-free under the abstract DP boundary `Policy.aggAllowed`.
#print axioms Postern.rewrite_sound_aggregate
#print axioms Postern.rewrite_groupBy_sound
#print axioms Postern.rewrite_refuses_forbidden_aggregate
-- Predicate-IR coverage (Filter now carries a `Pred` term; paper §4 Theorem 13, §6 C2).
-- Pointwise φ-level restatement of `rewrite_filter_sound`; `sorry`-free.
#print axioms Postern.rewrite_filter_coverage

-- Datalog evaluator — Datalog.lean
#print axioms Postern.Datalog.step_extensive
#print axioms Postern.Datalog.allMatches_subset_facts
#print axioms Postern.Datalog.step_subset_facts
#print axioms Postern.Datalog.step_subset_rules
#print axioms Postern.Datalog.step_subset
#print axioms Postern.Datalog.iterate_succ_extensive
#print axioms Postern.Datalog.iterate_subset_le
#print axioms Postern.Datalog.iterate_subset_program
-- Rule-free specialisation (covers the motivating examples) — all proved.
#print axioms Postern.Datalog.eval_fact_mem
#print axioms Postern.Datalog.step_no_rules
#print axioms Postern.Datalog.iterate_no_rules
#print axioms Postern.Datalog.eval_no_rules
-- Combinatorial helpers underpinning herbrandBound_mono — all proved.
#print axioms Postern.Datalog.length_eraseDups_le
#print axioms Postern.Datalog.nodup_eraseDups
#print axioms Postern.Datalog.length_le_eraseDups_of_nodup_subset
#print axioms Postern.Datalog.length_eraseDups_le_of_subset
#print axioms Postern.Datalog.maxArity_mono
-- Saturation helper underpinning the reverse direction of eval_terminates.
#print axioms Postern.Datalog.iterate_stable_of_step_stable

-- Bridge — Bridge.lean: closes the column-grant / Datalog gap.
-- `bridge_allowed` connects the rewriter's `Policy.allowed` to the
-- Datalog evaluator's `Program.allowed`, by compiling each Grant
-- into one ground `right(prin, rel, c)` fact per column. Fully proved.
#print axioms Postern.bridge_allowed

-- Headline theorems (open obligations isolated as `sorryAx`).
#print axioms Postern.Datalog.eval_monotone
#print axioms Postern.Datalog.herbrandBound_mono
#print axioms Postern.Datalog.eval_sound
#print axioms Postern.Datalog.eval_terminates
