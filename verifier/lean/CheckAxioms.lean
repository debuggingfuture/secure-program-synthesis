import Postern
import Datalog

/-
  Compile-time check that every theorem carrying the artifact's
  correctness claim depends only on Lean's built-in axioms — no
  user-supplied `axiom`. `sorry` would surface here too; any
  `sorry`-marked obligation is named explicitly below so the
  artifact's open work is auditable in one place.

  Expected output (Lean 4.29.1, no Mathlib):

    rewriter (Postern.lean — all `sorry`-free):
      'rewrite_touched'                       does not depend on any axioms
      'rewrite_schema_subset'                 depends on [propext]
      'rewrite_sound'                         depends on [propext]
      'rewrite_filter_sound'                  depends on [propext, Quot.sound]
      'rewrite_no_new_columns'                depends on [propext]
      'rewrite_idempotent'                    depends on [propext]
      'rewrite_monotone'                      depends on [propext]
      'rewrite_refuses_unknown'               does not depend on any axioms
      'rewrite_refuses_forbidden_filter'      depends on [propext, Quot.sound]

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

    These four cover the motivating-examples regime (financial-
    institution scenario uses ground `right(_,_,_)` facts only,
    no derivation rules). For that regime `eval P` is mem-set-
    equivalent to `P.facts`, which gives the soundness direction
    unconditionally — a useful baseline pending the full proofs.

    Datalog headline theorems:
      'eval_monotone'        depends on [propext, sorryAx, Quot.sound]
                             -- sorryAx is via herbrandBound_mono only;
                             -- the rewriter-side of monotonicity is fully proved.
      'herbrandBound_mono'   depends on [sorryAx]
                             -- isolated cardinality obligation:
                             -- |L.eraseDups| under set inclusion.
      'eval_sound'           depends on [propext, sorryAx]
                             -- iteration-trace induction; tracked in §6 follow-up.
      'eval_terminates'      depends on [propext, sorryAx]
                             -- Herbrand-base saturation argument; §6 follow-up.

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
-- Headline theorems (open obligations isolated as `sorryAx`).
#print axioms Postern.Datalog.eval_monotone
#print axioms Postern.Datalog.herbrandBound_mono
#print axioms Postern.Datalog.eval_sound
#print axioms Postern.Datalog.eval_terminates
