import Postern

/-
  Compile-time check that every theorem carrying the artifact's
  correctness claim depends only on Lean's built-in axioms — no
  `sorry`, no user-supplied `axiom`. Lean prints the axiom
  dependencies to the build log; any `sorry` would surface here.

  Expected output (Lean 4.29.1, no Mathlib):

    'rewrite_touched'                       does not depend on any axioms
    'rewrite_schema_subset'                 depends on [propext]
    'rewrite_sound'                         depends on [propext]
    'rewrite_filter_sound'                  depends on [propext]
    'rewrite_no_new_columns'                depends on [propext]
    'rewrite_idempotent'                    depends on [propext]
    'rewrite_monotone'                      depends on [propext]
    'rewrite_refuses_unknown'               does not depend on any axioms
    'rewrite_refuses_forbidden_filter'      depends on [propext]

  `propext` is one of Lean 4's three foundational axioms (the others
  are `Quot.sound` and `Classical.choice`) — its presence reflects
  use of `Iff`-shaped library lemmas (`List.mem_filter`,
  `List.contains_iff_mem`, `List.all_eq_true`), not any
  artifact-specific axiom.
-/

#print axioms Postern.rewrite_touched
#print axioms Postern.rewrite_schema_subset
#print axioms Postern.rewrite_sound
#print axioms Postern.rewrite_filter_sound
#print axioms Postern.rewrite_no_new_columns
#print axioms Postern.rewrite_idempotent
#print axioms Postern.rewrite_monotone
#print axioms Postern.rewrite_refuses_unknown
#print axioms Postern.rewrite_refuses_forbidden_filter
