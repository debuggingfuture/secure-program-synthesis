import Postern

/-
  Compile-time check that the three theorems carrying the artifact's
  correctness claim depend only on Lean's built-in axioms — no
  `sorry`, no user-supplied `axiom` declarations. Lean prints the
  axiom dependencies to the build log; any `sorry` would surface here.
-/
#print axioms Postern.rewrite_touched
#print axioms Postern.rewrite_schema_subset
#print axioms Postern.rewrite_sound
