/-
  Vapor.Thm — top-level theorems.

  At paper-time we'll prove:
    * `authorize_order_indep` — `authorize` ignores rule order.
    * `rewriter_sound` — `eval(rewrite(q,P)) ⊑ eval(q) ∩ allowed(P)`
      for the reject-only strategy stated in `Rewriter`.
    * `rewriter_transparent` — if no policy denies any touched resource,
      `rewrite(q,P) = accept q`.
    * `ingest_compose` — read-side rewrite + write-side ingest filter
      yield identical observable sets (the headline novelty).

  All theorems below are stubs (`sorry`-free skeletons would replace
  `sorry` with the actual proofs). Listed here so the Lean structure
  matches the paper outline.
-/

import Vapor.Spec
import Vapor.Plan
import Vapor.Rewriter

namespace Vapor.Thm

open Vapor.Spec
open Vapor.Plan
open Vapor.Rewriter

/-- Rule order does not change `authorize`'s decision. -/
theorem authorize_order_indep
    (pol pol' : Policy) (r : Request)
    (h : pol.Perm pol') :  -- list permutation
    authorize pol r = authorize pol' r := by
  sorry

/-- If no touched resource is denied for the principal, the rewriter
    is transparent. -/
theorem rewriter_transparent
    (pol : Policy) (p : Principal) (q : Plan)
    (h : ∀ r ∈ touches q,
           authorize pol { principal := p, action := .read, resource := r } ≠ .deny) :
    rewrite pol p q = .accept q := by
  sorry

/-- Soundness (reject-only variant): if `rewrite` returns `accept q'`,
    then every touched resource of `q'` is permitted for the principal. -/
theorem rewriter_sound_reject
    (pol : Policy) (p : Principal) (q q' : Plan)
    (h : rewrite pol p q = .accept q') :
    ∀ r ∈ touches q',
      authorize pol { principal := p, action := .read, resource := r } ≠ .deny := by
  sorry

end Vapor.Thm
