/-
  Vapor.Rewriter — policy-aware plan rewriter.

  Two strategies a final version will combine:
    (a) reject — if any touched resource is `forbid` for the principal,
        rewrite to ⊥ (the gateway raises an authorization error).
    (b) restrict — push WHERE / projection / mask under the policy so
        the plan returns ⊑ allowed(P).

  This file stubs the reject-only variant. Soundness for that
  fragment is straightforward and is proved in `Vapor.Thm`.
-/

import Vapor.Spec
import Vapor.Plan

namespace Vapor.Rewriter

open Vapor.Spec
open Vapor.Plan

/-- Decision: rewritten plan, or rejection. -/
inductive Rewrite
  | accept (p : Plan)
  | reject

/-- Reject-on-any-forbid strategy. -/
def rewrite (pol : Policy) (principal : Principal) (q : Plan) : Rewrite :=
  let touched := touches q
  if touched.any (fun r =>
       authorize pol { principal := principal, action := .read, resource := r } = .deny) then
    .reject
  else
    .accept q

end Vapor.Rewriter
