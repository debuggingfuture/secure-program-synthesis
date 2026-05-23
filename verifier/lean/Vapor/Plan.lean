/-
  Vapor.Plan — a tiny relational-plan IR.

  Just enough to state `Rewriter.sound`. The production prototype talks
  Substrait; this IR is a stripped-down decoy we can reason about.
-/

import Vapor.Spec

namespace Vapor.Plan

open Vapor.Spec

/-- Relational-algebra plan. -/
inductive Plan
  | source  (path : ResourcePath)          -- whole-table scan
  | project (cols : List ResourcePath) (p : Plan)
  | filter  (pred : Unit → Bool) (p : Plan)
  | join    (l r : Plan)
  | agg     (groupBy : List ResourcePath) (aggCols : List ResourcePath) (p : Plan)

/-- The set of resource paths the plan touches (columns + tables). -/
def touches : Plan → List ResourcePath
  | .source p          => [p]
  | .project cs p      => cs ++ touches p
  | .filter _ p        => touches p
  | .join l r          => touches l ++ touches r
  | .agg gs cs p       => gs ++ cs ++ touches p

end Vapor.Plan
