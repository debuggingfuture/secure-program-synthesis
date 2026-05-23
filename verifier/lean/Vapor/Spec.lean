/-
  Vapor.Spec — abstract syntax of the policy DSL.

  Mirrors cedar-spec/cedar-lean's Cedar/Spec.lean style: keep the spec
  small, executable, and the same shape as the production decision
  oracle so differential testing makes sense.

  Status: stub. The actual definitions evolve with paper section 3.
-/

namespace Vapor.Spec

/-- A resource path: source `.` schema `.` table `.` column.
    `column = none` means the whole table. -/
structure ResourcePath where
  source : String
  schema : String
  table  : String
  column : Option String
deriving DecidableEq, Repr

/-- An action the principal might perform on a resource. -/
inductive Action
  | read
  | aggregate
  | write
deriving DecidableEq, Repr

/-- A principal — identity + role + opaque attributes used by `when`. -/
structure Principal where
  id    : String
  role  : String
deriving Repr

/-- Effects à la Cedar. -/
inductive Effect | permit | forbid
deriving DecidableEq, Repr

/-- A single policy rule. `cond` is a placeholder for the WHEN-clause
    predicate; in the real artifact this is the full expression AST. -/
structure Rule where
  effect    : Effect
  action    : Action
  resources : List ResourcePath
  cond      : Principal → Bool   -- placeholder; will become an expr AST
deriving Inhabited

/-- A full policy is a list of rules — order does not matter, see
    `authorize_order_indep` in `Vapor.Thm`. -/
abbrev Policy := List Rule

/-- A request: who, what, on what, in what context. -/
structure Request where
  principal : Principal
  action    : Action
  resource  : ResourcePath
deriving Repr

/-- Decision. -/
inductive Decision | allow | deny
deriving DecidableEq, Repr

/-- Cedar-style evaluation: any matching forbid → deny; else any
    matching permit → allow; else deny. -/
def authorize (p : Policy) (r : Request) : Decision :=
  let matches (rule : Rule) : Bool :=
    rule.action = r.action
    ∧ r.resource ∈ rule.resources
    ∧ rule.cond r.principal
  if p.any (fun rule => rule.effect = .forbid ∧ matches rule) then
    .deny
  else if p.any (fun rule => rule.effect = .permit ∧ matches rule) then
    .allow
  else
    .deny

end Vapor.Spec
