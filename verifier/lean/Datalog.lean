/-
  Postern.Datalog — Horn-fragment Datalog over string symbols.

  This file is the policy *language* layer; Postern.lean is the
  plan-rewriter that consumes whatever ground `right(p,r,c)` atoms
  this evaluator derives. The split mirrors how `biscuit-auth`
  separates its Datalog evaluator (`biscuit_auth::datalog::World`)
  from the token surface.

  Narrow scope per the project's path-B-narrow pivot
  (see vault notes 2026-05-25):

    * Pure Horn fragment — no negation, no aggregation, no
      stratification machinery.
    * No attenuation / blocks / audience / expiry / key rotation
      (those are paper §6 future-work items).
    * Terms are `var` or `const`, both ranged over `String`.
      Matches Biscuit's symbol table once interning is applied.

  Headline definitions:

    `Term`, `Atom`, `Rule`, `Program`         syntax
    `Subst`                                   variable assignment
    `Atom.applySubst`, `Atom.matches`         grounding + matching
    `step`                                    one immediate-consequence step
    `iterate`                                 bounded iteration
    `Program.herbrandBound`                   fixpoint depth bound
    `eval`                                    LFP-equivalent evaluator

  Headline theorems (stated here; proofs land alongside in §4 of
  the artifact):

    `eval_monotone`     bigger program → bigger fact set
    `eval_sound`        every derived fact is supported by a rule
                        whose grounded body lies in `eval`
    `eval_terminates`   `iterate` past `herbrandBound` is stable
-/

namespace Postern.Datalog

/-! ## Symbols

  Both predicate names and constants are interned strings. Biscuit
  uses a `SymbolTable` of numeric indices for efficiency; we elide
  interning here and keep equality decidable via `String.decEq`. -/

abbrev Symbol := String

/-! ## Terms -/

inductive Term where
  | var   (name  : Symbol)
  | const (value : Symbol)
  deriving Repr, DecidableEq, Inhabited

def Term.isGround : Term → Bool
  | .const _ => true
  | .var   _ => false

/-! ## Atoms -/

structure Atom where
  pred : Symbol
  args : List Term
  deriving Repr, DecidableEq, Inhabited

def Atom.isGround (a : Atom) : Bool :=
  a.args.all Term.isGround

/-- A ground atom over `String` constants. Convenience constructor
    used by the rewriter when querying the derived fact set. -/
def Atom.ground (pred : Symbol) (args : List Symbol) : Atom :=
  { pred := pred, args := args.map .const }

/-! ## Rules

  Horn clauses: head ← body₁ ∧ … ∧ bodyₙ. A *fact* is the special
  case of an empty body — but we keep facts in `Program.facts` as
  ground atoms directly, to make the evaluator simpler. -/

structure Rule where
  head : Atom
  body : List Atom
  deriving Repr, DecidableEq, Inhabited

/-! ## Programs

  A Datalog program is a set of ground facts together with a set of
  rules. Postern's Biscuit-compatible policies usually have rules
  empty and `right(principal, relation, column)` facts only; the
  evaluator is still defined over the general Horn fragment so that
  derived predicates (e.g. role-inheritance rules) compose without
  re-mechanising. -/

structure Program where
  facts : List Atom
  rules : List Rule
  deriving Repr, DecidableEq, Inhabited

/-! ## Substitutions

  Variable assignment. We use a list of `(name, value)` pairs
  rather than a function so equality is decidable and the proof
  obligations stay first-order. -/

abbrev Subst := List (Symbol × Symbol)

def Subst.lookup (s : Subst) (n : Symbol) : Option Symbol :=
  (s.find? (·.1 = n)).map (·.2)

def Term.applySubst (s : Subst) : Term → Option Term
  | .const v => some (.const v)
  | .var   n => (s.lookup n).map .const

def Atom.applySubst (s : Subst) (a : Atom) : Option Atom := Id.run do
  let mut out : List Term := []
  for t in a.args do
    match Term.applySubst s t with
    | some t' => out := out ++ [t']
    | none    => return none
  return some { pred := a.pred, args := out }

/-! ## Matching

  `matchAtom pattern fact` returns a substitution extending the
  given partial one if `pattern` unifies with the ground `fact`,
  or `none` otherwise. Variables in `pattern` bind to the
  corresponding constants in `fact`; constants must match
  literally. -/

def matchTerm (s : Subst) : Term → Term → Option Subst
  | .const a, .const b => if a = b then some s else none
  | .var   n, .const b =>
      match s.lookup n with
      | some bound => if bound = b then some s else none
      | none       => some ((n, b) :: s)
  | _, _ => none  -- pattern is var/const, fact must be ground const

def matchArgs (s : Subst) : List Term → List Term → Option Subst
  | [], [] => some s
  | p :: ps, f :: fs =>
      match matchTerm s p f with
      | some s' => matchArgs s' ps fs
      | none    => none
  | _, _ => none

def matchAtom (s : Subst) (pattern fact : Atom) : Option Subst :=
  if pattern.pred = fact.pred then
    matchArgs s pattern.args fact.args
  else
    none

/-- All substitutions extending `s` under which every atom in
    `body` matches some fact in `facts`. The cross-product is
    implicit in the recursive structure. -/
def allMatches (facts : List Atom) (s : Subst) : List Atom → List Subst
  | []      => [s]
  | b :: bs =>
      facts.flatMap (fun f =>
        match matchAtom s b f with
        | some s' => allMatches facts s' bs
        | none    => [])

/-! ## Immediate-consequence step -/

/-- Fire every rule whose body is satisfied by `facts`, return the
    grounded heads. Existing facts are preserved. -/
def step (rules : List Rule) (facts : List Atom) : List Atom :=
  let derived : List Atom := rules.flatMap (fun r =>
    (allMatches facts [] r.body).filterMap (fun s =>
      Atom.applySubst s r.head))
  facts ++ derived.filter (fun a => ¬ facts.contains a)

/-- Iterate `step` `n` times. -/
def iterate (rules : List Rule) (facts : List Atom) : Nat → List Atom
  | 0     => facts
  | n + 1 => step rules (iterate rules facts n)

/-! ## Herbrand-universe bound

  The Herbrand base over a program's constants and predicates is
  finite. After at most `|HerbrandBase|` iterations of `step`, no
  new ground atom can be added and the evaluator is stable.

  We compute a *conservative* bound: |predicates| × |constants|^max-arity.
  Tighter bounds exist; this one is enough to underwrite
  `eval_terminates`. -/

def Term.consts : Term → List Symbol
  | .const v => [v]
  | .var   _ => []

def Atom.consts (a : Atom) : List Symbol :=
  a.args.flatMap Term.consts

def Rule.consts (r : Rule) : List Symbol :=
  r.head.consts ++ r.body.flatMap Atom.consts

def Program.consts (P : Program) : List Symbol :=
  (P.facts.flatMap Atom.consts ++ P.rules.flatMap Rule.consts).eraseDups

def Program.predicates (P : Program) : List Symbol :=
  (P.facts.map Atom.pred ++ P.rules.flatMap (fun r =>
    r.head.pred :: r.body.map Atom.pred)).eraseDups

def Program.maxArity (P : Program) : Nat :=
  let arities :=
    P.facts.map (·.args.length) ++
    P.rules.flatMap (fun r => r.head.args.length :: r.body.map (·.args.length))
  arities.foldl max 0

/-- Conservative upper bound on the Herbrand base size: enough
    iterations of `step` to saturate. -/
def Program.herbrandBound (P : Program) : Nat :=
  P.predicates.length * (P.consts.length + 1) ^ P.maxArity + 1

/-! ## Evaluator

  Run `step` for `herbrandBound P` iterations. By
  `eval_terminates`, further iterations are no-ops. -/

def eval (P : Program) : List Atom :=
  iterate P.rules P.facts P.herbrandBound

/-! ## Bridge to Postern's column-grant interface

  The rewriter (`Postern.rewrite`) consults `Policy.allowed prin
  rel : List Column`. We re-derive that interface from the Datalog
  evaluator by querying for ground `right(prin, rel, c)` atoms.

  The predicate name is fixed by Biscuit convention. -/

abbrev RIGHT : Symbol := "right"

def Program.allowed (P : Program) (prin rel : Symbol) : List Symbol :=
  (eval P).filterMap (fun a =>
    if a.pred = RIGHT then
      match a.args with
      | [.const p, .const r, .const c] =>
          if p = prin ∧ r = rel then some c else none
      | _ => none
    else none)

/-! ## Theorems (proofs deferred to §4 — see TODO below)

  Stated here so downstream files can depend on them. Each
  obligation is a one-liner once the supporting lemmas are in
  place; the lemmas themselves are mechanical inductions on
  `iterate` and `step` whose proofs we land in a follow-up. -/

/-- `eval_monotone`: enlarging the fact set or rule set of a
    program can only grow the derived fact set. -/
theorem eval_monotone
    (P P' : Program)
    (hF : ∀ a ∈ P.facts, a ∈ P'.facts)
    (hR : ∀ r ∈ P.rules, r ∈ P'.rules)
    : ∀ a ∈ eval P, a ∈ eval P' := by
  sorry

/-- `eval_sound`: every atom in `eval P` is either a starting fact
    of `P` or the grounded head of some rule of `P` whose grounded
    body is contained in `eval P`. -/
theorem eval_sound
    (P : Program) (a : Atom) (h : a ∈ eval P) :
    a ∈ P.facts ∨
    ∃ r ∈ P.rules, ∃ s : Subst,
      Atom.applySubst s r.head = some a ∧
      ∀ b ∈ r.body, (Atom.applySubst s b).getD a ∈ eval P := by
  sorry

/-- `eval_terminates`: iterating `step` past the Herbrand bound
    adds nothing. -/
theorem eval_terminates
    (P : Program) (k : Nat) :
    iterate P.rules P.facts (P.herbrandBound + k)
      = iterate P.rules P.facts P.herbrandBound := by
  sorry

end Postern.Datalog
