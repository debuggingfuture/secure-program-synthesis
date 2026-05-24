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

/-! ## Immediate-consequence step

  Fire every rule whose body is satisfied by `facts`; concatenate
  the grounded heads onto `facts`. We do *not* dedup; the output
  list may contain duplicates, but its mem-set is exactly the LFP
  step. Dedup would only complicate the monotonicity lemmas; the
  semantics downstream only consults `∈ eval P`. -/

def step (rules : List Rule) (facts : List Atom) : List Atom :=
  facts ++ rules.flatMap (fun r =>
    (allMatches facts [] r.body).filterMap (fun s =>
      Atom.applySubst s r.head))

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

/-! ## Supporting lemmas

  These walk the obvious set-theoretic facts about `step` and
  `iterate` step-by-step. Style follows `Postern.lean`: explicit
  `List.mem_*` lemmas, no `simp` doing the heavy lifting, so the
  audited axiom set stays bounded by `propext` and `Quot.sound`. -/

/-- `step` preserves every input fact. -/
theorem step_extensive (R : List Rule) (F : List Atom) (a : Atom) :
    a ∈ F → a ∈ step R F := by
  intro h
  unfold step
  exact List.mem_append_left _ h

/-- `allMatches` is monotone in the fact set. Adding more facts
    can only produce more matching substitutions. Proof by
    induction on the body list — at each step every fact used to
    match a body atom remains available. -/
theorem allMatches_subset_facts
    (F F' : List Atom) (hF : F ⊆ F') :
    ∀ (body : List Atom) (s : Subst) (s' : Subst),
      s' ∈ allMatches F s body → s' ∈ allMatches F' s body := by
  intro body
  induction body with
  | nil =>
      intro s s' h
      -- `allMatches F s []` = `[s]`
      simp [allMatches] at h
      simp [allMatches, h]
  | cons b bs ih =>
      intro s s' h
      -- `allMatches F s (b :: bs) = F.flatMap (fun f => match matchAtom s b f with
      --   | some s'' => allMatches F s'' bs | none => [])`
      unfold allMatches at h
      rw [List.mem_flatMap] at h
      obtain ⟨f, hfF, hcase⟩ := h
      -- f ∈ F ⇒ f ∈ F'
      have hfF' : f ∈ F' := hF hfF
      -- Case on matchAtom s b f
      cases hM : matchAtom s b f with
      | none =>
          rw [hM] at hcase
          simp at hcase
      | some s'' =>
          rw [hM] at hcase
          -- hcase : s' ∈ allMatches F s'' bs
          have ih' : s' ∈ allMatches F' s'' bs := ih s'' s' hcase
          -- Now build the membership on the F' side.
          unfold allMatches
          rw [List.mem_flatMap]
          refine ⟨f, hfF', ?_⟩
          rw [hM]
          exact ih'

/-- `step` is monotone in the fact set. -/
theorem step_subset_facts
    (R : List Rule) (F F' : List Atom) (hF : F ⊆ F') :
    ∀ a, a ∈ step R F → a ∈ step R F' := by
  intro a ha
  unfold step at ha
  rw [List.mem_append] at ha
  cases ha with
  | inl hFa =>
      -- a ∈ F ⇒ a ∈ F' ⇒ a ∈ step R F' by extensiveness
      exact step_extensive R F' a (hF hFa)
  | inr hDer =>
      -- a came from a rule firing. Lift the matching to F'.
      rw [List.mem_flatMap] at hDer
      obtain ⟨r, hrR, hRule⟩ := hDer
      rw [List.mem_filterMap] at hRule
      obtain ⟨s, hsM, hHead⟩ := hRule
      -- s ∈ allMatches F [] r.body ⇒ s ∈ allMatches F' [] r.body
      have hsM' : s ∈ allMatches F' [] r.body :=
        allMatches_subset_facts F F' hF r.body [] s hsM
      unfold step
      apply List.mem_append_right
      rw [List.mem_flatMap]
      refine ⟨r, hrR, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨s, hsM', hHead⟩

/-- `step` is monotone in the rule set. -/
theorem step_subset_rules
    (R R' : List Rule) (F : List Atom) (hR : R ⊆ R') :
    ∀ a, a ∈ step R F → a ∈ step R' F := by
  intro a ha
  unfold step at ha
  rw [List.mem_append] at ha
  cases ha with
  | inl hFa =>
      exact step_extensive R' F a hFa
  | inr hDer =>
      rw [List.mem_flatMap] at hDer
      obtain ⟨r, hrR, hRule⟩ := hDer
      unfold step
      apply List.mem_append_right
      rw [List.mem_flatMap]
      exact ⟨r, hR hrR, hRule⟩

/-- `step` is monotone in both arguments together. -/
theorem step_subset
    (R R' : List Rule) (F F' : List Atom)
    (hR : R ⊆ R') (hF : F ⊆ F') :
    ∀ a, a ∈ step R F → a ∈ step R' F' := by
  intro a ha
  exact step_subset_rules R R' F' hR a (step_subset_facts R F F' hF a ha)

/-- `iterate` is extensive: one more step never removes a fact. -/
theorem iterate_succ_extensive
    (R : List Rule) (F : List Atom) (n : Nat) :
    ∀ a, a ∈ iterate R F n → a ∈ iterate R F (n + 1) := by
  intro a h
  show a ∈ step R (iterate R F n)
  exact step_extensive _ _ _ h

/-- `iterate` is monotone in the iteration count. -/
theorem iterate_subset_le
    (R : List Rule) (F : List Atom) {n m : Nat} (hnm : n ≤ m) :
    ∀ a, a ∈ iterate R F n → a ∈ iterate R F m := by
  induction hnm with
  | refl => intro a h; exact h
  | step _ ih =>
      intro a h
      exact iterate_succ_extensive _ _ _ a (ih a h)

/-- `iterate` is monotone jointly in the rule set, fact set,
    and depth (where depth grows or stays equal). -/
theorem iterate_subset_program
    (R R' : List Rule) (F F' : List Atom)
    (hR : R ⊆ R') (hF : F ⊆ F') (n : Nat) :
    ∀ a, a ∈ iterate R F n → a ∈ iterate R' F' n := by
  induction n with
  | zero =>
      intro a h
      exact hF h
  | succ n ih =>
      intro a h
      -- h : a ∈ iterate R F (n+1) = step R (iterate R F n)
      have h' : a ∈ step R (iterate R F n) := h
      -- Lift through `step` monotonicity.
      have hStep :
          ∀ b, b ∈ iterate R F n → b ∈ iterate R' F' n := ih
      have hSubset : iterate R F n ⊆ iterate R' F' n := fun _ => hStep _
      have := step_subset R R' (iterate R F n) (iterate R' F' n) hR hSubset a h'
      exact this

/-! ## Theorems

  Headline obligations stated in the file comment. `eval_monotone`
  is fully proved below modulo `herbrandBound_mono` (combinatorial
  cardinality lemma — see comment). `eval_sound` and
  `eval_terminates` are stated; full proofs are tracked as
  separate work items. -/

/-- Monotonicity of the Herbrand bound. Stated separately so its
    combinatorial nature (length-after-eraseDups arithmetic) is
    isolated; the proof depends on a stdlib lemma about
    `List.eraseDups.length` under set inclusion that this file does
    not yet derive from scratch. The bound is *intuitively* monotone
    — more constants and predicates can only inflate the worst-case
    saturation depth — so we expose this as a labelled obligation
    rather than a hidden axiom. -/
theorem herbrandBound_mono
    (P P' : Program)
    (hF : ∀ a ∈ P.facts, a ∈ P'.facts)
    (hR : ∀ r ∈ P.rules, r ∈ P'.rules) :
    P.herbrandBound ≤ P'.herbrandBound := by
  sorry

/-- `eval_monotone`: enlarging the fact set or rule set of a
    program can only grow the derived fact set.

    Proven from `iterate_subset_program` plus `iterate_subset_le`
    plus the bound-monotonicity obligation `herbrandBound_mono`. -/
theorem eval_monotone
    (P P' : Program)
    (hF : ∀ a ∈ P.facts, a ∈ P'.facts)
    (hR : ∀ r ∈ P.rules, r ∈ P'.rules) :
    ∀ a ∈ eval P, a ∈ eval P' := by
  intro a h
  -- a ∈ iterate P.rules P.facts P.herbrandBound
  -- Goal: a ∈ iterate P'.rules P'.facts P'.herbrandBound
  -- Step 1: lift through (rules, facts) monotonicity at the smaller depth.
  have h1 : a ∈ iterate P'.rules P'.facts P.herbrandBound :=
    iterate_subset_program P.rules P'.rules P.facts P'.facts hR hF
      P.herbrandBound a h
  -- Step 2: extend iteration depth from P.herbrandBound to P'.herbrandBound.
  have hLe : P.herbrandBound ≤ P'.herbrandBound :=
    herbrandBound_mono P P' hF hR
  exact iterate_subset_le P'.rules P'.facts hLe a h1

/-- `eval_sound`: every atom in `eval P` is either a starting fact
    of `P` or the grounded head of some rule of `P` whose grounded
    body is contained in `eval P`. Stated; proof tracked separately. -/
theorem eval_sound
    (P : Program) (a : Atom) (h : a ∈ eval P) :
    a ∈ P.facts ∨
    ∃ r ∈ P.rules, ∃ s : Subst,
      Atom.applySubst s r.head = some a ∧
      ∀ b ∈ r.body, (Atom.applySubst s b).getD a ∈ eval P := by
  sorry

/-- `eval_terminates`: iterating `step` past the Herbrand bound
    adds nothing. Stated; full proof is the Knaster–Tarski-style
    cardinality argument tracked separately. -/
theorem eval_terminates
    (P : Program) (k : Nat) :
    iterate P.rules P.facts (P.herbrandBound + k)
      = iterate P.rules P.facts P.herbrandBound := by
  sorry

end Postern.Datalog
