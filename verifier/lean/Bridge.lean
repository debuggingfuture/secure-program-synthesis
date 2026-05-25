/-
  Postern.Bridge — connects the column-grant surface syntax
  (`Postern.Policy`) to the Datalog evaluator (`Postern.Datalog.Program`).

  The rewriter consults `Policy.allowed prin rel : List Column`.
  The Datalog evaluator computes `Program.allowed prin rel : List Symbol`
  by querying ground `right(prin, rel, c)` atoms in `eval P`.

  This file defines `Policy.toProgram : Policy → Program` and proves

    `bridge_allowed :
        ∀ (P : Policy) (p : Principal) (r : Relation),
          P.allowed p r = (P.toProgram).allowed p r`

  closing the gap flagged in paper §6. The translation produces a
  rule-free `Program` whose facts are one ground
  `right(principal, relation, c)` per `(grant, column)` pair, in
  insertion order — matching the byte-for-byte semantics of the
  Rust mirror.

  `Column` and `Symbol` are both `abbrev String`, so the equality
  is between identical underlying types; no decode/encode layer.
-/

import Postern
import Datalog

namespace Postern

open Postern.Datalog

/-! ## Translation -/

/-- Translate a single grant to the ground `right(principal,
    relation, column)` facts it licenses. One fact per column,
    in the order columns appear in the grant. -/
def Grant.toFacts (g : Grant) : List Atom :=
  g.columns.map (fun c => Atom.ground RIGHT [g.principal, g.relation, c])

/-- Translate a column-grant policy to a rule-free Datalog program.
    The resulting program has the union of all per-grant facts and
    no rules — exactly the Biscuit-style "right(_, _, _) ground
    facts only" regime the financial-institution scenario uses.
    `AggGrant`s do not participate in the standard column-grant
    bridge — they encode the abstract DP boundary which lives
    outside the Datalog evaluator's `right(_, _, _)` namespace. -/
def Policy.toProgram (P : Policy) : Program :=
  { facts := P.grants.flatMap Grant.toFacts, rules := [] }

/-! ## Bridge theorem

  The proof reduces in three layers:

    1. `eval (P.toProgram) = P.facts` mem-equivalent, because
       the program has no rules (`eval_no_rules`). For list
       equality we need a stronger result: `iterate [] F n = F`
       *as a list*, not just mem-equivalent. We prove that in
       `iterate_no_rules_eq`.

    2. `filterMap` of the `right(p, r, c)`-projection over
       `P.flatMap Grant.toFacts` distributes over `flatMap`
       (a stdlib equation).

    3. Per-grant, the projection equals the grant's `columns`
       when the grant matches, and `[]` otherwise. Combined with
       the standard `filter ... flatMap = flatMap (if-then-else)`
       equation, both sides reduce to the same `P.flatMap (...)`
       form.

  We deliberately keep every step as a function-projection or
  direct list equation so the axiom audit stays bounded by
  `propext` and `Quot.sound` — same discipline as `Postern.lean`. -/

/-- Pointwise: with no rules, `iterate` is the identity *as a
    list*, not just mem-equivalent. Companion to
    `Datalog.iterate_no_rules`. -/
private theorem iterate_no_rules_eq (F : List Atom) :
    ∀ n, iterate [] F n = F := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      -- iterate [] F (k+1) = step [] (iterate [] F k) = step [] F (by ih)
      show step [] (iterate [] F k) = F
      rw [ih]
      -- step [] F = F ++ [] = F
      unfold step
      simp

/-- Specialisation of the above to `eval`. -/
private theorem eval_no_rules_eq (P : Program) (h : P.rules = []) :
    eval P = P.facts := by
  show iterate P.rules P.facts P.herbrandBound = P.facts
  rw [h]
  exact iterate_no_rules_eq P.facts P.herbrandBound

/-- The "right-projection" used by `Program.allowed`. Pulled out
    as a named function so we can reason about it equationally. -/
private def rightProj (prin rel : Symbol) (a : Atom) : Option Symbol :=
  if a.pred = RIGHT then
    match a.args with
    | [.const p, .const r, .const c] =>
        if p = prin ∧ r = rel then some c else none
    | _ => none
  else none

/-- `Program.allowed` unfolded into the named projection. -/
private theorem allowed_as_filterMap (P : Program) (prin rel : Symbol) :
    P.allowed prin rel = (eval P).filterMap (rightProj prin rel) := by
  rfl

/-- The projection of a single grant's facts: it returns the
    grant's columns when `(g.principal, g.relation) = (prin, rel)`,
    `[]` otherwise. Proven by induction on the columns list,
    case-splitting on the principal/relation match. -/
private theorem grant_toFacts_filterMap (g : Grant) (prin rel : Symbol) :
    (g.toFacts).filterMap (rightProj prin rel) =
      (if g.principal = prin ∧ g.relation = rel then g.columns else []) := by
  unfold Grant.toFacts
  by_cases hMatch : g.principal = prin ∧ g.relation = rel
  · rw [if_pos hMatch]
    -- Push the filterMap through the map for a unified form.
    rw [List.filterMap_map]
    induction g.columns with
    | nil => rfl
    | cons c cs ih =>
        -- The head element reduces to `some c`.
        have hC :
            (rightProj prin rel ∘ fun c' =>
              Atom.ground RIGHT [g.principal, g.relation, c']) c = some c := by
          show rightProj prin rel
                  (Atom.ground RIGHT [g.principal, g.relation, c]) = some c
          unfold rightProj Atom.ground
          simp [hMatch.1, hMatch.2]
        -- filterMap reduces by the cons-equation; `simp` beta-reduces the match.
        simp only [List.filterMap_cons, hC]
        rw [ih]
  · rw [if_neg hMatch]
    rw [List.filterMap_map]
    induction g.columns with
    | nil => rfl
    | cons c cs ih =>
        have hC :
            (rightProj prin rel ∘ fun c' =>
              Atom.ground RIGHT [g.principal, g.relation, c']) c = none := by
          show rightProj prin rel
                  (Atom.ground RIGHT [g.principal, g.relation, c]) = none
          unfold rightProj Atom.ground
          simp
          intro hP hR
          exact hMatch ⟨hP, hR⟩
        simp only [List.filterMap_cons, hC]
        exact ih

/-- `filter ... flatMap` collapses to a single `flatMap` with an
    inline conditional. Standard list lemma we prove from scratch
    so the axiom audit stays bounded. The Bool form on both sides
    matches the shape Lean elaborates from `decide`-driven Prop
    filters / Prop-`if`s in `Policy.allowed`. -/
private theorem filter_flatMap_collapse
    {α β : Type _} (p : α → Bool) (f : α → List β) (xs : List α) :
    (xs.filter p).flatMap f =
      xs.flatMap (fun x => if p x = true then f x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : p x = true
      · simp [h, List.flatMap_cons, ih]
      · simp [h, List.flatMap_cons, ih]

/-- The flatMap-of-flatMap fusion used to commute `filterMap` and
    `flatMap`. Re-stated from stdlib for clarity at the call-site. -/
private theorem filterMap_flatMap
    {α β γ : Type _} (xs : List α) (f : α → List β) (g : β → Option γ) :
    (xs.flatMap f).filterMap g = xs.flatMap (fun x => (f x).filterMap g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.flatMap_cons, List.filterMap_append, ih]

/-- **Bridge theorem.** The column-grant surface form
    `Policy.allowed` agrees, as a list, with the Datalog
    evaluator's `Program.allowed` on `Policy.toProgram`. -/
theorem bridge_allowed (P : Policy) (prin : Principal) (rel : Relation) :
    P.allowed prin rel = (P.toProgram).allowed prin rel := by
  -- LHS: (P.filter matching).flatMap Grant.columns
  -- RHS: (eval P.toProgram).filterMap (rightProj prin rel)
  --    = P.facts.filterMap (rightProj prin rel)        [rule-free]
  --    = (P.flatMap Grant.toFacts).filterMap (rightProj prin rel)
  --    = P.flatMap (g => (g.toFacts).filterMap (rightProj prin rel))
  --    = P.flatMap (g => if matching g then g.columns else [])
  --    = (P.filter matching).flatMap Grant.columns   [filter_flatMap_collapse]
  -- Equal to LHS.
  -- Step 1: unfold RHS using rule-free evaluation.
  rw [allowed_as_filterMap]
  rw [eval_no_rules_eq P.toProgram rfl]
  -- Step 2: unfold toProgram.facts.
  show P.allowed prin rel
        = (P.grants.flatMap Grant.toFacts).filterMap (rightProj prin rel)
  -- Step 3: commute filterMap with flatMap.
  rw [filterMap_flatMap]
  -- Step 4: rewrite each per-grant filterMap via grant_toFacts_filterMap.
  have hPointwise :
      (fun g : Grant => (g.toFacts).filterMap (rightProj prin rel))
        = (fun g : Grant =>
            if g.principal = prin ∧ g.relation = rel then g.columns else []) := by
    funext g
    exact grant_toFacts_filterMap g prin rel
  rw [hPointwise]
  -- Step 5: LHS is (filter ... ).flatMap columns. Collapse it.
  show P.allowed prin rel
        = P.grants.flatMap (fun g =>
            if g.principal = prin ∧ g.relation = rel then g.columns else [])
  unfold Policy.allowed
  -- Both sides reduce to the Bool-`if` form, since Prop-`if`s in `Policy.allowed`
  -- and the rewritten RHS both go through `decide`. They are defeq, so the
  -- Bool-form lemma applies modulo a `simp` to fuse `decide (...) = true` with
  -- the corresponding Prop on each branch.
  have h := filter_flatMap_collapse
              (fun g : Grant => decide (g.principal = prin ∧ g.relation = rel))
              Grant.columns P.grants
  -- Both `if`s are over a Decidable proposition; one writes it as `decide ... = true`,
  -- the other as the Prop itself. Reconcile with funext and case split.
  have heq :
      (fun g : Grant =>
          if decide (g.principal = prin ∧ g.relation = rel) = true
            then g.columns else ([] : List Column))
        = (fun g : Grant =>
            if g.principal = prin ∧ g.relation = rel
              then g.columns else ([] : List Column)) := by
    funext g
    by_cases hM : g.principal = prin ∧ g.relation = rel
    · simp [hM]
    · simp [hM]
  rw [heq] at h
  exact h

/-! ## Demonstration

    Three unit cases that exercise the bridge at build time.
    Verified by `decide`; if `bridge_allowed` or the underlying
    definitions drift, these break the build immediately.

    The choice of cases mirrors the structural variability of
    `Policy.allowed`:

      1. A matching grant ⇒ the columns are visible on both sides.
      2. A non-matching principal ⇒ both sides yield `[]`.
      3. Multiple grants for the same `(principal, relation)`
         flat-union in the same order on both sides — pins the
         insertion-order semantics. -/

namespace BridgeDemo

/-- Case 1: a single matching grant. -/
def pol1 : Policy :=
  { grants := [{ principal := "CRM", relation := "users_data",
                 columns := ["id", "name"] }] }

example :
    pol1.allowed "CRM" "users_data"
    = pol1.toProgram.allowed "CRM" "users_data" :=
  bridge_allowed _ _ _

/-- Case 2: a principal with no grants — both sides `[]`. -/
example :
    pol1.allowed "Marketing" "users_data"
    = pol1.toProgram.allowed "Marketing" "users_data" :=
  bridge_allowed _ _ _

/-- Case 3: two grants for the same `(principal, relation)` flat-
    union with preserved insertion order. Also pins the case where
    other principals' grants are present (and correctly skipped on
    the RHS by the `right(prin, rel, _)` filter). -/
def pol2 : Policy := {
  grants := [
    { principal := "CRM",     relation := "users_data", columns := ["id", "name"] },
    { principal := "CardOps", relation := "cards_data", columns := ["card_id"] },
    { principal := "CRM",     relation := "users_data", columns := ["region", "age"] }
  ]
}

example :
    pol2.allowed "CRM" "users_data"
    = pol2.toProgram.allowed "CRM" "users_data" :=
  bridge_allowed _ _ _

/-- Case 4: empty policy — both sides `[]`. Pins the base case. -/
def polEmpty : Policy := { grants := [] }

example :
    polEmpty.allowed "CRM" "users_data"
    = polEmpty.toProgram.allowed "CRM" "users_data" :=
  bridge_allowed _ _ _

/-- The Demo policy from `Postern.lean` § Demo, exercised through
    the bridge. This ties the financial-institution scenario into
    the Datalog interface. -/
example : Demo.pol.allowed "CRM" "users_data"
        = Demo.pol.toProgram.allowed "CRM" "users_data" :=
  bridge_allowed _ _ _

/-! ### Concrete-value checks via the surface form

    The five `example`s above use `bridge_allowed` to pin the
    *equality* of the two evaluator paths. The checks below pin
    the concrete *value* on the surface side — cheap because
    `Policy.allowed` is a direct list filter+flatMap, no Datalog
    iteration. The bridge then transports each result to the
    Datalog side: any drift in `Policy.allowed` surfaces here,
    any drift in `Program.allowed`'s rule-free behaviour surfaces
    in the Rust diff corpus. -/

/-- pol1 admits exactly `["id", "name"]` on the matching principal. -/
example : pol1.allowed "CRM" "users_data" = ["id", "name"] := by decide

/-- pol1 yields `[]` on a non-matching principal. -/
example : pol1.allowed "Marketing" "users_data" = ([] : List Column) := by decide

/-- pol2 flat-unions two grants in insertion order on the
    matching `(principal, relation)`, and skips the unrelated
    `CardOps` grant. Pins the byte-for-byte semantics. -/
example :
    pol2.allowed "CRM" "users_data"
      = ["id", "name", "region", "age"] := by decide

/-- Empty policy yields `[]` on every query — base case. -/
example : polEmpty.allowed "CRM" "users_data" = ([] : List Column) := by decide

end BridgeDemo

end Postern
