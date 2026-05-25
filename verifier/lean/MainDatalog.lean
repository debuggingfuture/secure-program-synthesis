/-
  `postern-datalog-corpus` — Lean executable emitting the
  reference conformance corpus for the Horn-fragment Datalog
  evaluator.

  For each named (program, principal, relation) case we compute
  `Postern.Datalog.Program.allowed` against the Lean reference
  and serialise the bundle as JSON on stdout. The Rust harness
  (`postern-datalog-diff`) consumes the same JSON, drives
  `biscuit_auth::datalog::World` via `postern_core::datalog`,
  and asserts mem-set equality of the resulting column list.

  Like its rewriter sibling, this is a *reference conformance*
  corpus, not QuickCheck-style differential testing: a
  hand-curated set of cases drawn from the motivating
  financial-institution scenario plus rule-driven LFP stress
  cases. Property-based generation remains §6 future work.
-/

import Datalog

open Postern.Datalog

/-! ## Hand-rolled JSON encoder.

  Re-used shape from `Main.lean` — kept inlined here so the two
  corpus exes don't develop a hard build dependency on each
  other beyond what `Postern.lean` itself defines. -/

namespace JsonDL

/-- RFC 8259 §7-compliant character escape. The control-char
    branches use `Char.ofNat` rather than literal char-literals
    so this source file is pure ASCII and survives round-trips
    through tools that strip non-printable bytes. -/
def escapeChar (c : Char) : String :=
  let n := c.toNat
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if n = 0x08 then "\\b"
  else if n = 0x09 then "\\t"
  else if n = 0x0A then "\\n"
  else if n = 0x0C then "\\f"
  else if n = 0x0D then "\\r"
  else if n < 0x20 then
    let hi := Nat.toDigits 16 (n / 16) |>.head?.map (·.toString) |>.getD "0"
    let lo := Nat.toDigits 16 (n % 16) |>.head?.map (·.toString) |>.getD "0"
    "\\u00" ++ hi ++ lo
  else
    String.singleton c

def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

def str (s : String) : String := "\"" ++ escape s ++ "\""

def arr (items : List String) : String :=
  "[" ++ ",".intercalate items ++ "]"

def obj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map (fun (k, v) => str k ++ ":" ++ v)) ++ "}"

def strArr (items : List String) : String := arr (items.map str)

end JsonDL

/-! ## Encoders for Datalog types -/

def encTerm : Term → String
  | .var n   => JsonDL.obj [("kind", JsonDL.str "var"),   ("name",  JsonDL.str n)]
  | .const v => JsonDL.obj [("kind", JsonDL.str "const"), ("value", JsonDL.str v)]

def encAtom (a : Atom) : String :=
  JsonDL.obj [
    ("pred", JsonDL.str a.pred),
    ("args", JsonDL.arr (a.args.map encTerm))
  ]

def encRule (r : Rule) : String :=
  JsonDL.obj [
    ("head", encAtom r.head),
    ("body", JsonDL.arr (r.body.map encAtom))
  ]

def encProgram (P : Program) : String :=
  JsonDL.obj [
    ("facts", JsonDL.arr (P.facts.map encAtom)),
    ("rules", JsonDL.arr (P.rules.map encRule))
  ]

/-! ## Test cases

  Hand-curated, mixing the motivating ground-fact scenario, a
  rule-driven transitive `right`, refusal cases, and one
  larger program. -/

structure DLCase where
  name      : String
  note      : String := ""
  program   : Program
  principal : Symbol
  relation  : Symbol

/-- Convenience: build a ground `right(p, r, c)` fact. -/
def rg (p r c : Symbol) : Atom :=
  Atom.ground "right" [p, r, c]

/-- Financial-institution ground-fact-only program (matches
    `Postern.Demo.pol` compiled to Datalog facts). -/
def finFacts : Program :=
  { facts := [
      rg "CRM"       "users_data"        "id",
      rg "CRM"       "users_data"        "name",
      rg "CRM"       "users_data"        "region",
      rg "CRM"       "users_data"        "age",
      rg "CardOps"   "cards_data"        "card_id",
      rg "CardOps"   "cards_data"        "card_type",
      rg "CardOps"   "cards_data"        "limit",
      rg "CardOps"   "cards_data"        "activated",
      rg "FraudRisk" "transactions_data" "txn_id",
      rg "FraudRisk" "transactions_data" "card_id",
      rg "FraudRisk" "transactions_data" "amount",
      rg "FraudRisk" "transactions_data" "merchant",
      rg "FraudRisk" "transactions_data" "timestamp",
      rg "FraudRisk" "users_data"        "id",
      rg "FraudRisk" "users_data"        "region"
    ],
    rules := [] }

/-- One-rule program: roles derive rights via group membership.
      member(P, G) ∧ grant(G, R, C) → right(P, R, C). -/
def rolesProgram : Program :=
  { facts := [
      Atom.ground "member" ["Alice", "CRM"],
      Atom.ground "member" ["Bob",   "FraudRisk"],
      Atom.ground "grant"  ["CRM",       "users_data",        "id"],
      Atom.ground "grant"  ["CRM",       "users_data",        "name"],
      Atom.ground "grant"  ["FraudRisk", "transactions_data", "txn_id"],
      Atom.ground "grant"  ["FraudRisk", "transactions_data", "amount"]
    ],
    rules := [
      { head := { pred := "right",
                  args := [.var "p", .var "r", .var "c"] },
        body := [
          { pred := "member", args := [.var "p", .var "g"] },
          { pred := "grant",  args := [.var "g", .var "r", .var "c"] }
        ] }
    ] }

/-- Larger ground-fact program: 3 principals × 3 relations ×
    4 columns each — 36 facts. Sized to exercise the LFP
    saturation loop more than the toy cases. -/
def largeProgram : Program :=
  let principals := ["P1", "P2", "P3"]
  let relations  := ["R1", "R2", "R3"]
  let columns    := ["c0", "c1", "c2", "c3"]
  let facts := principals.flatMap (fun p =>
    relations.flatMap (fun r =>
      columns.map (fun c => rg p r c)))
  { facts := facts, rules := [] }

def cases : List DLCase := [
  -- §A. Ground-fact baseline (financial-institution scenario).
  { name := "fin_crm_users_data",
    note := "behavioural — ground facts only, CRM allowed columns on users_data",
    program := finFacts, principal := "CRM",       relation := "users_data" },

  { name := "fin_fraudrisk_users_data",
    note := "behavioural — minimum-necessary join surface (FraudRisk only id, region)",
    program := finFacts, principal := "FraudRisk", relation := "users_data" },

  { name := "fin_fraudrisk_transactions",
    note := "behavioural — full FraudRisk grant on transactions",
    program := finFacts, principal := "FraudRisk", relation := "transactions_data" },

  -- §B. Refusal cases.
  { name := "fin_cardops_users_data_refusal",
    note := "refusal — CardOps has no grant on users_data; expect empty derivation",
    program := finFacts, principal := "CardOps",   relation := "users_data" },

  { name := "fin_unknown_principal_refusal",
    note := "refusal — unknown principal yields no `right(...)` facts",
    program := finFacts, principal := "Marketing", relation := "users_data" },

  -- §C. Rule-driven LFP — single transitive rule.
  { name := "roles_transitive_right_alice",
    note := "rule-LFP — Alice inherits CRM grants through `member`",
    program := rolesProgram, principal := "Alice", relation := "users_data" },

  { name := "roles_transitive_right_bob",
    note := "rule-LFP — Bob inherits FraudRisk grants through `member`",
    program := rolesProgram, principal := "Bob",   relation := "transactions_data" },

  { name := "roles_transitive_right_no_membership",
    note := "rule-LFP refusal — Eve is in no group; no derivations",
    program := rolesProgram, principal := "Eve",   relation := "users_data" },

  -- §D. Larger program — exercises the saturation loop.
  { name := "large_p2_r2_full",
    note := "stress — 36-fact ground program, query one (principal, relation) cell",
    program := largeProgram, principal := "P2",    relation := "R2" }
]

/-- Serialise one case, including the Lean-computed expected
    `allowed` set as a JSON string array. The order of
    `Program.allowed` is deterministic in Lean (it's a
    `List.filterMap` over `eval P`) but downstream callers
    should treat the array as a mem-set — biscuit's `FactSet`
    iteration order isn't guaranteed. -/
def encCase (c : DLCase) : String :=
  let expected := c.program.allowed c.principal c.relation
  JsonDL.obj [
    ("name",      JsonDL.str c.name),
    ("note",      JsonDL.str c.note),
    ("principal", JsonDL.str c.principal),
    ("relation",  JsonDL.str c.relation),
    ("program",   encProgram c.program),
    ("expected_allowed", JsonDL.strArr expected)
  ]

def main : IO Unit := do
  IO.println (JsonDL.arr (cases.map encCase))
