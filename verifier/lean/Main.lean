/-
  `postern-corpus` — Lean executable that emits the differential-test
  corpus consumed by the Rust prototype.

  For each named (catalog, policy, principal, plan) input, we compute
  the reference rewrite output, output schema, and touched relation
  according to `Postern.lean`, then serialize the bundle to JSON on
  stdout. The Rust harness pipes this into its rewriter and asserts
  byte-equality of plans plus equality of schemas.

  The JSON encoder is hand-rolled (no `import Lean`) to keep build
  time short — corpus shape is small and stable. -/

import Postern

open Postern

/-! ## Hand-rolled JSON encoder -/

namespace Json

def escape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | _    => acc.push c) ""

def str (s : String) : String := "\"" ++ escape s ++ "\""

def arr (items : List String) : String :=
  "[" ++ ",".intercalate items ++ "]"

def obj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map (fun (k, v) => str k ++ ":" ++ v)) ++ "}"

def strArr (items : List String) : String := arr (items.map str)

end Json

/-! ## Encoders for Postern types -/

def encPlan : Plan → String
  | .scan r       => Json.obj [("op", Json.str "scan"),    ("rel", Json.str r)]
  | .project p cs => Json.obj [("op", Json.str "project"), ("sub", encPlan p), ("cols", Json.strArr cs)]
  | .filter  p c  => Json.obj [("op", Json.str "filter"),  ("sub", encPlan p), ("col", Json.str c)]

def encGrant (g : Grant) : String :=
  Json.obj [
    ("principal", Json.str g.principal),
    ("relation",  Json.str g.relation),
    ("columns",   Json.strArr g.columns)
  ]

def encPolicy (P : Policy) : String := Json.arr (P.map encGrant)

/-- A catalog is encoded as the subset of relations referenced by the
    plan (plus any relation grants apply to). Total functions don't
    serialize, so we materialize the relevant slice. -/
def encCatalog (cat : Catalog) (rels : List Relation) : String :=
  Json.obj (rels.eraseDups.map (fun r => (r, Json.strArr (cat r))))

/-- Collect every relation a plan touches and every relation a policy
    references — the union is the catalog slice the Rust side needs. -/
def planRels : Plan → List Relation
  | .scan r       => [r]
  | .project p _  => planRels p
  | .filter  p _  => planRels p

def policyRels (P : Policy) : List Relation := P.map Grant.relation

/-! ## Test cases

  Each case names the scenario, the principal, the input plan, and the
  policy. The corpus emitter computes the expected rewrite/schema and
  hands them to the Rust harness — so a Lean change that alters
  behaviour will surface as a Rust test failure. -/

structure Case where
  name      : String
  catalog   : Catalog
  policy    : Policy
  principal : Principal
  plan      : Plan

def cases : List Case := [
  { name := "crm_scans_users",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CRM",
    plan := .scan "users_data" },

  { name := "crm_filters_by_region",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CRM",
    plan := .filter (.scan "users_data") "region" },

  { name := "crm_overprojects_then_filters",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CRM",
    plan := .project (.filter (.scan "users_data") "region")
                     ["id", "name", "email", "ssn"] },

  { name := "cardops_scans_cards",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CardOps",
    plan := .scan "cards_data" },

  { name := "cardops_attempts_users",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CardOps",
    plan := .scan "users_data" },

  { name := "fraudrisk_scans_transactions",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "FraudRisk",
    plan := .scan "transactions_data" },

  { name := "fraudrisk_scans_users_minimal",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "FraudRisk",
    plan := .scan "users_data" },

  { name := "unknown_principal_denied_everywhere",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "Marketing",
    plan := .scan "users_data" },

  { name := "scan_of_unknown_relation_yields_empty",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CRM",
    plan := .scan "credit_bureau_imports" },

  { name := "project_of_already_redacted_columns",
    catalog := Demo.cat, policy := Demo.pol,
    principal := "CRM",
    plan := .project (.scan "users_data") ["ssn", "email"] }
]

def encCase (c : Case) : String :=
  let rewritten := rewrite c.catalog c.policy c.principal c.plan
  let rels := (planRels c.plan ++ policyRels c.policy).eraseDups
  Json.obj [
    ("name",      Json.str c.name),
    ("principal", Json.str c.principal),
    ("catalog",   encCatalog c.catalog rels),
    ("policy",    encPolicy c.policy),
    ("plan",      encPlan c.plan),
    ("expected_rewrite", encPlan rewritten),
    ("expected_schema",  Json.strArr (rewritten.schema c.catalog)),
    ("expected_touched", Json.str rewritten.touched)
  ]

def main : IO Unit := do
  IO.println (Json.arr (cases.map encCase))
