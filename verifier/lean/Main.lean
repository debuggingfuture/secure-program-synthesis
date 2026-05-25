/-
  `postern-corpus` — Lean executable that emits the reference
  conformance corpus consumed by the Rust prototype.

  For each named (catalog, policy, principal, plan) input we compute
  the reference rewriter outcome — `some q'` or `none` — together
  with the output schema, predicate-column read-set, and touched
  relation, then serialize the bundle as JSON on stdout. The Rust
  harness pipes this into its rewriter and asserts byte-equivalence
  of the resulting `Option<Plan>` and its schema / filterCols.

  We deliberately label this a *conformance test*, not "differential
  testing" in the QuickCheck / cargo-fuzz sense: the corpus is a
  fixed, hand-curated set of cases plus regressions for known
  attack shapes (`filter_on_forbidden_column`, `unknown_relation`,
  …). Property-based generation is paper §6 / future work. -/

import Postern

open Postern

/-! ## Hand-rolled JSON encoder (RFC 8259 §7-compliant). -/

namespace Json

/-- Escape a single character per RFC 8259 §7. Covers the six
    short forms (`\" \\ \b \f \n \r \t`) and U+0000–U+001F via
    `\u00XX`. Higher Unicode is passed through verbatim. -/
def escapeChar (c : Char) : String :=
  match c with
  | '"'  => "\\\""
  | '\\' => "\\\\"
  | '' => "\\b"
  | '	' => "\\t"
  | '
' => "\\n"
  | '' => "\\f"
  | '' => "\\r"
  | c =>
    let n := c.toNat
    if n < 0x20 then
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

end Json

/-! ## Encoders for Postern types -/

def encAggOp : AggOp → String
  | .sum   => Json.str "sum"
  | .count => Json.str "count"
  | .min   => Json.str "min"
  | .max   => Json.str "max"
  | .avg   => Json.str "avg"

/-- Predicate-term encoder. Mirrors the Rust `Pred` enum's serde
    representation (`{"kind": "ref"|"lit"|"app", ...}`). Uses the
    `args.attach` recursion shape so Lean's termination checker
    accepts the nested call without a wf-recursion clause — the
    JSON encoder isn't in the proof surface, so we keep it
    structurally simple. -/
def encPred : Pred → String
  | .ref c       =>
    Json.obj [("kind", Json.str "ref"), ("col", Json.str c)]
  | .lit v       =>
    Json.obj [("kind", Json.str "lit"), ("val", Json.str v)]
  | .app op args =>
    Json.obj [
      ("kind", Json.str "app"),
      ("op",   Json.str op),
      ("args", Json.arr (args.attach.map (fun ⟨a, _⟩ => encPred a)))
    ]
decreasing_by
  have h := List.sizeOf_lt_of_mem (by assumption)
  simp_wf
  omega

def encPlan : Plan → String
  | .scan r       => Json.obj [("op", Json.str "scan"),    ("rel", Json.str r)]
  | .project p cs => Json.obj [("op", Json.str "project"), ("sub", encPlan p), ("cols", Json.strArr cs)]
  | .filter  p φ  => Json.obj [("op", Json.str "filter"),  ("sub", encPlan p), ("pred", encPred φ)]
  | .join l r on  =>
    Json.obj [
      ("op",    Json.str "join"),
      ("left",  encPlan l),
      ("right", encPlan r),
      ("on",    Json.str on)
    ]
  | .aggregate op col gb p =>
    Json.obj [
      ("op",      Json.str "aggregate"),
      ("agg",     encAggOp op),
      ("col",     Json.str col),
      ("groupBy", Json.strArr gb),
      ("inner",   encPlan p)
    ]

def encGrant (g : Grant) : String :=
  Json.obj [
    ("principal", Json.str g.principal),
    ("relation",  Json.str g.relation),
    ("columns",   Json.strArr g.columns)
  ]

def encAggGrant (g : AggGrant) : String :=
  Json.obj [
    ("principal", Json.str g.principal),
    ("relation",  Json.str g.relation),
    ("op",        encAggOp g.op),
    ("column",    Json.str g.column)
  ]

def encPolicy (P : Policy) : String :=
  Json.obj [
    ("grants",    Json.arr (P.grants.map encGrant)),
    ("aggGrants", Json.arr (P.aggGrants.map encAggGrant))
  ]

/-- Catalog encoded as the slice of relations referenced by the plan
    or the policy. Total functions don't serialise, so we materialise
    only the relevant rows; the Rust side treats unknown relations
    the same (empty column list ⇒ refusal). -/
def encCatalog (cat : Catalog) (rels : List Relation) : String :=
  Json.obj (rels.eraseDups.map (fun r => (r, Json.strArr (cat r))))

def planRels : Plan → List Relation
  | .scan r              => [r]
  | .project p _         => planRels p
  | .filter  p _         => planRels p
  | .join l r _          => planRels l ++ planRels r
  | .aggregate _ _ _ p   => planRels p

/-- Convenience: `Pred.ref c` lifted to the bare-column smart-
    constructor style used by older corpus entries. The bare-column
    pre-C2 form `.filter sub col` is now `.filter sub (refCol col)`. -/
def refCol (c : Column) : Pred := .ref c

def policyRels (P : Policy) : List Relation :=
  P.grants.map Grant.relation ++ P.aggGrants.map AggGrant.relation

/-- Outcome JSON: either `{"kind":"accept", ...}` with the rewritten
    plan + schema + filterCols, or `{"kind":"refuse"}`. -/
def encOutcome (cat : Catalog) (rw : Option Plan) : String :=
  match rw with
  | none =>
    Json.obj [("kind", Json.str "refuse")]
  | some q' =>
    Json.obj [
      ("kind",       Json.str "accept"),
      ("rewrite",    encPlan q'),
      ("schema",     Json.strArr (q'.schema cat)),
      ("filterCols", Json.strArr q'.filterCols),
      ("touched",    Json.str q'.touched)
    ]

/-! ## Test cases

  Hand-curated. Each case names a scenario, names the principal,
  pins the input plan + policy, and labels the *expected outcome
  shape* in the comment. The corpus emitter computes the reference
  outcome from the Lean spec — so any change in spec behaviour
  surfaces as a Rust diff. Adversarial / regression-for-known-
  attack cases are labelled. -/

structure Case where
  name      : String
  catalog   : Catalog
  policy    : Policy
  principal : Principal
  plan      : Plan
  note      : String := ""

/-- A second catalog used by the "unknown relation" / "catalog-
    absent column" cases. -/
def smallCat : Catalog
  | "users_data" => ["id"]
  | _             => []

def cases : List Case := [
  -- §A. Demo / behavioural cases.
  { name := "crm_scans_users", note := "behavioural — CRM full read; ssn/email redacted",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .scan "users_data" },

  { name := "crm_filters_by_region", note := "behavioural — filter on allowed col",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data") (refCol "region") },

  { name := "crm_overprojects_then_filters", note := "behavioural — agent asks for forbidden cols",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .project (.filter (.scan "users_data") (refCol "region"))
                     ["id", "name", "email", "ssn"] },

  { name := "cardops_scans_cards", note := "behavioural — CardOps happy path",
    catalog := Demo.cat, policy := Demo.pol, principal := "CardOps",
    plan := .scan "cards_data" },

  { name := "cardops_attempts_users", note := "behavioural — cross-department; CardOps has no grant on users_data",
    catalog := Demo.cat, policy := Demo.pol, principal := "CardOps",
    plan := .scan "users_data" },

  { name := "fraudrisk_scans_transactions", note := "behavioural — FraudRisk full transactions",
    catalog := Demo.cat, policy := Demo.pol, principal := "FraudRisk",
    plan := .scan "transactions_data" },

  { name := "fraudrisk_scans_users_minimal", note := "behavioural — minimum-necessary join surface",
    catalog := Demo.cat, policy := Demo.pol, principal := "FraudRisk",
    plan := .scan "users_data" },

  -- §B. Regression for refusals (close attacks the previous IR silently admitted).
  { name := "unknown_principal_denied_everywhere",
    note := "regression — unknown principal yields empty allow ⇒ schema = []; ACCEPT (no filterCols)",
    catalog := Demo.cat, policy := Demo.pol, principal := "Marketing",
    plan := .scan "users_data" },

  { name := "scan_of_unknown_relation_refused",
    note := "regression — unknown relation ⇒ rewriter REFUSES (was: silently empty)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .scan "credit_bureau_imports" },

  { name := "filter_on_forbidden_column_refused",
    note := "regression — filter side-channel: CRM cannot filter on ssn even if ssn isn't projected",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data") (refCol "ssn") },

  { name := "nested_filter_one_forbidden_refused",
    note := "regression — deeply-nested filter on forbidden col still refuses",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.filter (.scan "users_data") (refCol "region")) (refCol "email") },

  { name := "project_of_already_redacted_columns",
    note := "behavioural — over-project: ssn/email dropped to empty",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .project (.scan "users_data") ["ssn", "email"] },

  -- §C. Policy-language edge cases.
  { name := "empty_policy_denies_all",
    note := "edge — empty policy ⇒ accept with empty schema (no grants to match)",
    catalog := Demo.cat, policy := { grants := [] }, principal := "CRM",
    plan := .scan "users_data" },

  { name := "duplicate_grants_flat_union",
    note := "edge — two grants for the same (principal, relation) flat-union (no dedup)",
    catalog := Demo.cat,
    policy := { grants := [
      { principal := "CRM", relation := "users_data", columns := ["id", "name"] },
      { principal := "CRM", relation := "users_data", columns := ["name", "region"] }
    ] },
    principal := "CRM",
    plan := .scan "users_data" },

  { name := "policy_grants_columns_not_in_catalog",
    note := "edge — grant lists ssn but catalog doesn't ⇒ intersection drops ssn",
    catalog := smallCat,
    policy := { grants := [
      { principal := "CRM", relation := "users_data", columns := ["id", "ssn"] }
    ] },
    principal := "CRM",
    plan := .scan "users_data" },

  { name := "case_sensitive_principal",
    note := "edge — `\"crm\"` ≠ `\"CRM\"` (no normalisation); expect empty schema",
    catalog := Demo.cat, policy := Demo.pol, principal := "crm",
    plan := .scan "users_data" },

  { name := "principal_with_trailing_space",
    note := "edge — `\"CRM \"` ≠ `\"CRM\"`; pins exact-string equality",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM ",
    plan := .scan "users_data" },

  { name := "project_listing_nonexistent_column",
    note := "edge — Project of `nonexistent` is dropped by schema intersection",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .project (.scan "users_data") ["id", "nonexistent"] },

  -- §D. Cross-relation joins (C1 — paper §6 → §4).
  { name := "join_legal_key_both_sides_allow",
    note :=
      "join — FraudRisk joins transactions⋈users on `card_id`/`id`; the join key " ++
      "needs to be policy-allowed on BOTH legs. For this case we degenerate to a " ++
      "self-join of users_data on `id` (FraudRisk holds `id` on users_data).",
    catalog := Demo.cat, policy := Demo.pol, principal := "FraudRisk",
    plan := .join (.scan "users_data") (.scan "users_data") "id" },

  { name := "join_key_forbidden_on_one_leg_refused",
    note :=
      "join — refusal: CRM tries users⋈users on `ssn`. CRM has no grant for `ssn` " ++
      "on users_data; the join-key leak rule refuses regardless of the legs' own " ++
      "rewrite outcome.",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .join (.scan "users_data") (.scan "users_data") "ssn" },

  { name := "join_with_refusing_leg_refused",
    note :=
      "join — refusal: CRM joins users_data ⋈ credit_bureau_imports on `id`; the " ++
      "right leg refuses (unknown relation), so the join refuses.",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .join (.scan "users_data") (.scan "credit_bureau_imports") "id" },

  -- §E. Aggregation with the abstract DP boundary (paper §6, C3).
  --
  -- The boundary is parameterised in the Lean spec as
  -- `Policy.aggAllowed`; the corpus exercises five shapes:
  --   E1 ACCEPT — analytics-only role, AggGrant covers Sum(amount)
  --   E2 REFUSE — analytics-only role, no AggGrant for Avg(amount)
  --             and `amount` not in `allowed` ⇒ DP boundary refuses
  --   E3 ACCEPT — column-grant already covers `amount` for
  --             FraudRisk; aggregate admissible *trivially*
  --             (no DP boundary needed, the existing grant
  --             dominates).
  --   E4 ACCEPT — Count(txn_id) AggGrant with no groupBy
  --   E5 REFUSE — groupBy on a column with no column-grant
  { name := "agg_sum_amount_analytics_via_agggrant",
    note := "C3 ACCEPT — DP boundary lets Analytics compute Sum(amount) on transactions_data via AggGrant",
    catalog := Demo.cat, policy := Demo.pol, principal := "Analytics",
    plan := .aggregate .sum "amount" [] (.scan "transactions_data") },

  { name := "agg_avg_amount_analytics_refused",
    note := "C3 REFUSE — no AggGrant for Avg(amount) and amount ∉ allowed(Analytics, ...)",
    catalog := Demo.cat, policy := Demo.pol, principal := "Analytics",
    plan := .aggregate .avg "amount" [] (.scan "transactions_data") },

  { name := "agg_sum_amount_fraudrisk_trivial",
    note := "C3 ACCEPT (trivial) — FraudRisk already has column-grant on amount; aggregate dominates",
    catalog := Demo.cat, policy := Demo.pol, principal := "FraudRisk",
    plan := .aggregate .sum "amount" [] (.scan "transactions_data") },

  { name := "agg_count_with_group_by_analytics",
    note := "C3 ACCEPT — Count(txn_id) AggGrant + groupBy on no columns (whole-table)",
    catalog := Demo.cat, policy := Demo.pol, principal := "Analytics",
    plan := .aggregate .count "txn_id" [] (.scan "transactions_data") },

  { name := "agg_groupBy_forbidden_column_refused",
    note := "C3 REFUSE — groupBy on a column not in allowed (`merchant` for Analytics, no column-grant)",
    catalog := Demo.cat, policy := Demo.pol, principal := "Analytics",
    plan := .aggregate .sum "amount" ["merchant"] (.scan "transactions_data") },

  -- §F. Predicate-IR cases (C2 — paper §4 Theorem 13).
  --
  -- These exercise the coverage condition at the φ level: every
  -- free column of every Filter predicate must be policy-allowed.
  --   F1 ACCEPT — compound predicate `region = "EU"` (only refs allowed).
  --   F2 REFUSE — direct forbidden ref under an operator wrapper.
  --   F3 REFUSE — conjunction with one forbidden ref taints the whole.
  --   F4 REFUSE — disjunction with one forbidden ref same shape.
  --   F5 ACCEPT — negation over an allowed ref.
  { name := "pred_compound_allowed_only_accepts",
    note := "C2 ACCEPT — `region = \"EU\"` (compound predicate, only refs allowed columns)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data")
              (.app "=" [.ref "region", .lit "EU"]) },

  { name := "pred_direct_forbidden_ref_refused",
    note := "C2 REFUSE — `ssn = \"X\"` (forbidden ref wrapped in operator)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data")
              (.app "=" [.ref "ssn", .lit "X"]) },

  { name := "pred_and_one_forbidden_refused",
    note := "C2 REFUSE — `region = \"EU\" AND ssn = \"X\"` (conjunction; one forbidden ref taints the whole)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data")
              (.app "and" [
                .app "=" [.ref "region", .lit "EU"],
                .app "=" [.ref "ssn", .lit "X"]
              ]) },

  { name := "pred_or_one_forbidden_refused",
    note := "C2 REFUSE — `region = \"EU\" OR email = \"x@y\"` (disjunction; one forbidden ref taints the whole)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data")
              (.app "or" [
                .app "=" [.ref "region", .lit "EU"],
                .app "=" [.ref "email", .lit "x@y"]
              ]) },

  { name := "pred_not_allowed_accepts",
    note := "C2 ACCEPT — `NOT (age = 18)` (negation over allowed ref)",
    catalog := Demo.cat, policy := Demo.pol, principal := "CRM",
    plan := .filter (.scan "users_data")
              (.app "not" [.app "=" [.ref "age", .lit "18"]]) }
]

def encCase (c : Case) : String :=
  let rw := rewrite c.catalog c.policy c.principal c.plan
  let rels := (planRels c.plan ++ policyRels c.policy).eraseDups
  Json.obj [
    ("name",      Json.str c.name),
    ("note",      Json.str c.note),
    ("principal", Json.str c.principal),
    ("catalog",   encCatalog c.catalog rels),
    ("policy",    encPolicy c.policy),
    ("plan",      encPlan c.plan),
    ("expected_filter_cols", Json.strArr c.plan.filterCols),
    ("expected_outcome",     encOutcome c.catalog rw)
  ]

def main : IO Unit := do
  IO.println (Json.arr (cases.map encCase))
