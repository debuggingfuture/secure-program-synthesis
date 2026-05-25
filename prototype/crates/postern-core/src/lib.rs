//! Postern core — Rust mirror of `verifier/lean/Postern.lean`.
//!
//! Types and the `rewrite` function deliberately match the Lean
//! reference one-for-one so the conformance harness can compare
//! outputs structurally. Any divergence here that changes
//! behaviour will surface as a `postern-diff` test failure.
//!
//! The Lean theorem set carries the correctness claim:
//!
//!   `rewrite_sound`         — output columns ⊆ policy-allowed
//!   `rewrite_filter_sound`  — predicate columns ⊆ policy-allowed
//!   `rewrite_refuses_unknown` — unknown relation ⇒ `None`
//!   `rewrite_refuses_forbidden_filter` — forbidden filter ⇒ `None`
//!
//! This crate must preserve those properties; conformance is checked
//! at test time against the JSON corpus emitted by
//! `lake exe postern-corpus`.

#![warn(missing_docs)]

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[cfg(feature = "datalog-biscuit")]
pub mod datalog_biscuit;

/// Horn-fragment Datalog programs — Rust mirror of
/// `verifier/lean/Datalog.lean` plus the `biscuit_auth::datalog::World`
/// evaluation backend. Public regardless of the `datalog-biscuit`
/// feature so corpus emitters can serialise `Program` JSON; the
/// `allowed` function returns a clear error if the feature is off.
pub mod datalog;

/// Identifier for a principal (e.g. a department or service-account).
pub type Principal = String;
/// Relation (table) name.
pub type Relation = String;
/// Column name.
pub type Column = String;

/// Catalog slice — relation → ordered column list.
///
/// The Lean spec treats this as a total function (`Relation → List
/// Column`); we model it as a partial map and return an empty
/// column list for unknown relations — which the rewriter interprets
/// as the *refusal* signal `rewrite_refuses_unknown`. Do **not**
/// rely on iteration order of the underlying map: the Lean spec is
/// order-agnostic, the Rust impl uses `BTreeMap` for determinism
/// only.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Catalog(BTreeMap<Relation, Vec<Column>>);

impl Catalog {
    /// Construct an empty catalog.
    #[must_use]
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    /// Construct a catalog from an iterator of `(relation, columns)`.
    pub fn from_entries<I, R, C>(entries: I) -> Self
    where
        I: IntoIterator<Item = (R, Vec<C>)>,
        R: Into<Relation>,
        C: Into<Column>,
    {
        Self(
            entries
                .into_iter()
                .map(|(r, cs)| (r.into(), cs.into_iter().map(Into::into).collect()))
                .collect(),
        )
    }

    /// Lookup columns for a relation. Unknown relations get the
    /// empty list (signals refusal to the rewriter).
    #[must_use]
    pub fn columns(&self, rel: &str) -> Vec<Column> {
        self.0.get(rel).cloned().unwrap_or_default()
    }
}

/// Plan IR — mirrors the Lean `inductive Plan`. Tag layout matches
/// the JSON shape emitted by `Main.lean`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Plan {
    /// Read all columns from `rel`.
    Scan {
        /// Relation to scan.
        rel: Relation,
    },
    /// Keep only the listed columns from the sub-plan.
    Project {
        /// Sub-plan.
        sub: Box<Plan>,
        /// Columns to keep (intersected with sub-plan's schema).
        cols: Vec<Column>,
    },
    /// Row-only predicate; schema unchanged. `col` is the read
    /// dependency that the rewriter checks for policy-coverage.
    Filter {
        /// Sub-plan.
        sub: Box<Plan>,
        /// Column the predicate reads.
        col: Column,
    },
    /// Equi-join of `left` and `right` on a shared column `on`.
    /// Output schema is `left.schema ++ right.schema`; the rewriter
    /// refuses if `on` is not policy-allowed on *both* legs (closes
    /// the join-key leak — see Lean `rewrite_refuses_unallowed_join_key`).
    Join {
        /// Left leg.
        left: Box<Plan>,
        /// Right leg.
        right: Box<Plan>,
        /// Join key (shared column).
        on: Column,
    },
}

impl Plan {
    /// Smart constructor for `Scan`.
    #[must_use]
    pub fn scan(rel: impl Into<Relation>) -> Self {
        Plan::Scan { rel: rel.into() }
    }

    /// Smart constructor for `Project`.
    #[must_use]
    pub fn project(sub: Plan, cols: impl IntoIterator<Item = impl Into<Column>>) -> Self {
        Plan::Project {
            sub: Box::new(sub),
            cols: cols.into_iter().map(Into::into).collect(),
        }
    }

    /// Smart constructor for `Filter`.
    #[must_use]
    pub fn filter(sub: Plan, col: impl Into<Column>) -> Self {
        Plan::Filter {
            sub: Box::new(sub),
            col: col.into(),
        }
    }

    /// Smart constructor for `Join`.
    #[must_use]
    pub fn join(left: Plan, right: Plan, on: impl Into<Column>) -> Self {
        Plan::Join {
            left: Box::new(left),
            right: Box::new(right),
            on: on.into(),
        }
    }

    /// `Plan.touched` — the single relation a plan reads from. For
    /// `Join`, by convention this is the left leg's touched relation;
    /// `touched_rels()` reports the multi-relation view used by
    /// `rewrite_sound_join` on the Lean side.
    #[must_use]
    pub fn touched(&self) -> &Relation {
        match self {
            Plan::Scan { rel } => rel,
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.touched(),
            Plan::Join { left, .. } => left.touched(),
        }
    }

    /// `Plan.touchedRels` — the multi-relation view (singleton for
    /// non-`Join`, concatenated legs for `Join`). Used by the
    /// generalised soundness statement.
    #[must_use]
    pub fn touched_rels(&self) -> Vec<Relation> {
        match self {
            Plan::Scan { rel } => vec![rel.clone()],
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.touched_rels(),
            Plan::Join { left, right, .. } => {
                let mut out = left.touched_rels();
                out.extend(right.touched_rels());
                out
            }
        }
    }

    /// `Plan.schema` — same shape as Lean's. `Project` intersects
    /// with the listed columns (preserving sub-plan order);
    /// `Filter` is row-only; `Join` concatenates left- then-right
    /// sub-schemas (caller must disambiguate column-name collisions
    /// upstream).
    #[must_use]
    pub fn schema(&self, cat: &Catalog) -> Vec<Column> {
        match self {
            Plan::Scan { rel } => cat.columns(rel),
            Plan::Project { sub, cols } => sub
                .schema(cat)
                .into_iter()
                .filter(|c| cols.contains(c))
                .collect(),
            Plan::Filter { sub, .. } => sub.schema(cat),
            Plan::Join { left, right, .. } => {
                let mut out = left.schema(cat);
                out.extend(right.schema(cat));
                out
            }
        }
    }

    /// `Plan.filterCols` — read-set of every `Filter` predicate in
    /// the plan, distinct from the output schema. Closes the
    /// side-channel where a forbidden column could be a row
    /// predicate without ever appearing in the output. For `Join`,
    /// concatenates both legs' filter columns. The join key itself
    /// is *not* a Filter read in this sense — the join-key leak is
    /// its own coverage condition (`Lean rewrite_refuses_unallowed_join_key`).
    #[must_use]
    pub fn filter_cols(&self) -> Vec<Column> {
        let mut out = Vec::new();
        self.collect_filter_cols(&mut out);
        out
    }

    fn collect_filter_cols(&self, acc: &mut Vec<Column>) {
        match self {
            Plan::Scan { .. } => {}
            Plan::Project { sub, .. } => sub.collect_filter_cols(acc),
            Plan::Filter { sub, col } => {
                acc.push(col.clone());
                sub.collect_filter_cols(acc);
            }
            Plan::Join { left, right, .. } => {
                left.collect_filter_cols(acc);
                right.collect_filter_cols(acc);
            }
        }
    }
}

/// `Grant` — `(principal, relation, columns)`. Multiple grants for
/// the same `(principal, relation)` flat-union via
/// `Policy::allowed` (no dedup), matching Lean's `flatMap`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Grant {
    /// Principal the grant applies to.
    pub principal: Principal,
    /// Relation the grant applies to.
    pub relation: Relation,
    /// Columns the principal may read.
    pub columns: Vec<Column>,
}

impl Grant {
    /// Smart constructor.
    pub fn new(
        principal: impl Into<Principal>,
        relation: impl Into<Relation>,
        columns: impl IntoIterator<Item = impl Into<Column>>,
    ) -> Self {
        Self {
            principal: principal.into(),
            relation: relation.into(),
            columns: columns.into_iter().map(Into::into).collect(),
        }
    }
}

/// Policy — ordered list of `Grant`s. Monotone grant-only (no deny
/// lists); deny-lists are paper §6 / future work.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Policy(Vec<Grant>);

impl Policy {
    /// Construct an empty policy.
    #[must_use]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Construct from an iterator of grants.
    pub fn from_grants(grants: impl IntoIterator<Item = Grant>) -> Self {
        Self(grants.into_iter().collect())
    }

    /// View the underlying grants.
    #[must_use]
    pub fn grants(&self) -> &[Grant] {
        &self.0
    }

    /// `Policy.allowed` — flat union of column lists across grants
    /// matching `(principal, relation)`. Preserves insertion order
    /// and duplicates so the Rust output is byte-equal to the Lean
    /// reference.
    #[must_use]
    pub fn allowed(&self, prin: &str, rel: &str) -> Vec<Column> {
        self.0
            .iter()
            .filter(|g| g.principal == prin && g.relation == rel)
            .flat_map(|g| g.columns.iter().cloned())
            .collect()
    }
}

/// `rewrite` — Rust mirror of `Postern.rewrite : Catalog → Policy →
/// Principal → Plan → Option Plan`.
///
/// Refusal conditions:
///   1. `cat.columns(plan.touched())` is empty — unknown relation.
///   2. any column read by a `Filter` predicate is not in the
///      principal's allowed set on the touched relation.
///   3. `Join`: either leg refuses; or the join key is not in the
///      principal's allowed set on *both* legs' touched relations
///      (closes the join-key leak — Lean
///      `rewrite_refuses_unallowed_join_key`).
///
/// On accept:
///   - Non-`Join` plans wrap in `Plan::Project` with
///     `cols = plan.schema(cat) ∩ policy.allowed(prin, plan.touched())`.
///   - `Join` plans compose per-leg rewrites under a `Plan::Join`
///     wrapper; the per-leg `Project` wrappers handle column
///     projection, mirroring the Lean rewriter.
pub fn rewrite(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan) -> Option<Plan> {
    if let Plan::Join { left, right, on } = plan {
        let l_rewritten = rewrite(cat, pol, prin, left)?;
        let r_rewritten = rewrite(cat, pol, prin, right)?;
        let allow_l = pol.allowed(prin, left.touched());
        let allow_r = pol.allowed(prin, right.touched());
        if !allow_l.contains(on) || !allow_r.contains(on) {
            return None;
        }
        return Some(Plan::Join {
            left: Box::new(l_rewritten),
            right: Box::new(r_rewritten),
            on: on.clone(),
        });
    }
    rewrite_leaf(cat, pol, prin, plan)
}

/// Single-relation rewriter body — mirrors `Postern.rewriteLeaf` on
/// the Lean side. Called by `rewrite` for `.scan / .project / .filter`
/// inputs; the `Join` arm is handled inline.
fn rewrite_leaf(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan) -> Option<Plan> {
    let touched = plan.touched();
    let cat_cols = cat.columns(touched);
    if cat_cols.is_empty() {
        return None;
    }
    let allow = pol.allowed(prin, touched);
    for fc in plan.filter_cols() {
        if !allow.contains(&fc) {
            return None;
        }
    }
    let cols = plan
        .schema(cat)
        .into_iter()
        .filter(|c| allow.contains(c))
        .collect();
    Some(Plan::Project {
        sub: Box::new(plan.clone()),
        cols,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_catalog() -> Catalog {
        Catalog::from_entries([
            (
                "users_data",
                vec!["id", "name", "email", "ssn", "region", "age"],
            ),
            (
                "cards_data",
                vec![
                    "card_id",
                    "user_id",
                    "card_number",
                    "card_type",
                    "limit",
                    "activated",
                ],
            ),
            (
                "transactions_data",
                vec!["txn_id", "card_id", "amount", "merchant", "timestamp"],
            ),
        ])
    }

    fn demo_policy() -> Policy {
        Policy::from_grants([
            Grant::new("CRM", "users_data", ["id", "name", "region", "age"]),
            Grant::new("FraudRisk", "users_data", ["id", "region"]),
        ])
    }

    #[test]
    fn crm_users_redacts_pii() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), "region"),
        )
        .expect("accept");
        assert_eq!(
            rw.schema(&demo_catalog()),
            vec!["id", "name", "region", "age"]
        );
        assert_eq!(rw.touched(), "users_data");
    }

    #[test]
    fn fraudrisk_users_minimal() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "FraudRisk",
            &Plan::scan("users_data"),
        )
        .expect("accept");
        assert_eq!(rw.schema(&demo_catalog()), vec!["id", "region"]);
    }

    #[test]
    fn unknown_principal_yields_empty_schema_but_accepts() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "Marketing",
            &Plan::scan("users_data"),
        )
        .expect("accept (unknown principal ⇒ empty allow ⇒ empty schema, not refusal)");
        assert!(rw.schema(&demo_catalog()).is_empty());
    }

    #[test]
    fn unknown_relation_refused() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::scan("credit_bureau_imports"),
        );
        assert!(rw.is_none(), "unknown relation must refuse");
    }

    #[test]
    fn filter_on_forbidden_column_refused() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), "ssn"),
        );
        assert!(rw.is_none(), "filter on ssn must refuse");
    }

    #[test]
    fn nested_filter_one_forbidden_still_refused() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::filter(Plan::scan("users_data"), "region"), "email"),
        );
        assert!(rw.is_none(), "any forbidden filter col must refuse");
    }

    #[test]
    fn duplicate_grants_flat_union() {
        let pol = Policy::from_grants([
            Grant::new("CRM", "users_data", ["id", "name"]),
            Grant::new("CRM", "users_data", ["name", "region"]),
        ]);
        // duplicates preserved per Lean's flatMap semantics
        assert_eq!(
            pol.allowed("CRM", "users_data"),
            vec!["id", "name", "name", "region"]
        );
    }

    #[test]
    fn empty_policy_accepts_empty_schema() {
        let rw = rewrite(
            &demo_catalog(),
            &Policy::new(),
            "CRM",
            &Plan::scan("users_data"),
        )
        .expect("accept");
        assert!(rw.schema(&demo_catalog()).is_empty());
    }

    #[test]
    fn join_legal_key_accepts() {
        // CRM joins users_data with itself on `id` (a column CRM is allowed to read
        // on both legs — degenerate but valid). Output schema = legs' schemas
        // concatenated, each projected to CRM's allow.
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::join(Plan::scan("users_data"), Plan::scan("users_data"), "id");
        let rw = rewrite(&cat, &pol, "CRM", &plan).expect("accept");
        // The result is Join(Project(scan, ...), Project(scan, ...), id).
        match &rw {
            Plan::Join { left, right, on } => {
                assert_eq!(on, "id");
                assert!(matches!(left.as_ref(), Plan::Project { .. }));
                assert!(matches!(right.as_ref(), Plan::Project { .. }));
            }
            _ => panic!("join output must be a Plan::Join"),
        }
        let schema = rw.schema(&cat);
        assert_eq!(
            schema,
            vec![
                "id", "name", "region", "age", // left leg
                "id", "name", "region", "age", // right leg (CRM has same allow on users_data)
            ]
        );
    }

    #[test]
    fn join_forbidden_key_refused() {
        // CRM tries to join users_data with itself on `ssn` — a column CRM is NOT
        // allowed to read. This is the join-key leak: refused.
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::join(Plan::scan("users_data"), Plan::scan("users_data"), "ssn");
        let rw = rewrite(&cat, &pol, "CRM", &plan);
        assert!(rw.is_none(), "join on forbidden column must refuse");
    }

    #[test]
    fn join_with_refusing_leg_refused() {
        // CRM joins users_data ⋈ unknown_relation — right leg's scan refuses
        // (unknown relation), so the whole join refuses.
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::join(
            Plan::scan("users_data"),
            Plan::scan("credit_bureau_imports"),
            "id",
        );
        let rw = rewrite(&cat, &pol, "CRM", &plan);
        assert!(rw.is_none(), "join with refusing leg must refuse");
    }

    #[test]
    fn case_sensitive_principal() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "crm",
            &Plan::scan("users_data"),
        )
        .expect("accept");
        assert!(
            rw.schema(&demo_catalog()).is_empty(),
            "crm ≠ CRM, no grants ⇒ empty schema"
        );
    }
}
