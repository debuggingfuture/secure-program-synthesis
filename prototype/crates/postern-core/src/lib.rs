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

    /// `Plan.touched` — every operator preserves the touched
    /// relation because single-relation plans are the only IR we
    /// model.
    #[must_use]
    pub fn touched(&self) -> &Relation {
        match self {
            Plan::Scan { rel } => rel,
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.touched(),
        }
    }

    /// `Plan.schema` — same shape as Lean's. `Project` intersects
    /// with the listed columns (preserving sub-plan order);
    /// `Filter` is row-only.
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
        }
    }

    /// `Plan.filterCols` — read-set of every `Filter` predicate in
    /// the plan, distinct from the output schema. Closes the
    /// side-channel where a forbidden column could be a row
    /// predicate without ever appearing in the output.
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
/// Returns `None` (refusal) when:
///   1. `cat.columns(plan.touched())` is empty — unknown relation; or
///   2. any column read by a `Filter` predicate is not in the
///      principal's allowed set on the touched relation.
///
/// Otherwise returns `Some(Plan::Project { sub: plan, cols })` where
/// `cols = plan.schema(cat) ∩ policy.allowed(prin, plan.touched())`.
pub fn rewrite(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan) -> Option<Plan> {
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
