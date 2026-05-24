//! Postern core — Rust mirror of `verifier/lean/Postern.lean`.
//!
//! Types and the `rewrite` function deliberately match the Lean
//! reference one-for-one so the differential test harness can compare
//! outputs structurally. Any divergence here that changes behaviour
//! will surface as a `postern-diff` test failure.
//!
//! The Lean theorem `rewrite_sound` carries the correctness claim:
//! every column in the rewritten plan's output schema is allowed by
//! the policy for the requesting principal on the touched relation.
//! This crate must preserve that property; it is checked at test time
//! against the JSON corpus emitted by `lake exe postern-corpus`.

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub type Principal = String;
pub type Relation = String;
pub type Column = String;

/// Catalog slice — relation → ordered column list. The Lean spec
/// treats this as a total function; we model it as a partial map and
/// return an empty schema for unknown relations to match Lean's
/// `default := []` branch in `Demo.cat`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Catalog(pub BTreeMap<Relation, Vec<Column>>);

impl Catalog {
    pub fn columns(&self, rel: &str) -> Vec<Column> {
        self.0.get(rel).cloned().unwrap_or_default()
    }
}

/// Plan IR — mirrors the Lean `inductive Plan`. Tag layout matches
/// the JSON shape emitted by `Main.lean`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Plan {
    Scan {
        rel: Relation,
    },
    Project {
        sub: Box<Plan>,
        cols: Vec<Column>,
    },
    Filter {
        sub: Box<Plan>,
        col: Column,
    },
}

impl Plan {
    /// `Plan.touched` — every operator preserves the touched relation
    /// because single-relation plans are the only IR we model.
    pub fn touched(&self) -> &Relation {
        match self {
            Plan::Scan { rel } => rel,
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.touched(),
        }
    }

    /// `Plan.schema` — same shape as Lean's. `Project` intersects with
    /// the listed columns (preserving the sub-plan's order); `Filter`
    /// is row-only and leaves the schema untouched.
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
}

/// `Grant` — a (principal, relation, columns) tuple. Multiple grants
/// for the same (principal, relation) pair are flat-unioned by
/// `Policy::allowed`, matching Lean's `flatMap`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Grant {
    pub principal: Principal,
    pub relation: Relation,
    pub columns: Vec<Column>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Policy(pub Vec<Grant>);

impl Policy {
    /// `Policy.allowed` — flat union of column lists across grants
    /// matching `(principal, relation)`. Preserves insertion order so
    /// the Rust output is byte-equal to the Lean reference.
    pub fn allowed(&self, prin: &str, rel: &str) -> Vec<Column> {
        self.0
            .iter()
            .filter(|g| g.principal == prin && g.relation == rel)
            .flat_map(|g| g.columns.iter().cloned())
            .collect()
    }
}

/// `rewrite` — post-hoc projection: wrap the plan in a `Project`
/// whose column list is `schema(plan) ∩ allowed(P, prin, touched)`.
/// This is the exact algorithm proved sound in `Postern.lean`.
pub fn rewrite(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan) -> Plan {
    let allow = pol.allowed(prin, plan.touched());
    let cols = plan
        .schema(cat)
        .into_iter()
        .filter(|c| allow.contains(c))
        .collect();
    Plan::Project {
        sub: Box::new(plan.clone()),
        cols,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_catalog() -> Catalog {
        let mut m = BTreeMap::new();
        m.insert(
            "users_data".into(),
            vec!["id", "name", "email", "ssn", "region", "age"]
                .into_iter()
                .map(Into::into)
                .collect(),
        );
        m.insert(
            "cards_data".into(),
            vec![
                "card_id",
                "user_id",
                "card_number",
                "card_type",
                "limit",
                "activated",
            ]
            .into_iter()
            .map(Into::into)
            .collect(),
        );
        m.insert(
            "transactions_data".into(),
            vec!["txn_id", "card_id", "amount", "merchant", "timestamp"]
                .into_iter()
                .map(Into::into)
                .collect(),
        );
        Catalog(m)
    }

    fn demo_policy() -> Policy {
        Policy(vec![
            Grant {
                principal: "CRM".into(),
                relation: "users_data".into(),
                columns: vec!["id", "name", "region", "age"]
                    .into_iter()
                    .map(Into::into)
                    .collect(),
            },
            Grant {
                principal: "FraudRisk".into(),
                relation: "users_data".into(),
                columns: vec!["id", "region"].into_iter().map(Into::into).collect(),
            },
        ])
    }

    #[test]
    fn crm_users_redacts_pii() {
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::Filter {
            sub: Box::new(Plan::Scan {
                rel: "users_data".into(),
            }),
            col: "region".into(),
        };
        let rw = rewrite(&cat, &pol, "CRM", &plan);
        assert_eq!(rw.schema(&cat), vec!["id", "name", "region", "age"]);
        assert_eq!(rw.touched(), "users_data");
    }

    #[test]
    fn fraudrisk_users_minimal() {
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::Scan {
            rel: "users_data".into(),
        };
        let rw = rewrite(&cat, &pol, "FraudRisk", &plan);
        assert_eq!(rw.schema(&cat), vec!["id", "region"]);
    }

    #[test]
    fn unknown_principal_yields_empty_schema() {
        let cat = demo_catalog();
        let pol = demo_policy();
        let plan = Plan::Scan {
            rel: "users_data".into(),
        };
        let rw = rewrite(&cat, &pol, "Marketing", &plan);
        assert!(rw.schema(&cat).is_empty());
    }
}
