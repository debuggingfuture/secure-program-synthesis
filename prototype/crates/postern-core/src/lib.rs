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
//!   `rewrite_filter_coverage` — every free col of every Filter
//!                               predicate ⊆ policy-allowed
//!                               (Theorem 13, pointwise φ-level)
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

/// Literal value inside a predicate term. The rewriter never
/// inspects literal values — only `Pred::free_cols` does — so
/// `String` is enough to faithfully mirror the Lean reference
/// (`abbrev Value := String`). The executor is responsible for
/// re-typing / re-coercing literals as needed.
pub type Value = String;

/// Operator label inside `Pred::App`. The rewriter is operator-
/// agnostic; only `Ref` contributes to `free_cols`.
pub type Op = String;

/// Predicate term — abstract syntax of a `Filter`'s WHERE clause.
/// Mirrors the Lean `inductive Pred` one-for-one. Three
/// constructors:
///
///   * `Ref { col }` — column reference; the only thing that
///     contributes to `free_cols`.
///   * `Lit { val }` — constant; opaque to the rewriter.
///   * `App { op, args }` — operator with predicate-term children.
///     The rewriter walks the tree; only `Ref` leaves matter.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Pred {
    /// Column reference.
    Ref {
        /// The column name.
        col: Column,
    },
    /// Literal value.
    Lit {
        /// The literal payload (opaque to the rewriter).
        val: Value,
    },
    /// Operator application.
    App {
        /// Operator label (e.g. `"="`, `"and"`).
        op: Op,
        /// Predicate-term arguments.
        args: Vec<Pred>,
    },
}

impl Pred {
    /// Smart constructor for `Ref`.
    #[must_use]
    pub fn r(col: impl Into<Column>) -> Self {
        Pred::Ref { col: col.into() }
    }

    /// Smart constructor for `Lit`.
    #[must_use]
    pub fn lit(val: impl Into<Value>) -> Self {
        Pred::Lit { val: val.into() }
    }

    /// Smart constructor for `App`.
    #[must_use]
    pub fn app(op: impl Into<Op>, args: impl IntoIterator<Item = Pred>) -> Self {
        Pred::App {
            op: op.into(),
            args: args.into_iter().collect(),
        }
    }

    /// `Pred.freeCols` — list every `Ref` reachable in the term,
    /// preserving order and duplicates so the encoding matches the
    /// Lean reference. The rewriter's coverage condition is
    /// `pred.free_cols() ⊆ policy.allowed(prin, touched(q))`.
    #[must_use]
    pub fn free_cols(&self) -> Vec<Column> {
        let mut out = Vec::new();
        self.collect_free_cols(&mut out);
        out
    }

    fn collect_free_cols(&self, acc: &mut Vec<Column>) {
        match self {
            Pred::Ref { col } => acc.push(col.clone()),
            Pred::Lit { .. } => {}
            Pred::App { args, .. } => {
                for a in args {
                    a.collect_free_cols(acc);
                }
            }
        }
    }
}

/// Closed enumeration of aggregate operators. Mirrors Lean's
/// `inductive AggOp` and the JSON tags in `Main.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AggOp {
    /// Sum of column values.
    Sum,
    /// Count of rows (per group).
    Count,
    /// Minimum value.
    Min,
    /// Maximum value.
    Max,
    /// Arithmetic mean.
    Avg,
}

impl AggOp {
    /// The label prefix for the synthesized output column name
    /// (`Sum`, `Count`, `Min`, `Max`, `Avg`). Must match
    /// `Postern.AggOp.label` byte-for-byte.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            AggOp::Sum => "Sum",
            AggOp::Count => "Count",
            AggOp::Min => "Min",
            AggOp::Max => "Max",
            AggOp::Avg => "Avg",
        }
    }

    /// Synthesized output column name for the aggregate's result
    /// — `<Label>_<col>` (e.g. `Sum_amount`). Must match
    /// `Postern.AggOp.outputColumn` byte-for-byte.
    #[must_use]
    pub fn output_column(self, col: &str) -> Column {
        format!("{}_{}", self.label(), col)
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
    /// Row-only predicate; schema unchanged. `pred` is the
    /// predicate-term whose free-column set the rewriter checks
    /// for policy-coverage (Theorem 13). The rewriter is
    /// operator-agnostic — only `Pred::Ref` leaves contribute to
    /// the coverage check.
    Filter {
        /// Sub-plan.
        sub: Box<Plan>,
        /// Predicate term — see [`Pred`].
        pred: Pred,
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
    /// Aggregate — `op(col)` grouped by `group_by`, computed over
    /// `inner`. The output schema is `group_by ++ [op.output_column(col)]`.
    /// Soundness is parameterised over the abstract DP boundary
    /// (`Policy::agg_allowed`) — see Lean theorem
    /// `rewrite_sound_aggregate`.
    Aggregate {
        /// Aggregate operator.
        agg: AggOp,
        /// Column the aggregate reads.
        col: Column,
        /// Group-by columns (must be policy-allowed under the
        /// standard column-grant rule).
        #[serde(rename = "groupBy")]
        group_by: Vec<Column>,
        /// Sub-plan whose rows feed the aggregate.
        inner: Box<Plan>,
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

    /// Smart constructor for `Filter` with a predicate term.
    #[must_use]
    pub fn filter(sub: Plan, pred: Pred) -> Self {
        Plan::Filter {
            sub: Box::new(sub),
            pred,
        }
    }

    /// Convenience smart constructor for the common case
    /// `Filter(sub, Ref(col))` — keeps test/demo sites concise and
    /// matches the bare-column ergonomics of the pre-C2 IR for
    /// migration purposes. Equivalent to
    /// `Plan::filter(sub, Pred::r(col))`.
    #[must_use]
    pub fn filter_col(sub: Plan, col: impl Into<Column>) -> Self {
        Plan::Filter {
            sub: Box::new(sub),
            pred: Pred::r(col),
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

    /// Smart constructor for `Aggregate`.
    #[must_use]
    pub fn aggregate(
        agg: AggOp,
        col: impl Into<Column>,
        group_by: impl IntoIterator<Item = impl Into<Column>>,
        inner: Plan,
    ) -> Self {
        Plan::Aggregate {
            agg,
            col: col.into(),
            group_by: group_by.into_iter().map(Into::into).collect(),
            inner: Box::new(inner),
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
            Plan::Aggregate { inner, .. } => inner.touched(),
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
            Plan::Aggregate { inner, .. } => inner.touched_rels(),
        }
    }

    /// `Plan.schema` — same shape as Lean's. `Project` intersects
    /// with the listed columns (preserving sub-plan order);
    /// `Filter` is row-only; `Join` concatenates left- then-right
    /// sub-schemas (caller must disambiguate column-name collisions
    /// upstream); `Aggregate` exposes the group-by columns plus a
    /// single synthesized result column (`op.output_column(col)`).
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
            Plan::Aggregate {
                agg, col, group_by, ..
            } => {
                let mut out = group_by.clone();
                out.push(agg.output_column(col));
                out
            }
        }
    }

    /// `Plan.filterCols` — read-set of every `Filter` predicate in
    /// the plan, distinct from the output schema. Closes the
    /// side-channel where a forbidden column could be a row
    /// predicate without ever appearing in the output. For `Join`,
    /// concatenates both legs' filter columns. `Aggregate` recurses
    /// into its `inner` sub-plan; aggregates themselves are not
    /// row-selection. The join key itself is *not* a Filter read in
    /// this sense — the join-key leak is its own coverage condition
    /// (`Lean rewrite_refuses_unallowed_join_key`).
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
            Plan::Filter { sub, pred } => {
                pred.collect_free_cols(acc);
                sub.collect_filter_cols(acc);
            }
            Plan::Join { left, right, .. } => {
                left.collect_filter_cols(acc);
                right.collect_filter_cols(acc);
            }
            Plan::Aggregate { inner, .. } => inner.collect_filter_cols(acc),
        }
    }

    /// `Plan.preds` — every `Pred` term at any `Filter` node inside
    /// `self`, outer-to-inner. Mirrors Lean's `Plan.preds` and feeds
    /// the predicate-level coverage statement (Theorem 13).
    #[must_use]
    pub fn preds(&self) -> Vec<Pred> {
        let mut out = Vec::new();
        self.collect_preds(&mut out);
        out
    }

    fn collect_preds(&self, acc: &mut Vec<Pred>) {
        match self {
            Plan::Scan { .. } => {}
            Plan::Project { sub, .. } => sub.collect_preds(acc),
            Plan::Filter { sub, pred } => {
                acc.push(pred.clone());
                sub.collect_preds(acc);
            }
            Plan::Join { left, right, .. } => {
                left.collect_preds(acc);
                right.collect_preds(acc);
            }
            Plan::Aggregate { inner, .. } => inner.collect_preds(acc),
        }
    }

    /// `Plan.aggregates` — every `(op, col)` pair appearing in an
    /// `Aggregate` node in the plan. Drives the DP-boundary check
    /// in `rewrite`.
    #[must_use]
    pub fn aggregates(&self) -> Vec<(AggOp, Column)> {
        let mut out = Vec::new();
        self.collect_aggregates(&mut out);
        out
    }

    fn collect_aggregates(&self, acc: &mut Vec<(AggOp, Column)>) {
        match self {
            Plan::Scan { .. } => {}
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.collect_aggregates(acc),
            Plan::Join { left, right, .. } => {
                left.collect_aggregates(acc);
                right.collect_aggregates(acc);
            }
            Plan::Aggregate {
                agg, col, inner, ..
            } => {
                acc.push((*agg, col.clone()));
                inner.collect_aggregates(acc);
            }
        }
    }

    /// `Plan.groupByCols` — every column appearing as a `group_by`
    /// key in an `Aggregate` node. Standard column-grant rule
    /// (not the DP boundary) gates these.
    #[must_use]
    pub fn group_by_cols(&self) -> Vec<Column> {
        let mut out = Vec::new();
        self.collect_group_by_cols(&mut out);
        out
    }

    fn collect_group_by_cols(&self, acc: &mut Vec<Column>) {
        match self {
            Plan::Scan { .. } => {}
            Plan::Project { sub, .. } | Plan::Filter { sub, .. } => sub.collect_group_by_cols(acc),
            Plan::Join { left, right, .. } => {
                left.collect_group_by_cols(acc);
                right.collect_group_by_cols(acc);
            }
            Plan::Aggregate {
                group_by, inner, ..
            } => {
                acc.extend(group_by.iter().cloned());
                inner.collect_group_by_cols(acc);
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

/// *Aggregate-only* capability — "principal may compute `op(col)`
/// over `rel`" without read access to the underlying column. The
/// DP boundary (paper §6) is **abstract** here: a concrete
/// mechanism (ε-budget, k-anonymity, Laplace noise) refines the
/// `agg_allowed` predicate at policy-evaluation time; the
/// rewriter and the Lean soundness theorem are stated against
/// this predicate, not against any specific mechanism.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AggGrant {
    /// Principal the grant applies to.
    pub principal: Principal,
    /// Relation the grant applies to.
    pub relation: Relation,
    /// Aggregate operator.
    pub op: AggOp,
    /// Column the aggregate may read.
    pub column: Column,
}

impl AggGrant {
    /// Smart constructor.
    pub fn new(
        principal: impl Into<Principal>,
        relation: impl Into<Relation>,
        op: AggOp,
        column: impl Into<Column>,
    ) -> Self {
        Self {
            principal: principal.into(),
            relation: relation.into(),
            op,
            column: column.into(),
        }
    }
}

/// Policy — column grants plus aggregate-only grants. Monotone
/// grant-only (no deny lists); deny-lists are paper §6 / future
/// work. The aggregate-only branch parameterises the DP boundary
/// (see `AggGrant` doc).
///
/// Deserialization accepts **two shapes** for backward compatibility:
///   1. The new struct form `{"grants": [...], "aggGrants": [...]}`
///      (emitted by Lean's `postern-corpus`).
///   2. The legacy array form `[grant, grant, ...]` (used by older
///      JS callers and pre-C3 demos) — interpreted as `grants` with
///      empty `aggGrants`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize)]
pub struct Policy {
    /// Ordinary column grants.
    pub grants: Vec<Grant>,
    /// Aggregate-only grants — the abstract DP boundary surface.
    #[serde(rename = "aggGrants")]
    pub agg_grants: Vec<AggGrant>,
}

impl<'de> Deserialize<'de> for Policy {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct PolicyStruct {
            #[serde(default)]
            grants: Vec<Grant>,
            #[serde(default, rename = "aggGrants")]
            agg_grants: Vec<AggGrant>,
        }

        #[derive(Deserialize)]
        #[serde(untagged)]
        enum PolicyRepr {
            // New canonical shape — must come first so it wins when
            // both forms are syntactically valid (empty object {}).
            Struct(PolicyStruct),
            // Legacy: bare array of grants.
            Legacy(Vec<Grant>),
        }

        let raw = PolicyRepr::deserialize(deserializer)?;
        Ok(match raw {
            PolicyRepr::Struct(s) => Policy {
                grants: s.grants,
                agg_grants: s.agg_grants,
            },
            PolicyRepr::Legacy(grants) => Policy {
                grants,
                agg_grants: Vec::new(),
            },
        })
    }
}

impl Policy {
    /// Construct an empty policy.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Construct from column grants alone (no aggregate-only
    /// capability). Convenience for the pre-aggregation regime.
    pub fn from_grants(grants: impl IntoIterator<Item = Grant>) -> Self {
        Self {
            grants: grants.into_iter().collect(),
            agg_grants: Vec::new(),
        }
    }

    /// Construct from both grant kinds.
    pub fn from_parts(
        grants: impl IntoIterator<Item = Grant>,
        agg_grants: impl IntoIterator<Item = AggGrant>,
    ) -> Self {
        Self {
            grants: grants.into_iter().collect(),
            agg_grants: agg_grants.into_iter().collect(),
        }
    }

    /// View the underlying column grants.
    #[must_use]
    pub fn grants(&self) -> &[Grant] {
        &self.grants
    }

    /// View the underlying aggregate-only grants.
    #[must_use]
    pub fn agg_grants(&self) -> &[AggGrant] {
        &self.agg_grants
    }

    /// `Policy.allowed` — flat union of column lists across grants
    /// matching `(principal, relation)`. Preserves insertion order
    /// and duplicates so the Rust output is byte-equal to the Lean
    /// reference.
    #[must_use]
    pub fn allowed(&self, prin: &str, rel: &str) -> Vec<Column> {
        self.grants
            .iter()
            .filter(|g| g.principal == prin && g.relation == rel)
            .flat_map(|g| g.columns.iter().cloned())
            .collect()
    }

    /// `Policy.aggAllowed` — does the policy carry an aggregate-only
    /// grant for `(prin, rel, op, col)`? The **abstract DP boundary**:
    /// concrete mechanisms refine this predicate (ε-budget remaining,
    /// k-anonymity threshold met, Laplace mechanism parameters) at
    /// the executor, but the rewriter only inspects the grant.
    #[must_use]
    pub fn agg_allowed(&self, prin: &str, rel: &str, op: AggOp, col: &str) -> bool {
        self.agg_grants
            .iter()
            .any(|g| g.principal == prin && g.relation == rel && g.op == op && g.column == col)
    }

    /// `aggAdmissible` — the `op(col)` aggregate over `rel` for
    /// `prin` is admissible iff either `col` is in the standard
    /// column-grant set, **or** the policy carries an `AggGrant`
    /// (the parameterised DP boundary).
    #[must_use]
    pub fn agg_admissible(&self, prin: &str, rel: &str, op: AggOp, col: &str) -> bool {
        self.allowed(prin, rel).iter().any(|c| c == col) || self.agg_allowed(prin, rel, op, col)
    }

    /// `Policy.allowedOutputs` — `allowed` extended with one
    /// synthesized name per admissible aggregate in the plan.
    /// Defines the *output*-side coverage set against which the
    /// rewriter filters columns.
    #[must_use]
    pub fn allowed_outputs(&self, prin: &str, rel: &str, plan: &Plan) -> Vec<Column> {
        let mut out = self.allowed(prin, rel);
        for (op, col) in plan.aggregates() {
            if self.agg_admissible(prin, rel, op, &col) {
                out.push(op.output_column(&col));
            }
        }
        out
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
/// the Lean side. Called by `rewrite` for `.scan / .project / .filter
/// / .aggregate` inputs; the `Join` arm is handled inline. Four
/// nested refusal guards: catalog non-empty; filterCols all
/// column-allowed; groupByCols all column-allowed; aggregates all
/// admissible under the abstract DP boundary.
fn rewrite_leaf(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan) -> Option<Plan> {
    let touched = plan.touched();
    let cat_cols = cat.columns(touched);
    if cat_cols.is_empty() {
        return None;
    }
    let allow = pol.allowed(prin, touched);
    // Filter-predicate guard — close the row-selection side channel.
    for fc in plan.filter_cols() {
        if !allow.contains(&fc) {
            return None;
        }
    }
    // Group-by guard — group keys appear verbatim in the output and
    // must be allowed under the standard column-grant rule.
    for gb in plan.group_by_cols() {
        if !allow.contains(&gb) {
            return None;
        }
    }
    // Aggregate guard — DP boundary applies: either the column is
    // directly allowed, or the policy carries an AggGrant.
    for (op, col) in plan.aggregates() {
        if !pol.agg_admissible(prin, touched, op, &col) {
            return None;
        }
    }
    let allowed_outputs = pol.allowed_outputs(prin, touched, plan);
    let cols = plan
        .schema(cat)
        .into_iter()
        .filter(|c| allowed_outputs.contains(c))
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
            &Plan::filter_col(Plan::scan("users_data"), "region"),
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
            &Plan::filter_col(Plan::scan("users_data"), "ssn"),
        );
        assert!(rw.is_none(), "filter on ssn must refuse");
    }

    #[test]
    fn nested_filter_one_forbidden_still_refused() {
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter_col(
                Plan::filter_col(Plan::scan("users_data"), "region"),
                "email",
            ),
        );
        assert!(rw.is_none(), "any forbidden filter col must refuse");
    }

    #[test]
    fn pred_compound_allowed_only_accepts() {
        // `region = "EU"` — refs only the allowed `region` column.
        let pred = Pred::app("=", [Pred::r("region"), Pred::lit("EU")]);
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), pred),
        )
        .expect("compound predicate over allowed col must accept");
        assert_eq!(
            rw.schema(&demo_catalog()),
            vec!["id", "name", "region", "age"]
        );
    }

    #[test]
    fn pred_compound_one_forbidden_refused() {
        // `region = "EU" AND ssn = "X"` — one forbidden ref taints the whole predicate.
        let pred = Pred::app(
            "and",
            [
                Pred::app("=", [Pred::r("region"), Pred::lit("EU")]),
                Pred::app("=", [Pred::r("ssn"), Pred::lit("X")]),
            ],
        );
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), pred),
        );
        assert!(
            rw.is_none(),
            "compound predicate with one forbidden ref must refuse"
        );
    }

    #[test]
    fn pred_negation_allowed_accepts() {
        // `NOT (age = 18)` — every ref is to an allowed column.
        let pred = Pred::app("not", [Pred::app("=", [Pred::r("age"), Pred::lit("18")])]);
        let rw = rewrite(
            &demo_catalog(),
            &demo_policy(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), pred),
        )
        .expect("negation over allowed col must accept");
        assert_eq!(
            rw.schema(&demo_catalog()),
            vec!["id", "name", "region", "age"]
        );
    }

    #[test]
    fn pred_free_cols_walks_nested_app() {
        // Sanity check the `Pred::free_cols` traversal independent
        // of `rewrite` — preserves order, includes duplicates.
        let pred = Pred::app(
            "and",
            [
                Pred::r("a"),
                Pred::app("=", [Pred::r("b"), Pred::lit("x")]),
                Pred::r("a"),
            ],
        );
        assert_eq!(pred.free_cols(), vec!["a", "b", "a"]);
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

    fn analytics_policy() -> Policy {
        Policy::from_parts(
            [Grant::new(
                "FraudRisk",
                "transactions_data",
                ["txn_id", "card_id", "amount", "merchant", "timestamp"],
            )],
            [
                AggGrant::new("Analytics", "transactions_data", AggOp::Sum, "amount"),
                AggGrant::new("Analytics", "transactions_data", AggOp::Count, "txn_id"),
            ],
        )
    }

    #[test]
    fn agg_sum_amount_analytics_via_agggrant() {
        let plan = Plan::aggregate(
            AggOp::Sum,
            "amount",
            Vec::<String>::new(),
            Plan::scan("transactions_data"),
        );
        let rw = rewrite(&demo_catalog(), &analytics_policy(), "Analytics", &plan)
            .expect("AggGrant lets Analytics compute Sum(amount)");
        assert_eq!(rw.schema(&demo_catalog()), vec!["Sum_amount"]);
    }

    #[test]
    fn agg_avg_amount_analytics_refused() {
        let plan = Plan::aggregate(
            AggOp::Avg,
            "amount",
            Vec::<String>::new(),
            Plan::scan("transactions_data"),
        );
        let rw = rewrite(&demo_catalog(), &analytics_policy(), "Analytics", &plan);
        assert!(
            rw.is_none(),
            "no AggGrant for Avg(amount) ⇒ DP boundary refuses"
        );
    }

    #[test]
    fn agg_sum_amount_fraudrisk_trivial() {
        let plan = Plan::aggregate(
            AggOp::Sum,
            "amount",
            Vec::<String>::new(),
            Plan::scan("transactions_data"),
        );
        let rw = rewrite(&demo_catalog(), &analytics_policy(), "FraudRisk", &plan)
            .expect("FraudRisk has column-grant on amount ⇒ aggregate dominates");
        assert_eq!(rw.schema(&demo_catalog()), vec!["Sum_amount"]);
    }

    #[test]
    fn agg_group_by_forbidden_column_refused() {
        let plan = Plan::aggregate(
            AggOp::Sum,
            "amount",
            ["merchant"],
            Plan::scan("transactions_data"),
        );
        let rw = rewrite(&demo_catalog(), &analytics_policy(), "Analytics", &plan);
        assert!(
            rw.is_none(),
            "Analytics has no column-grant on merchant ⇒ groupBy refuses"
        );
    }

    #[test]
    fn agg_output_column_label_matches_lean() {
        assert_eq!(AggOp::Sum.output_column("amount"), "Sum_amount");
        assert_eq!(AggOp::Count.output_column("txn_id"), "Count_txn_id");
        assert_eq!(AggOp::Min.output_column("x"), "Min_x");
        assert_eq!(AggOp::Max.output_column("x"), "Max_x");
        assert_eq!(AggOp::Avg.output_column("x"), "Avg_x");
    }

    #[test]
    fn policy_deserialize_legacy_array() {
        // Pre-aggregation JS callers send the legacy array shape.
        let json = r#"[{"principal":"CRM","relation":"users_data","columns":["id"]}]"#;
        let pol: Policy = serde_json::from_str(json).unwrap();
        assert_eq!(pol.grants().len(), 1);
        assert!(pol.agg_grants().is_empty());
    }

    #[test]
    fn policy_deserialize_struct_shape() {
        let json = r#"{"grants":[{"principal":"CRM","relation":"users_data","columns":["id"]}],"aggGrants":[{"principal":"Analytics","relation":"transactions_data","op":"sum","column":"amount"}]}"#;
        let pol: Policy = serde_json::from_str(json).unwrap();
        assert_eq!(pol.grants().len(), 1);
        assert_eq!(pol.agg_grants().len(), 1);
    }
}
