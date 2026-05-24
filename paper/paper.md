---
title: "Postern: a Lean-verified access gateway for agentic data lakehouses"
subtitle: "Secure Program Synthesis Hackathon 2026 — Track 3 research artifact"
author:
  - name: FractalBox
abstract: |
  Per-source authorization is *non-compositional* under ETL
  fusion: when $n$ heterogeneous sources are materialised into a
  single columnar lakehouse, the per-source guards (channel ACLs,
  field-level security, OAuth-scoped tokens) have no representative
  in the lake's authorization surface, and the effective permission
  of a query-issuing agent becomes the *union* of the upstream
  principals rather than the *intersection* under the querying
  identity. **Postern** closes this gap at the plan boundary: a
  verified gateway that rewrites every
  dataframe plan against a column-grant policy before it reaches the
  executor. The core — Plan IR, policy, rewriter — is mechanized in
  Lean 4 with nine `sorry`-free theorems, including
  *output-column soundness* and *filter-predicate soundness*
  (closing the `WHERE ssn = ?` side-channel the IR previously
  admitted). A Rust mirror runs the same algorithm and is
  **conformance-tested against a Lean-emitted JSON reference
  corpus** of 18 cases (15 accept, 3 refusal), all green. We
  exercise the artifact on a 3-department financial-institution
  scenario and identify three load-bearing open problems — joins,
  aggregation / DP, capability attenuation.
keywords:
  - access control
  - formal verification
  - Lean 4
  - data lakehouse
  - LLM agents
  - conformance testing
---

# Introduction

The deployment shape of an agentic system in 2026 has two
properties that 2024-era access control was not designed for.
**(i)** Context is materialized from heterogeneous upstream sources
into a single columnar lakehouse — typically DuckDB over Parquet on
S3 [@duckdb] — populated by ETL pipelines [@mem0]. **(ii)** The
agent itself *issues* the dataframe query, through MCP tools [@mcp];
indirect prompt-injection benchmarks [@agentdojo2024; @camel2025]
make the case that the agent must be treated as adversarial.

**The combination breaks per-source authorization.** For upstream
sources $S_1, \ldots, S_n$ with access-control denotations
$A_1, \ldots, A_n$, the materialized lakehouse
$L = \bigcup_i S_i$ has authorization denotation $A_L$ determined
by the ingest service-account's IAM role alone; the originals
$\{A_i\}$ have no semantic representative in $A_L$. The effective
permission of an agent querying $L$ is the *union* of upstream
principals' permissions, not the *intersection* under the querying
identity. Concretely: when Slack channel ACLs, Salesforce field-
level security, and Stripe customer-scoped tokens all collapse to
one DuckDB service-account role at ingest, an indirect-prompt-
injected agent inherits the read surface of the ingest service
itself.

**Postern** restores the boundary with a two-layer verified
gateway.

- **Layer 1 — plan boundary.** A column-grant policy DSL and a
  plan rewriter whose soundness is mechanized in Lean 4 [@lean4].
  For every accepted plan two invariants hold: the output schema
  is contained in the policy-allowed columns
  (`rewrite_sound`), and every column read by a `Filter` predicate
  is policy-allowed (`rewrite_filter_sound`, closing the
  `WHERE ssn = ?` side-channel). Refusal is explicit — unknown
  relations and forbidden filter columns produce `None`, not
  silently empty schemas.

- **Layer 2 — agent-code boundary.** A Rust capability-tracking
  layer inspired by Odersky et al. 2026
  [@capabilities-agents-2026], which proposes Scala 3
  capture-checking for the same purpose. The verified output of
  Layer 1 is wrapped in `Tagged<T, C>` and handed to the agent
  together with a single-use `Cap<C>`. Sanctioned compute
  operations (`map`, `and_then`) preserve the tag; un-tagging
  requires consuming the Cap at a sanctioned sink. Capabilities
  are unforgeable — sealed types, private constructors — so
  downstream agent code cannot mint a Cap, and the inner value of
  `Tagged` is unreachable without one.

The two layers are stack-complementary. Layer 1's correctness is
mechanized (Lean theorems); Layer 2's correctness reduces to Rust's
privacy and ownership rules, and we exhibit two bypass attempts
that fail at compile time (forging `Cap`, accessing
`Tagged::value`).

## Contributions

1. **Mechanized plan-boundary core (Layer 1).** A Plan IR
   (`Scan`/`Project`/`Filter`), a column-grant policy language,
   and `rewrite : Catalog → Policy → Principal → Plan → Option Plan`,
   all in Lean 4. **Nine** `sorry`-free theorems span output-
   column soundness, filter-predicate soundness, schema subset,
   monotonicity in policy, idempotence, and explicit-refusal
   lemmas for unknown relations and forbidden filter columns
   (§4). Per-theorem axiom dependencies are audited
   (`CheckAxioms.lean`) and bounded by `{propext, Quot.sound}` —
   Lean's built-in foundational axioms; two theorems depend on
   none.

2. **Capability-tracking guardrail (Layer 2).** A Rust crate
   `postern-guardrail` providing sealed `Cap<C>` and
   `Tagged<T, C>` types and a `gateway::issue_plan` entry point
   that combines the verified rewrite with capability issuance.
   Two bypass attempts are pinned as `compile_fail` doctests:
   constructing `Cap` outside the crate, and reading
   `Tagged::value` directly. Rust has no effect system, so the
   layer's perimeter is the type system's privacy boundary; we
   discuss the limits in §3.

3. **Rust mirror + reference-conformance harness.** A Rust crate
   `postern-core` mirrors the Lean types and rewriter byte-for-
   byte (target deployment: a Polars [@polars] / DuckDB gateway
   with biscuit-token [@biscuit] capability distribution). The
   harness `postern-diff` ingests a JSON corpus emitted by Lean
   and asserts byte-equivalence of the resulting `Option<Plan>`,
   schema, predicate read-set, and touched relation. **18 / 18
   cases pass**, including three refusal regressions for known
   attack shapes (filter-on-forbidden-column, unknown-relation,
   nested forbidden filter). We label this *reference-conformance
   testing*, not QuickCheck-style differential testing — the
   corpus is hand-curated; property-based generation is §6.

4. **Financial-institution case study.** Kaggle
   `transactions-fraud-datasets` with three principals
   (CRM, CardOps, FraudRisk) exercising PII redaction, cross-
   department refusal, and minimum-necessary disclosure (§5). Each
   row of the demo table is a corpus case driving the conformance
   harness.

# Plan IR (preview)

For §2 and §3 to be readable in one pass we state the IR up front:

```
Plan ::= Scan(rel)
       | Project(plan, cols)
       | Filter(plan, col)
```

`Project(p, cs)` keeps only `cs ∩ schema(p)`. `Filter(p, c)` is
row-only — the column `c` is *read* by the predicate but does not
appear in the output schema. This asymmetry is what makes the
filter side-channel real.

# Threat model

We assume a trusted gateway holding the policy and the
cryptographic root for capability tokens. Everything else is
untrusted:

| Component                                  | Trust | Notes                                                          |
| ------------------------------------------ | :---: | -------------------------------------------------------------- |
| LLM / agent (planner)                      |   ✗   | Jailbreakable; may emit hostile SQL / dataframe ops.            |
| Tool-generated code                        |   ✗   | Indirect injection from retrieved context; supply chain.        |
| Capability tokens [@biscuit]               |   ~   | Trusted *only* once the gateway verifies the signature.         |
| Gateway process (Postern, this paper)      |   ✓   | TCB. Holds the Lean-verified rewriter and the policy.           |
| **Catalog** (relation → columns map)       |   ✓   | TCB. Assumed bound to the physical Parquet schema (§6).         |
| **Plan-to-executor lowering**              |   ✓   | TCB. We trust the rewritten plan is honoured literally by DuckDB. |
| **Principal-string extraction from token** |   ✓   | TCB. A buggy biscuit verifier defeats every theorem below.      |
| DuckDB + Parquet store                     |   ✓   | TCB.                                                            |

**In-scope attacks the rewriter defeats.** (i) Over-projection of
forbidden columns. (ii) Filter on a forbidden column (the
`WHERE ssn = ?` side-channel — closed by
`rewrite_filter_sound`). (iii) Scan of an un-attested relation
(closed by `rewrite_refuses_unknown`). (iv) Cross-department reach
by a principal with no matching grants. (v) Unknown principals
(fail-closed: empty allow ⇒ empty schema).

**Out of scope (paper §6).** Aggregation / inference attacks;
covert channels through query latency or row counts; multi-relation
joins; biscuit-token attenuation inside the proof; policy
synthesis from natural language; the planner→executor lowering
step.

# Design

Postern compiles a single policy artifact to plan-level enforcement.

```mermaid
flowchart LR
  agent[LLM agent] -->|MCP plan + biscuit| gw{{Postern gateway}}
  subgraph TCB
    gw -->|verify| bc[biscuit verifier]
    bc -->|principal| rw[Lean-extracted rewriter]
    pol[(policy)] --> rw
    cat[(catalog)] --> rw
    rw -->|Option Plan| exe[DuckDB / Polars]
  end
  exe --> agent
```

## Policy

A policy is a list of **column-grants** $\langle p, r, C \rangle$:
"principal $p$ may read columns $C$ on relation $r$". Multiple
grants for the same $(p, r)$ flat-union. Anything outside the
union is denied — fail-closed. **No deny-lists**: the policy
language is deliberately monotone grant-only, which makes policy
review additive (a new grant can only widen). Deny-lists and
attribute-based predicates are §6.

## Rewriter

```
rewrite cat P prin q :=
  if cat q.touched = [] then     none                          -- unknown relation
  else if ¬ q.filterCols ⊆ allow then  none                    -- forbidden filter col
  else
    some (Project q (q.schema cat ∩ allow))
  where allow := P.allowed prin q.touched
```

Post-hoc projection is the simplest algorithm that admits a clean
soundness proof. Predicate-pushdown variants can be verified
against this rewriter as a reference; we leave that to future work.

## Layer 2: capability-tracking guardrail

Layer 1 (the Lean rewriter) bounds *what data reaches the agent*.
Layer 2 bounds *what the agent's compute can do with it*. Odersky
et al. [@capabilities-agents-2026] propose using Scala 3
capture-checking for exactly this — capabilities as first-class
program variables, so agent-generated code cannot exfiltrate data
it does not hold a capability for. Rust has no capture-checking,
but the same intuition can be mechanized via **sealed types**:
capabilities are unforgeable tokens minted only by the gateway,
and data is wrapped in `Tagged<T, C>` whose inner value cannot be
reached without consuming a matching `Cap<C>`.

The `postern-guardrail` crate provides:

```rust
// Sealed: only the gateway can mint; downstream cannot construct.
pub struct Cap<C: 'static> { /* private fields */ }
pub struct Tagged<T, C: 'static> { /* private value */ }

impl<T, C: 'static> Tagged<T, C> {
  pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Tagged<U, C>;
  pub fn and_then<U>(self, f: impl FnOnce(T) -> Tagged<U, C>) -> Tagged<U, C>;
  pub fn release(self, _: Cap<C>) -> T;   // single-use: Cap moves
}

pub mod gateway {
  pub fn issue_plan(cat: &Catalog, pol: &Policy, prin: &str, plan: &Plan)
    -> Option<(Tagged<Plan, AllowedColumns>, Cap<AllowedColumns>)>;
  // None iff Layer 1's `rewrite` refused.
}
```

The gateway's `issue_plan` is the only entry to capability minting:
it runs the verified rewriter and, on accept, returns a
`Tagged<Plan, AllowedColumns>` together with its single-use
`Cap<AllowedColumns>`. Agent code may compose the value through
`map` / `and_then` (the tag is preserved by construction) but the
only path back to a raw `T` is `release(cap)`, which consumes the
Cap.

**What this defends against.** Forging a Cap (`Cap` is sealed),
reading `Tagged::value` directly (private field), and using a
released Cap twice (consumed by `release`). The first two are
demonstrated as `compile_fail` doctests in the crate: an
attempt to construct a `Cap` or to project `t.value` does not
type-check.

**What it does not defend against.** Rust has no effect system. A
capability-bearing agent can still side-channel through `panic!`,
timing, or thread-local globals. We make `Cap: !Send + !Sync` (via
`PhantomData<*const ()>`) to close the obvious thread-move, and
deliberately do not implement `Display` / `Debug` for `Tagged`, but
a determined adversary inside the agent runtime is out of scope.
The full hardening path — a custom lint or `unsafe`-style markers
gating exit sinks — is §6.

# Formal model

Mechanized in `verifier/lean/Postern.lean`. Build with `lake build`;
the per-theorem axiom set is reported by `CheckAxioms.lean`.

**Theorem 1 (`rewrite_sound`).** If
$\texttt{rewrite}\ cat\ P\ prin\ q = \texttt{some}\ q'$, then for
every column $c$ in $q'\!.\texttt{schema}\ cat$,
$c \in P.\texttt{allowed}\ prin\ q.\texttt{touched}$. *Every
column appearing in the rewritten plan's output schema is one the
policy permits.*

**Theorem 2 (`rewrite_filter_sound`).** Under the same accept
hypothesis, every column read by a `Filter` predicate inside $q'$
is policy-allowed. **Closes the side-channel** in which a
principal who cannot *read* `ssn` could still filter on it.

**Theorem 3 (`rewrite_schema_subset`)** and **Theorem 4
(`rewrite_no_new_columns`).** The rewriter only ever removes
columns — never invents them.

**Theorem 5 (`rewrite_idempotent`).** Rewriting twice admits the
same column set. The rewriter is a closure operator on schemas.

**Theorem 6 (`rewrite_monotone`).** If $P \subseteq P'$ (multiset
inclusion on allowed columns), then the output schema under $P$ is
contained in that under $P'$ — strengthening the policy can only
widen the output.

**Theorem 7 (`rewrite_touched`).** `q'.touched = q.touched`.
*Touched relation is preserved.*

**Theorem 8 (`rewrite_refuses_unknown`).** `cat q.touched = []`
implies `rewrite ... = none`. **An unknown relation is never a
silently empty schema** — explicit refusal protects against
catalog drift attacks.

**Theorem 9 (`rewrite_refuses_forbidden_filter`).** If
`c ∈ q.filterCols` and `c ∉ allow`, then `rewrite ... = none`.
Companion to Theorem 2.

`CheckAxioms.lean` reports per-theorem axiom dependencies. The set
is bounded by `{propext, Quot.sound}` — Lean 4's built-in
foundational axioms; two theorems (`rewrite_touched`,
`rewrite_refuses_unknown`) depend on *no* axioms. There is no
`sorry`, no user-supplied `axiom`.

# Implementation and conformance testing

The Rust prototype (`prototype/crates/postern-core`) mirrors the
Lean types and `rewrite` literally. The conformance harness
(`postern-diff`) reads a JSON corpus from `lake exe postern-corpus`
and asserts:

1. Outcome kind (`accept` / `refuse`) matches.
2. On accept: rewritten plan equals Lean's reference structurally;
   so do `schema(cat)`, `filter_cols`, and `touched`.
3. The input plan's `filter_cols` matches Lean's `Plan.filterCols`
   (sanity-checks the IR helper independent of the rewriter).

We chose JSON-corpus conformance over Lean → Rust extraction
because the corpus interface is stable across compiler churn and
surfaces divergence as a CI signal, not a build break.

**Corpus shape.** 18 cases: 7 behavioural (the §5 demo), 4
refusal regressions for known attacks, 7 policy-language edge
cases (empty policy, duplicate grants, catalog-absent columns,
case sensitivity, trailing-whitespace principal, nonexistent
project column, nested Project narrowing). All 18 pass.

# Demo: a financial institution with three departments

Kaggle `transactions-fraud-datasets`. Policy in
`scenarios/financial-institution/policy.postern`; the load-bearing
rows:

| principal   | plan                                | outcome             | rewritten schema                       |
| ----------- | ----------------------------------- | ------------------- | -------------------------------------- |
| `CRM`       | `Scan users_data`                   | accept              | `id, name, region, age`                |
| `CRM`       | `Project [ssn,email]` over above    | accept              | `∅` (over-projection collapses)        |
| `CRM`       | `Filter on ssn`                     | **refuse**          | —                                      |
| `CardOps`   | `Scan users_data` (cross-dept)      | accept              | `∅` (no matching grant)                |
| `FraudRisk` | `Scan users_data`                   | accept              | `id, region` (minimum-necessary)       |
| `Marketing` | `Scan users_data` (unknown prin.)   | accept              | `∅` (empty allow)                      |
| `CRM`       | `Scan credit_bureau_imports`        | **refuse**          | — (unknown relation)                   |

Each row is a corpus case; "refuse" rows exercise Theorems 8 / 9.

# Related work

No prior system, to our knowledge, proves soundness of a
plan-level rewriter for an LLM-agent-facing lakehouse. The closest
landmarks:

- **Cedar** [@cedar2024] proves authorization-decision soundness
  for per-call API authorization, also in Lean. The axis is
  different: Cedar verifies "may this principal call read?",
  Postern verifies "is the dataframe the executor sees contained
  in what the policy permits?".
- **SEAL** [@seal2023] gives capability-based enforcement at
  runtime; the policy core itself is unverified. Postern is the
  inverse — verified policy core, lighter runtime — and pairs with
  biscuit [@biscuit] for capability distribution.
- **Jeeves / Jacqueline** [@jeeves2012; @jacqueline2016] and the
  faceted-execution line [@faceted-haskell] enforce IFC in ORM-
  backed apps via a heavyweight faceted-value runtime. They
  predate the LLM-agent threat model and ship no Lean artifact.
- **Postgres RLS** [@rls-postgres] and **OPA / Rego** [@opa-rego]
  are the deployed baselines. RLS is per-database with no formal
  guarantee beyond `EXPLAIN`; OPA is general-purpose but does not
  reason about query outputs.
- **AgentDojo** [@agentdojo2024] and **CaMeL** [@camel2025] argue
  for capability-flow defences against indirect prompt injection
  at the *agent* layer. Postern is the complementary lake-side
  enforcement point.
- **Capture-checking for agent capabilities**
  [@capabilities-agents-2026]. Odersky et al. propose Scala 3
  capture-checking as a type-level "tactic" that makes capabilities
  first-class program variables, so agent-emitted code cannot
  exfiltrate data it doesn't hold a capability for. Stack-
  complementary to Postern: their work bounds the agent's code,
  ours bounds the plan at the gateway. The two layers compose
  without re-verifying each other's TCB.

# Open challenges and future work

The Lean spec is narrow on purpose. Three load-bearing extensions
remain.

1. **Joins under proof.** The IR is single-relation; the Rust impl
   handles joins by per-leg rewriting but is not under proof. The
   natural next theorem is
   `rewrite_sound_join`: for `Join(q₁, q₂)`, the rewritten output
   columns are contained in the union of per-leg allowed sets. The
   hard case is the join-key leak — joining on `ssn` without
   projecting it mirrors the filter side-channel and needs the
   same join-key-coverage condition.

2. **Aggregation, with a differential-privacy boundary.** A
   principal may be allowed `SUM(amount)` without individual-row
   visibility. Lifting the rewriter to aggregations is open; SEAL
   and the faceted line [@seal2023; @faceted-haskell] are the
   closest reference points.

3. **Biscuit attenuation inside the proof.** The current Lean
   spec sees a flat `principal : String`. Modelling biscuit's
   Datalog-based attenuation, expiry, and audience checks inside
   the proof lifts the principal-string-extraction row out of the
   TCB. Catalog integrity, plan integrity in transit, and NL →
   policy synthesis are further out but the same shape.

# Reproducibility

```
verifier/lean/   Lean 4 spec + theorems + corpus emitter
prototype/       Rust workspace: postern-core, postern-diff
scenarios/       Financial-institution case study
paper/           This document
scripts/         reproduce.sh — chains everything
```

Toolchains: **Lean 4.29.1** (pinned in `verifier/lean/lean-toolchain`),
**Rust stable** (tested 1.93). Single command:

```sh
scripts/reproduce.sh
```

Expected output ends with
`18/18 cases pass (Lean reference == Rust impl)` and an axiom
audit showing only `propext` and `Quot.sound`. Runs in under
two minutes on an M-series Mac on a warm cache.

# References

::: {#refs}
:::
