---
title: "Postern: a Lean-verified access gateway for agentic data lakehouses"
subtitle: "Secure Program Synthesis Hackathon 2026 — Track 3 research artifact"
author:
  - name: FractalBox
abstract: |
  Agentic systems increasingly read their context out of a single
  lakehouse — DuckDB over Parquet on S3, fed by Airbyte / mem0-style
  retrieval pipelines — and the per-source RBAC that protected each
  upstream SaaS no longer holds at the lake boundary. We present
  **Postern**, a research artifact that pairs (a) a small policy DSL
  and dataframe-plan IR mechanized in **Lean 4** with a
  fully-proved soundness theorem (no `sorry`, only Lean's built-in
  axioms), (b) a Rust prototype mirroring the same `rewrite`
  algorithm, and (c) a **differential test harness** that pipes a
  Lean-emitted JSON corpus into the Rust rewriter and asserts
  byte-equality of the rewritten plans. The artifact closes the gap
  between Cedar-style verified policy authoring and capability-based
  data sandboxes by verifying the *rewriter*, not just per-call
  authorization. We use a financial-institution scenario (Kaggle
  transactions dataset, three departments) to make the threat model
  concrete and identify open challenges around joins, filter
  side-channels, and aggregation inference.
keywords:
  - access control
  - formal verification
  - Lean 4
  - data lakehouse
  - LLM agents
  - differential testing
---

# Introduction

Two shifts in production agentic systems motivate this work. **First**,
context for an LLM agent is no longer drawn from a single SaaS API
guarded by that SaaS's own RBAC; it is drawn from a centralized
lakehouse (typically DuckDB over Parquet on S3 [@duckdb]) populated by
Airbyte-style ETL and by long-term memory services [@mem0]. **Second**,
agents are increasingly the entity *issuing* the SQL/dataframe query
— through MCP tools [@mcp2024] — rather than receiving rows
hand-picked by a human analyst. The cost of asking a question has
dropped; so has the security boundary that used to protect each
source.

This paper is about *restoring* that boundary by inserting a verified
gateway between agents and the lake. The gateway holds a single
policy artifact and **rewrites** every plan it sees so the result is
contained in what the policy permits. We treat the gateway as the
trusted base; everything beyond it (LLM, agent-generated code) is
untrusted.

## Contributions

1. A narrow, fully-mechanized core in **Lean 4** [@lean4]:
   a Plan IR (`Scan`/`Project`/`Filter`), a column-grant policy
   language, and a `rewrite` algorithm whose **column-soundness**
   theorem — "every column in the rewritten plan's output schema is
   allowed by the policy" — is proved with no `sorry`, depending only
   on Lean's standard axioms `propext` and `Quot.sound`.

2. A **Rust prototype** that mirrors the Lean types and rewriter and
   targets a DuckDB + Polars [@polars] dataframe gateway. Capability
   authentication is via biscuit tokens [@biscuit].

3. A **differential test harness**: the Lean side emits a JSON corpus
   of `(catalog, policy, principal, plan)` inputs paired with the
   reference rewritten plan; the Rust harness re-runs `rewrite` over
   each input and asserts byte-equal output. 10/10 cases pass on the
   demo corpus; any future divergence between the Lean spec and the
   Rust implementation surfaces as a CI failure.

4. A **financial-institution case study** (Kaggle
   `transactions-fraud-datasets`) with three principals
   (CRM, CardOps, FraudRisk) that exercises PII redaction,
   cross-department refusal, and minimum-necessary disclosure.

# Threat model

We assume a trusted gateway process holding the policy artifact and
the cryptographic root for capability tokens. Everything else is
untrusted:

| Component                               | Trust | Why                                                                       |
| --------------------------------------- | :---: | ------------------------------------------------------------------------- |
| LLM / agent (planner)                   |   ✗   | Can be jailbroken; may emit hostile SQL / dataframe ops.                  |
| Tool-generated code (executors)         |   ✗   | Indirect injection from retrieved context; supply chain.                  |
| Capability tokens (biscuit) [@biscuit]  |   ~   | Trusted only insofar as the gateway verifies the signature.               |
| Gateway process (Postern)               |   ✓   | TCB. Holds the Lean-verified rewriter and the policy.                     |
| DuckDB + Parquet store                  |   ✓   | TCB. Assumed to honour the rewritten plan literally.                      |
| Lake operators / DBAs                   |   ✓   | Out of scope — same as for any RDBMS-RLS [@rls-postgres] deployment.      |

In-scope attacks: prompt-injected agents requesting forbidden columns;
agent-generated dataframe ops that over-project; cross-department
queries by mis-scoped capability tokens; unknown principals.

Out of scope for this draft: filter side-channels (a `WHERE` clause
that references a forbidden column to *infer* its values without
projecting it); aggregation/inference attacks; covert channels
through query latency.

# Design

Postern compiles a single policy artifact to plan-level enforcement.

```
       MCP / dataframe op                 plan (typed IR)
agent ─────────────────────► gateway ───────────────────────► rewriter
                                  │                              │
                                  ▼                              ▼
                          biscuit verifier              Lean-extracted spec
                                  │                              │
                                  └────────► policy ◄────────────┘
                                                  │
                                                  ▼
                                         DuckDB + Polars execution
```

## Policy

A policy is a list of **column-grants** $\langle p, r, C \rangle$ —
"principal $p$ may read columns $C$ on relation $r$". Multiple grants
for the same $(p, r)$ are flat-unioned. Anything outside the union is
denied — fail-closed.

This is a deliberate narrowing of Cedar [@cedar2024]: column-level,
not row-level; declarative, not predicate-rich. It buys us a small
proof obligation. Row-level filtering is layered on top of the
rewriter in the prototype but is not yet under proof
(see §6).

## Plan IR

```
Plan ::= Scan(rel)
       | Project(plan, cols)
       | Filter(plan, col)
```

The IR is single-relation by design: every operator preserves the
touched relation, which lets the soundness proof reduce to a
membership argument. Joins exist in the Rust impl as compositions of
single-relation legs.

## Rewriter

`rewrite cat P prin q` wraps `q` in a `Project` whose column list is
the intersection of `q.schema cat` and `P.allowed prin q.touched`.
Post-hoc projection is the simplest algorithm that admits a clean
soundness proof; more aggressive predicate-pushdown rewriters can be
proved sound against this one as an oracle.

# Formal model

Mechanized in `verifier/lean/Postern.lean`. The three theorems are
listed below; all are checked by `lake build` and the axiom set is
audited by `CheckAxioms.lean`.

**Theorem 1 (`rewrite_touched`).** For every `cat, P, prin, q`:
`(rewrite cat P prin q).touched = q.touched`.

**Theorem 2 (`rewrite_schema_subset`).** For every `cat, P, prin, q`
and column `c`: if `c ∈ (rewrite cat P prin q).schema cat` then
`c ∈ q.schema cat`. The rewriter can only remove columns, never
fabricate them.

**Theorem 3 (`rewrite_sound`, headline).** For every `cat, P, prin, q`
and column `c`: if `c ∈ (rewrite cat P prin q).schema cat` then
`c ∈ P.allowed prin q.touched`. Every column visible at the gateway
boundary is one the policy permits.

`CheckAxioms.lean` reports the axiom dependencies:

```
'Postern.rewrite_touched'        does not depend on any axioms
'Postern.rewrite_schema_subset'  depends on [propext, Quot.sound]
'Postern.rewrite_sound'          depends on [propext, Quot.sound]
```

— i.e., only Lean 4's built-in axioms, no `sorry` and no
user-supplied `axiom` declarations.

# Implementation and differential testing

The Rust prototype (`prototype/crates/postern-core`) mirrors the Lean
types and `rewrite` function literally. The differential harness
(`postern-diff`) reads a JSON corpus emitted by `lake exe
postern-corpus`, runs `postern_core::rewrite` on each
`(catalog, policy, principal, plan)`, and asserts three equalities:

1. Rust output plan == Lean reference plan (structural).
2. Output schema (Rust) == Lean reference schema.
3. Touched relation (Rust) == Lean reference touched.

Current corpus is 10 cases (financial-institution scenario, §5);
all 10 pass. Adding a case is a two-line edit in `Main.lean`; the
Rust side requires no change because the same algorithm runs against
the same JSON.

This is a weak form of code-extracted certified executable, picked
deliberately over Lean→C/Rust extraction: a JSON corpus is the
smallest interface that survives Lean and Rust release churn and is
trivial to diff in CI.

# Demo: a financial institution with three departments

Three principals (`CRM`, `CardOps`, `FraudRisk`) over the Kaggle
`computingvictor/transactions-fraud-datasets` schema. Full policy and
expected behaviour are in `scenarios/financial-institution/README.md`;
here are the load-bearing rows:

| principal   | plan                                | rewritten output schema             |
| ----------- | ----------------------------------- | ----------------------------------- |
| `CRM`       | `Scan users_data`                   | `id, name, region, age`             |
| `CRM`       | `Project [ssn, email]` over the above | `∅` (forbidden columns dropped)   |
| `CardOps`   | `Scan users_data` (cross-dept)      | `∅`                                 |
| `FraudRisk` | `Scan users_data`                   | `id, region`                        |
| `Marketing` | `Scan users_data` (unknown principal) | `∅`                               |

Each row is an entry in the differential corpus.

# Related work

**Cedar** [@cedar2024] proves authorization-decision soundness for
per-call API authorization, also in Lean. Postern targets *query
rewriting* rather than decision functions: the policy survives into
the executed plan, not just into a yes/no on a request. We borrow
Cedar's stance on a small denotational core but specialize the
surface to column grants.

**SEAL** [@seal2023] gives capability-based control over analytic
workloads with an enforcement runtime; the policy core itself is
unverified. Postern flips the balance — verified policy core, lighter
runtime — and pairs it with biscuit [@biscuit] for the capability
distribution layer.

**Jeeves / Jacqueline** [@jeeves2012; @jacqueline2016] enforce IFC in
ORM-backed apps via a faceted-value runtime; they predate the
LLM-agent threat model and have no Lean artifact.

**Postgres RLS** [@rls-postgres] and **OPA / Rego** [@opa-rego] are
the deployed baselines. RLS is per-database and lacks formal
guarantees beyond `EXPLAIN`; OPA is general-purpose but does not
reason about query outputs. Postern's contribution is a *verified*
plan-level rewriter for the lakehouse setting.

**Object-capability SQL** [@ocsql2023] makes dangerous queries
inexpressible by construction; we view it as a complementary
defence-in-depth layer rather than a replacement.

# Open challenges and future work

1. **Joins under proof.** The Lean spec is single-relation; the Rust
   impl supports joins by per-leg rewriting but does not prove
   schema-soundness across them. The natural next theorem is
   `rewrite_sound_join`: for `q = Join(q₁, q₂)`, every column of the
   rewritten join belongs to one of the per-leg allowed sets.

2. **Filter side-channels.** `Filter(p, col)` does not include `col`
   in the output schema, but the *predicate* still reads it. A
   principal who cannot read `ssn` can still ask
   "rows where `ssn = 'X'`" and observe row counts. We currently
   leave this open; one mitigation is to require predicate columns to
   appear in the allowed set, which we believe is straightforwardly
   provable.

3. **Aggregation and differential privacy.** A principal may be
   allowed `SUM(amount)` but not individual rows. Lifting the
   rewriter to aggregations is open; SEAL and IFC-for-ML
   [@seal2023; @ifc-ml] are the closest reference points.

4. **Policy synthesis from natural language.** The MCP frontend lets
   agents propose policy edits in natural language; the Lean spec
   then synthesises the policy artifact and verifies preservation
   against an existing access log. This is genuinely
   secure-program-synthesis territory and the natural follow-up
   project.

5. **Cross-system capability passing.** Biscuit tokens can chain
   attenuations, but the Lean spec currently sees a flat principal
   string. Modelling attenuated capabilities inside the proof is open
   and lines up with the SEAL line of work [@seal2023].

# Reproducibility

```
verifier/lean/   # Lean 4 spec + theorems + corpus emitter
prototype/       # Rust workspace: postern-core, postern-diff
scenarios/       # Financial-institution case study
paper/           # This document
```

Build:

```sh
cd verifier/lean && lake build && lake exe postern-corpus \
  > ../../prototype/corpus/postern-corpus.json
cd ../../prototype && cargo test --workspace \
  && cargo run -p postern-diff -- corpus/postern-corpus.json
```

Expected output: `10/10 cases pass (Lean reference == Rust impl)`.

# References

::: {#refs}
:::
