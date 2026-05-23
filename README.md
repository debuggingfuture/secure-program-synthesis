# VAPOR — Verified Access Policy Over Retrieval

> *Working title for a research artifact. Pairs a Lean4-verified policy core
> with a prototype dataframe gateway that mediates LLM-agent access to
> heterogeneous SaaS data (Slack, PostHog, RDS, Cloudflare D1).*

VAPOR is a research artifact exploring **formally verified access control
for agentic context systems**. Today, agents pull context from a sprawl of
SaaS sources through ETL pipelines and "memory" services (mem0, Notion AI,
Airbyte sinks, RAG indexes). Once data lands in a centralized lake, the
per-SaaS RBAC that protected it dissolves — every agent that can read the
lake can, in practice, read everything.

VAPOR proposes a single, decoupled policy layer placed at the **dataframe
gateway**: every agent query (SQL, dataframe op, retrieval call) and every
ingestion job is mediated by a policy decision module whose semantics are
machine-checked in Lean 4. The same policy artifact serves the ingest path
(field-level scrubbing, aggregation enforcement) and the egress path
(row-level filters, column projection, query rewriting).

## Why this artifact

| Existing approach | Gap VAPOR addresses |
|---|---|
| Per-SaaS RBAC | Doesn't survive ETL into the lake. |
| Postgres RLS | Policy is coupled to the table; hard to author, no semantics across sources; nothing aggregates ingest + egress. |
| Cedar (AWS) | Verified policy language, but scoped to "authorize an API call" — not "rewrite a dataframe query so the result respects the policy." |
| SEAL (SACMAT'23) | Capability-based, runs computation in a sandbox under owner-defined policy — orthogonal: VAPOR is the formal layer that proves the *policy* sound. |
| Jacqueline / Jeeves | Policy-agnostic IFC for DB-backed apps — predates LLM agents, no formal Lean artifact, framework-coupled. |
| Object-capability SQL sandbox for LLM agents | Conceptually adjacent (capabilities baked into tool surface) but unverified; SQL-only. |

VAPOR's bet: a **small, Cedar-shaped policy DSL with Lean4 semantics**, a
**verified query rewriter** that emits Substrait/Ibis plans, and a
**dataframe-native enforcement gateway** is the minimal artifact that lets
us *prove* an agent query never returns data outside its grants — across
heterogeneous sources, without re-implementing each source's ACL story.

## Repo layout

```
paper/         Paper draft (Pandoc markdown → LaTeX for camera-ready)
verifier/lean/ Lean 4 formalization: policy AST, semantics, rewriter, theorems
prototype/     Python prototype: Ibis-based gateway, source connectors,
               policy decision module (Lean → exported decision oracle)
scenarios/     Reproducible motivating scenarios (engineer vs finance, etc.)
docs/          Design notes, ADRs
```

## Status

Pre-publication research artifact. Not production software. The paper, Lean
proofs, and prototype are co-evolving — see `paper/outline.md` for the
intended thesis and contribution structure, and `paper/related-work.md` for
the prior-art map.

## License

TBD (likely Apache-2.0 for code, CC-BY for paper).
