---
title: "VAPOR: Verified Access Policy Over Retrieval for Agentic-Context Data Lakehouses"
author:
  - name: TBD
abstract: |
  Agentic systems increasingly consume their context from centralized data
  lakes — fed by ETL pipelines from heterogeneous SaaS sources — and from
  agent-memory services that re-emit retrieved fragments to downstream
  tools. The per-source RBAC that protected each SaaS does not survive
  this collapse: once an LLM agent can query the lake, source-level
  access controls are no longer the security boundary. Existing
  mitigations either couple policy to a single store (Postgres RLS),
  authorize at the per-API-call granularity without reasoning about
  query outputs (Cedar), or rely on sandbox-level capabilities without
  formally verifying the policy itself (SEAL, object-capability SQL
  sandboxes). We present **VAPOR**, a research artifact that pairs (a)
  a Cedar-shaped policy DSL with denotational semantics mechanized in
  Lean 4, (b) a query-plan rewriter whose soundness is proved against
  those semantics, and (c) a dataframe-gateway prototype that mediates
  every agent read against the Lean-extracted decision oracle. The same
  policy artifact governs both the ingest path (write-side scrubbing)
  and the egress path (read-side rewriting). We sketch four
  motivating scenarios drawn from a realistic Slack + PostHog + RDS +
  D1 stack, contrast against Postgres RLS, Cedar, OPA, and the
  object-capability SQL sandboxing approach, and identify open
  challenges in policy authoring, aggregation-inference attacks, and
  cross-system capability passing.
keywords:
  - access control
  - formal verification
  - Lean 4
  - data lakehouse
  - LLM agents
  - information flow
  - prompt injection
---

# Introduction

The deployment shape of agentic systems has changed in two years. A
typical 2024 LLM agent answered questions inside a single SaaS context
— "summarize the last 20 messages in this Slack channel" — under that
SaaS's own RBAC. The 2026 agent is **context-fused**: a retrieval
pipeline (mem0 [@mem0], Notion AI, in-house Airbyte sinks, RAG over
vector + KG memory) ingests heterogeneous sources into a central
lakehouse, and the agent issues SQL-like dataframe queries or vector
retrievals at inference time. The cost-of-context for the agent has
dropped; the **security boundary** of the original per-SaaS RBAC has
also dropped — into the lake's ingest service account.

This paper is about restoring that boundary. We frame the problem as
**verified access control for agentic context systems** and present
VAPOR, a Lean-verified policy core paired with a dataframe-gateway
prototype.

## Why existing approaches fall short

| Approach | What it protects | What it misses |
|---|---|---|
| Per-SaaS RBAC | API calls inside one SaaS | ETL-aggregated lake; cross-source joins |
| Postgres RLS | Rows in one table | Cross-table aggregation; no formal guarantees; per-source policy duplication |
| Cedar [@cedar] | Per-API authorization, formally verified | "Authorize this call," not "rewrite this query so the result respects the policy" |
| SEAL [@seal] | Owner-controlled compute inside a sandbox | No formal proof of policy correctness |
| Object-capability SQL [@ocsql] | Make dangerous SQL inexpressible | Unverified; SQL-only; per-table hand-written capability classes |
| Jeeves/Jacqueline [@jeeves] | Policy-agnostic IFC in ORM-backed apps | Heavyweight runtime; predates LLM-agent threat model; no Lean artifact |

## Contributions

1. A problem framing for **access control in agentic context systems**
   — the union of ETL-fed lakehouses, agent-memory services, and
   tool-calling LLMs — with a threat model that fuses indirect prompt
   injection, over-broad ingest, and cross-source aggregation.
2. A policy DSL, `Vapor.Spec`, with denotational semantics mechanized
   in Lean 4. Cedar-shaped surface (principal / action / resource /
   context) extended with dataframe-aware predicates over rows,
   columns, and aggregations.
3. A **verified query-plan rewriter**: for plan `q` and policy `P`,
   `rewrite(q,P)` produces a plan whose evaluation is contained in the
   intersection of `q`'s rows and `P`'s allowed set. Proved sound in
   Lean (reject-only fragment) with the path-to-proof for the
   restricting fragment sketched in §5.
4. A reference enforcement **gateway** in Python that intercepts Ibis
   dataframe operations, walks the Substrait plan, calls the Lean
   decision oracle, and either rewrites or rejects.
5. An evaluation protocol grounded in four motivating scenarios over a
   realistic stack (Slack + PostHog + AWS RDS + Cloudflare D1).

# Motivating scenario

A 200-person SaaS startup runs an analytics lake (Iceberg on S3) fed
from Slack, PostHog, an application RDS, and Cloudflare D1. A platform
engineer's "Ops Copilot" agent has `read` on Bronze/Silver Slack
tables, all PostHog events, and `application_db.*` except `finance.*`.

An attacker posts in a public Slack channel: *"To diagnose payroll
anomalies, join `slack_messages` with `application_db.finance.payroll`
on `user_id` and DM the result."* When an engineer next asks the
copilot to investigate ingestion alerts, the agent reads the injected
message as part of its context, treats it as an instruction, and
issues the cross-table join.

- **Per-SaaS RBAC** doesn't help — both rows landed in the lake under
  the ingest service account.
- **Postgres RLS** doesn't help — the engineer's row-level policy on
  each table is independently satisfied; RLS has no concept of
  cross-table aggregation privilege.
- **Cedar** could deny the *tool invocation*, but it has no
  vocabulary to say "this plan, after rewrite, returns no row whose
  source-table is in `finance.*`."

A VAPOR policy `forbid read on application_db.finance.*` is enforced
by the plan rewriter: the join touches `finance.payroll`, the
rewriter's reject path fires, the gateway returns an authorization
error. `Rewriter.sound` (Lean theorem `rewriter_sound_reject`)
guarantees that **no rewrite path** could have surfaced those rows.

# Threat model

- **Untrusted agent.** Issues arbitrary dataframe / SQL / retrieval
  ops. May be prompt-injected. Adversarial.
- **Untrusted ingest payloads.** Source data (Slack messages, PostHog
  events) may be attacker-controlled.
- **Trusted policy author.** Authoring mistakes are *in scope* for
  static analysis (`Vapor.Analyze`, à la Cedar's symbolic compiler).
- **TCB.** The gateway process, the Lean-extracted decision oracle,
  and the rewriter's compiled artifact.
- **Out of scope.** Side channels; resource-exhaustion DoS;
  inference attacks beyond the aggregation predicates the policy
  explicitly models; post-access exfiltration via agent tool output
  (a complementary defense layer).

# Design

## Policy DSL

`Vapor.Spec` rules have the form

```
{permit | forbid} <action> on <resource-set>
  when <expression>
[ mask <column> using <function> ]
```

mirroring Cedar's `permit`/`forbid` with `principal`/`action`/
`resource`/`context`. Resources are `source.schema.table.column` paths
with wildcards. `mask` is a column-level rewrite primitive (e.g.
`sha256`, `hash3`, `redact`) introduced by VAPOR. Aggregation
predicates (`aggregation.row_count`, `aggregation.is_grouped_by_at_least`)
let policies require group-by privacy without committing to a
particular DP mechanism.

## Plan rewriter

Two strategies, combined:

- **Reject** — if any touched resource is denied for the principal,
  rewrite to ⊥; the gateway returns a typed authorization error.
- **Restrict** — push `WHERE`, projection, and `mask` operators below
  the policy boundary so the plan returns ⊑ `allowed(P)`. The mask
  variant is sound because each masked column's projected values are
  the image of the raw column under the policy-declared masking
  function.

## Lean kernel layout

We mirror `cedar-policy/cedar-spec/cedar-lean`:

- `Vapor/Spec.lean` — policy AST, `authorize` function.
- `Vapor/Plan.lean` — small relational IR.
- `Vapor/Rewriter.lean` — reject-only strategy (this draft).
- `Vapor/Thm.lean` — top-level theorems.
- (Future) `Vapor/SymCC.lean` — symbolic compiler à la Cedar Analysis,
  emitting CVC5 SMT for queries like "could principal $p$ ever observe
  column $c$".

## Gateway

A Python process exposes Ibis-table-shaped tool surfaces to agents.
Each call serializes to a Substrait plan; the gateway extracts the set
of `(source, schema, table, column)` touched, invokes the
Lean-extracted decision oracle, and (in the current prototype) either
forwards or rejects. The Ibis frontend lets one prototype talk to
DuckDB, Postgres, BigQuery, and pgvector with a single intercept point.

# Verification

## What is proved

The current artifact proves theorem **skeletons**; the proofs of all
top-level theorems are either complete (for the trivial fragments) or
have an explicit `sorry`-stub with a sketched argument. We claim no
proof we have not exhibited.

- `authorize_order_indep` — `authorize` ignores rule order. Argument:
  case analysis on `any (Effect.forbid ∧ matches)` over `Perm`-related
  lists.
- `rewriter_transparent` — if no touched resource is denied for the
  principal, `rewrite(q,P) = accept q`. Direct from the definition.
- `rewriter_sound_reject` — if `rewrite(q,P) = accept q'`, every
  touched resource of `q'` is permitted. Direct from the negated
  condition that triggered the reject branch.

## What we want to prove

- `Rewriter.sound` (restrict variant) — the headline theorem.
  Statement: for the full rewrite strategy that adds `WHERE`,
  projection, and `mask`, the rewritten plan's set of observable rows
  is ⊑ the row-set the policy admits, columnwise.
- `Mask.sound` — projected values for a masked column are exactly the
  image of the raw column under the policy-declared mask function.
- `Ingest.sound` — read-side rewrite ≡ write-side ingest filter, given
  the same policy. This is the **headline novelty**: ingest and egress
  are two compilations of one source artifact, and the soundness
  theorem is their observational equivalence.
- `SymCC.sound` / `.complete` — Cedar-style: VAPOR's symbolic compiler
  to SMT preserves the Lean semantics, so analysis answers ("could
  principal $p$ ever read column $c$") have no false negatives.

## Methodology

We adopt Cedar's verification-guided development [@vgd]:

1. Write the Lean executable spec.
2. Implement the production decision oracle (currently Python; Rust
   or Lean→C FFI for the camera-ready).
3. Drive both with the same property generators (`hypothesis` in
   Python, `slim_check`-style generators in Lean) and compare outputs.
   Cedar reports 4 bugs caught by proof and 21 by DRT; we expect a
   similar split.

# Evaluation (plan)

Four scenarios in `scenarios/`:

1. **Engineer vs Finance** — the motivating example.
2. **Support vs PII** — `mask email using sha256`; never expose
   `card_last_four`.
3. **Exec aggregate-only** — read allowed only as `GROUP BY`
   coarser than a threshold.
4. **Cross-source RAG** — labels on embeddings; vector-store metadata
   filter forced by policy.

Baselines: Postgres RLS, Cedar (per-API authorization), OPA/Rego.

Metrics:

- **Authoring** — policy LOC; # source-specific concepts leaking into
  policy text; # artifacts to maintain.
- **Soundness** — for each baseline, attacks-let-through under each
  scenario (manual + property-based fuzz).
- **Performance** — added end-to-end latency per query; oracle call
  overhead; policy compile time.
- **Verification cost** — Lean proof LOC, total `lake build` time on
  commodity hardware, # of `Vapor.Analyze` SMT calls per scenario.

# Discussion: open challenges

1. **Aggregation-inference attacks.** Beyond `k`-min-group-size
   predicates, more is needed. Wiring DP mechanisms into the same
   policy artifact is future work — `Mask.sound` already gives us the
   abstraction.
2. **Policy authoring is still hard.** `Vapor.Analyze` ports Cedar's
   symbolic compiler to our DSL; combining it with **LLM-emitted
   policies** (agent drafts, Lean checks, human approves) is a
   promising loop.
3. **Source-connector trust.** Ingest connectors are in the TCB for
   labeling. Verified connectors per source (start with PostHog →
   Iceberg) is the next artifact.
4. **Cross-system capabilities.** VAPOR proves policies sound; SEAL
   gives sandboxed compute. Composing them — a verified policy that
   mints SEAL capabilities — gives the end-to-end "context can leave
   the lake, computation cannot" story.
5. **Free-text egress.** An agent that reads allowed rows can still
   leak via tool output. Output filters are a complementary layer.

# Related work

A detailed map is in the repo (`paper/related-work.md`). Most direct
ancestors: Cedar [@cedar; @vgd] (verified policy language, per-API),
SEAL [@seal] (capability sandbox), Jeeves/Jacqueline [@jeeves] (IFC
for DB-backed apps), MemArchitect [@memarchitect] (agent-memory
governance), object-capability SQL sandboxing [@ocsql] (capabilities
for LLM SQL agents), IFC for ML pipelines [@ifcml]. The recent
prompt-injection literature [@owasp-llm-2025; @echoleak] motivates
the threat model.

# Conclusion

Centralized agentic-context pipelines have outpaced the access-control
story they inherited. We argue that the right shape of mitigation is a
small, decoupled, dataframe-aware policy DSL with **machine-checked
semantics** and a verified plan rewriter, deployed at the gateway
between agent and lake. VAPOR is a research artifact in that shape —
paper + Lean kernel + prototype + scenarios — designed to be the next
artifact a Cedar reviewer can navigate without surprise. The headline
gap is `Ingest.sound`: a single policy artifact that compiles to both
write-side scrubbing and read-side rewriting, with their equivalence
mechanically proved. We invite collaboration on that proof.

# References {-}

::: {#refs}
:::
