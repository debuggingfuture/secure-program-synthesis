# Threat model

Single source of truth for what VAPOR defends against. The paper §3
condenses this.

## Assets

1. **Source-system rows** — Slack messages, PostHog events, RDS tables,
   D1 rows. After ingest, these live in the lake's Bronze/Silver/Gold
   tiers.
2. **Agent-memory records** — embeddings + KG nodes + KV blobs in
   mem0-style stores derived from (1).
3. **Aggregate outputs** — GROUP BY results, dashboards, retrieval
   ranks. Aggregates carry inference risk (re-identification,
   membership inference) beyond raw rows.
4. **Policy artifact itself** — the `Vapor.Spec` policy is in the
   TCB; tampering with it defeats VAPOR.

## Adversaries

| Adversary | Capability | Trust | In-scope? |
|---|---|---|---|
| Prompt-injected agent | issues any tool call permitted by its tool surface | untrusted | **yes** |
| Indirect-injection payload | crafts strings landing in source data | untrusted | **yes** |
| Malicious source-system user | seeds adversarial content (e.g. Slack message with PII) | untrusted | **yes** |
| Compromised ingest connector | mislabels data during ETL | trusted | **out (future work — verified connectors)** |
| Compromised gateway process | runs arbitrary code in TCB | trusted | **out (TCB)** |
| Network adversary | observes encrypted traffic | untrusted | **out (orthogonal — TLS layer)** |
| Side-channel adversary | timing / cache / page-fault on the gateway | trusted process under adversarial input | **out (not modeled)** |
| Policy author with mistake | writes overly-permissive policy | trusted intent, untrusted output | **in (mitigated by `Vapor.Analyze`)** |

## Defended attacks

1. **Cross-source aggregation leak** (Scenario 1). Engineer agent
   joining permitted Slack data with denied finance data — rejected by
   `Rewriter.sound`.
2. **Column-level PII leak** (Scenario 2). Support agent reading raw
   `email` — projected through `mask sha256` by the rewriter.
3. **Row-level overreach** (Scenario 2). Support agent reading other
   customers' rows — rewriter injects `WHERE customer_id = ctx.customer_id`.
4. **Raw-row exfil under aggregate role** (Scenario 3). Exec agent
   issuing non-aggregate query — rejected.
5. **Cross-tenant embedding leak** (Scenario 4). Vector retriever
   returning chunks from unauthorized channels — rewriter forces
   metadata filter into the ANN call.
6. **Indirect prompt injection that ends in (1)–(5)**. The injection
   succeeds at the LLM level (agent issues the bad query); the
   gateway is the second line of defense.

## Not defended

- **Free-text exfiltration after access.** An agent that reads allowed
  rows can still leak them via tool output, screenshot, etc. VAPOR
  enforces access, not post-access. Pair with output filters.
- **Aggregation-inference attacks** beyond the `k`-min-group-size
  predicates the policy explicitly models. Wiring DP is future work.
- **DoS via crafted query plans.** The rewriter is policy-decidable in
  time linear-ish in the policy, but a complex plan can still be
  expensive. Out of scope; pair with query-cost limits.
- **Supply chain on the policy artifact / Lean kernel.** Standard
  software-supply-chain hygiene applies.
- **Side channels.** Not modeled.

## TCB

The trusted computing base is exactly:

1. The Lean-extracted decision oracle (or the Python mirror once
   validated by differential testing).
2. The plan rewriter (Lean-proved sound for the strategies we
   implement).
3. The gateway process that intercepts agent tool calls.
4. The policy artifact (authored by humans, statically analyzed by
   `Vapor.Analyze`).

Source systems, agents, and the underlying query engine are **not**
in the TCB.
