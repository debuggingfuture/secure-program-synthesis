# Scenario 05 — MNPI / Chinese wall

## Setting

The Investment Banking team is advising Acquirer Corp (ticker `ACQ`)
on the acquisition of Target Inc (ticker `TGT`). Drafts, term sheets,
and the deal team roster live in `deals.mna_pipeline`. Announcement is
planned for 2026-06-15.

A trader on the Equities desk uses the "Trader Copilot" for intraday
research:

> *"Anything interesting in TGT or ACQ today? Vol seems off."*

## What must not happen

The agent must not surface:

- Existence of an in-flight deal between ACQ and TGT.
- Any field from `deals.mna_pipeline` where `mnpi_ticker ∈ {ACQ, TGT}`
  and `mnpi_until > now()`.
- Embedding-retrieved chunks from M&A-team Slack channels.
- Aggregates whose contributing rows include the above.

These constraints hold even if the trader explicitly types
`SELECT * FROM deals.mna_pipeline WHERE ticker = 'TGT'` — the
agent's principal has no clearance for the deal team, so the gateway
rejects.

## Sequence (Mermaid)

```mermaid
sequenceDiagram
    autonumber
    participant T as Trader (principal)
    participant A as Trader Copilot
    participant G as VAPOR Gateway
    participant D as Decision Oracle (Lean)
    participant L as Audit Log
    participant LH as Lakehouse

    T->>A: "Anything interesting in TGT today?"
    A->>G: query(plan) — touches market_data + deals.mna_pipeline
    G->>D: authorize(principal=T, touched=[...])
    D->>D: match rule:<br/>forbid read on deals.* when<br/>dept == TRADING and not MNPI_DEAL_TEAM in clearances
    D-->>G: DENY (reason: rule R-MNPI-001)
    G->>L: append(decision=DENY, principal=T, resource=deals.mna_pipeline.*, rule=R-MNPI-001, ts)
    G-->>A: AuthorizationError(R-MNPI-001)
    A-->>T: "I can't answer — that table is restricted."
    Note over T,LH: Lakehouse never queried;<br/>denial is the side effect that's audited
```

## Policy fragment

```vapor
@rule R-MNPI-001
forbid read, aggregate on deals.*
  when principal.department == TRADING
   and not (MNPI_DEAL_TEAM in principal.clearances)

@rule R-MNPI-002
forbid read on memory.embeddings.*
  when row.labels.source == "slack"
   and row.labels.channel matches "#deal-*"
   and principal.department != IB
   and not (MNPI_DEAL_TEAM in principal.clearances)

@rule R-MNPI-003   -- time-window release
permit read on deals.*
  when row.labels.mnpi_until < now()    -- public after announcement+30d
```

## Lean obligation exercised

- `Rewriter.sound` — reject path fires for any plan touching
  `deals.*` when the principal matches R-MNPI-001's condition.
- `Time-aware predicate` — `now()` and `row.labels.mnpi_until` are
  modeled as parameters in the Lean spec; the soundness argument
  treats `now` as a fixed timestamp at request time.
- `Slice.sound` — the trader principal's policy slice contains
  R-MNPI-001 and R-MNPI-002 even if R-MNPI-003 isn't in the slice;
  this is the test that proves we can't shortcut by slicing too
  aggressively.

## Why RLS / Cedar / SEAL fall short here

- **RLS** can express "TRADING role denied on `deals.mna_pipeline`",
  but cannot bridge `deals` + the *embedding store* with one policy.
  Once the deal-team Slack channels are indexed, RLS has nothing to
  say about vector retrieval.
- **Cedar** authorizes the agent's tool call but doesn't *rewrite the
  plan* — it can deny the entire call but not "drop the M&A columns
  and proceed."
- **SEAL** can sandbox the computation, but only if the deal-team
  owner explicitly publishes a capability — that's a process step
  that doesn't compose with the daily-deals stream.

## Eval angle

Measure:

- Policy LOC: ~6 lines for the wall (above) vs ~120 lines of
  equivalent RLS spread across 4 tables + a `pg_cron` job that toggles
  permission grants at announcement+30d.
- Number of *systems* touched: 1 (`Vapor.Spec`) vs 4
  (RDS RLS + Slack RBAC + pgvector + cron).
- Attacks blocked: indirect prompt injection telling the agent to
  "join with deals.mna_pipeline" — blocked by reject before plan
  reaches the lake.
