# Scenario 06 — GDPR data residency

## Setting

BankCo has EU (Frankfurt), UK (London), and US (Virginia) customers.
GDPR Art. 5(1)(f) plus internal interpretation: EU customer personal
data must not leave EU regions during *processing*. The Iceberg lake
is region-partitioned but the catalog spans regions; an analyst in NYC
can query an EU-partitioned table physically pinned to Frankfurt — at
which point bytes do leave the EU even though "the table is in EU."

The Wealth team in Frankfurt has an "Advisor Copilot" with read on EU
HNW clients. The Wealth team in NYC has an analogous copilot for US
HNW clients. The two teams sometimes cross-cover; the cover protocol
is the source of trouble.

## What must not happen

- A US-principal agent must not retrieve EU customer PII *anywhere* —
  even into ephemeral memory in a US-region VPC.
- A right-to-be-forgotten request from `customer_id = 4711` must
  cascade: future reads see `tombstone`; cached embeddings for that
  customer are invalidated; the ingest path drops the customer's rows
  on the next sync.
- A US analyst running an aggregate over global revenue may see EU
  contributions only via row-counts ≥ k=50 *with* a residency-aware
  group; never via raw rows.

## Sequence (Mermaid)

```mermaid
sequenceDiagram
    autonumber
    participant U as US Analyst (principal.country=US)
    participant A as Advisor Copilot (US region)
    participant GUS as VAPOR Gateway (US)
    participant D as Decision Oracle
    participant LEU as Lakehouse (EU partition)
    participant LUS as Lakehouse (US partition)

    U->>A: "Pull customer 4711's portfolio."
    A->>GUS: query(plan) — read on customers + portfolios for cust 4711
    GUS->>D: authorize(principal=U, touched=[customers, portfolios], context.row_labels=labels(4711))
    D->>D: labels.residency=["DE","EU"] ; principal.country=US ∉ residency
    D-->>GUS: DENY (R-GDPR-RES-001)
    GUS-->>A: AuthorizationError(reason: residency)
    A-->>U: "I cannot fetch this customer from the US region. Use the EU dashboard."

    Note over U,LUS: Compare to allowed path:
    U->>A: "Pull customer 9001's portfolio." (US resident)
    A->>GUS: query(plan)
    GUS->>D: authorize(...)  labels.residency=["US"]; principal.country=US
    D-->>GUS: ALLOW (R-GDPR-RES-002)
    GUS->>LUS: rewritten plan
    LUS-->>GUS: rows
    GUS-->>A: rows
```

## Policy fragment

```vapor
@rule R-GDPR-RES-001
forbid read, aggregate on customers.*
  when 'EU' in row.labels.residency
   and principal.country not in row.labels.residency

@rule R-GDPR-RES-002
permit read on customers.*
  when principal.country in row.labels.residency

@rule R-GDPR-RTBF
mask customers.*
  using tombstone
  when row.id in dataset("rtbf_active")

@rule R-GDPR-EMBED-RES
forbid read on memory.embeddings.*
  when 'EU' in row.labels.residency
   and principal.country not in row.labels.residency
```

## Lean obligation: `Ingest.compose`

This scenario is the headline test for the *ingest+egress equivalence*
theorem. Two enforcement paths must produce the same observable set:

- **Read-side:** the US gateway calls the EU partition, the rewriter
  rejects rows whose residency excludes US.
- **Write-side:** the US partition's ingest filter never accepts EU
  rows in the first place. A US-region replica of the
  `customers` table simply contains no EU rows.

`Ingest.compose` (Lean theorem we want):

```
∀ q P region.
  eval_at(region, rewrite(q, P)) ⊑
  eval_at(region, q.over(Ingest(P, region).output))
```

i.e. *"reading through the read-side rewriter at region R against the
global table is equivalent to reading the unrewritten query at R
against the region-filtered table."* Without this theorem, a bank
running both read-side and write-side enforcement has no proof they
agree — a Class-of-2025 regulatory headache.

## Eval angle

- Policy LOC: residency rules ~10 lines vs the status-quo combination
  of Lake Formation tags + per-region IAM + a `customers_eu_only`
  materialized view per region (~hundreds of lines, plus the manual
  sync to embed the residency tag in the view name).
- Attack blocked: indirect injection in a US-resident customer's CRM
  notes telling the agent "also fetch customer 4711 for comparison."
- Performance: residency check is a label comparison — `O(1)` per row,
  pushed below the join.
