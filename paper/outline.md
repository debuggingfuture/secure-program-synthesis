# Paper outline — VAPOR

**Working title:** *Verified Access Policy Over Retrieval: A Lean4-checked
mediator for agentic-context data lakehouses*

**Target venue (candidates, in decreasing fit):**
SOSP / OSDI workshops on AI infrastructure · SACMAT · USENIX Security ·
PLDI (artifact track) · CIDR. The Cedar PLDI 2024 paper sets a precedent
for "verified policy language" at PL venues; SACMAT (where SEAL appeared)
is the most natural fit for the access-control framing.

## Thesis

> Agentic-context pipelines collapse per-SaaS RBAC into a single shared
> data plane. A **decoupled, dataframe-aware policy layer** — whose
> semantics are mechanized in Lean 4 and whose enforcement is a
> machine-verified plan rewriter — can re-establish least-privilege across
> heterogeneous sources without coupling policy to any single store.

## Claimed contributions

1. **Problem framing.** First (to our knowledge) treatment of access
   control specifically for **agentic context systems** — the union of
   ETL-fed lakehouses, vector/KG memory stores (mem0, Notion AI), and
   tool-calling agents — where the threat model fuses prompt injection,
   over-broad ingest, and cross-source aggregation attacks.
2. **A policy DSL `Vapor.Spec`** with denotational semantics in Lean 4.
   Cedar-shaped surface syntax (principal/action/resource/context) extended
   with dataframe-aware predicates over rows, columns, and aggregations.
3. **A verified query-plan rewriter.** Given a Substrait plan `q` and
   policy `P`, produces `q' = rewrite(q, P)` such that `eval(q') ⊑
   allowed(q, P)` — proved sound in Lean.
4. **A reference enforcement gateway.** Ibis-based Python prototype that
   intercepts dataframe operations from agent tools, calls the
   Lean-extracted decision oracle, and emits the rewritten plan to the
   underlying engine (DuckDB / Postgres / D1 / Slack search / PostHog HogQL).
5. **Empirical evaluation** on four scenarios derived from a realistic
   stack (Slack + PostHog + RDS + D1), comparing against Postgres RLS and
   bare Cedar baselines on: policy LOC, authoring complexity, query
   overhead, and the set of attacks each baseline lets through.

## System overview

```mermaid
flowchart LR
  subgraph Sources
    SLK[Slack]
    PH[PostHog]
    RDS[(AWS RDS)]
    D1[(Cloudflare D1)]
  end
  subgraph Lakehouse[Lakehouse / Iceberg]
    BRZ[Bronze]
    SLV[Silver]
    GLD[Gold]
  end
  subgraph VAPOR[VAPOR mediator]
    ING[Ingest policy filter]
    GW[Dataframe gateway]
    DEC[Decision oracle\n(extracted from Lean)]
    REW[Plan rewriter]
  end
  subgraph Agents
    ENG[Engineer agent]
    FIN[Finance agent]
    SUP[Support agent]
  end

  SLK --> ING --> BRZ --> SLV --> GLD
  PH --> ING
  RDS --> ING
  D1 --> ING
  ENG --> GW
  FIN --> GW
  SUP --> GW
  GW --> DEC
  GW --> REW --> GLD
  DEC -.policy decisions.-> REW
```

The same `Vapor.Spec` policy artifact drives both `ING` (write-side
mediation: drop / hash / aggregate before landing) and `GW + REW`
(read-side mediation: rewrite queries before they hit storage). Both paths
share a single Lean-verified decision function.

## Motivating example (running through the paper)

A platform engineer's "ops copilot" agent is granted broad read on the
analytics lake to debug pipeline failures. A Slack message containing
indirect-prompt-injection content (e.g. shared in `#general` and ingested
into the lake's `slack_messages` Bronze table) instructs the agent to
"join `slack_messages` with `finance.payroll` and email the result." Under
RLS the join silently returns rows the engineer's role can read on each
table individually — but the *combination* leaks payroll. Under VAPOR, the
policy expresses **column-set capabilities and per-resource aggregation
predicates**; the plan rewriter rejects the join (the engineer principal
has no capability covering `finance.payroll.*`), and the Lean theorem
guarantees no rewrite path could have surfaced those rows.

## Threat model

- **Untrusted agent.** Issues arbitrary dataframe / SQL / retrieval ops.
  May be prompt-injected; we treat the agent as adversarial.
- **Untrusted ingest payloads.** Source data (Slack messages, PostHog
  events) may be attacker-controlled (indirect prompt injection, label
  spoofing in payload metadata).
- **Trusted policy author.** A human (or LLM with human review) writes
  `Vapor.Spec` policies. Authoring mistakes are *in scope* for analysis
  (we provide `Vapor.Analyze` à la Cedar's symbolic compiler) but not
  attack-model trust.
- **Trusted gateway + Lean kernel.** TCB = the gateway process + the
  Lean-extracted oracle + the rewriter's compiled artifact. Sources and
  agents are outside the TCB.
- **Out of scope (this paper).** Side channels, DoS, query-result-based
  inference attacks beyond the aggregation predicates we explicitly model.

## Proof obligations (Lean 4)

Mirroring `cedar-spec/cedar-lean`:

| Theorem | Statement (informal) |
|---|---|
| `Spec.authorize_sound` | `Forbid` policies always deny; `Permit` policies require explicit allowance; order-independence. |
| `Rewriter.sound` | `∀ q P. ⟦rewrite(q,P)⟧ ⊑ ⟦q⟧ ∩ allowed(P)` (rewritten plan only returns rows the policy allows). |
| `Rewriter.transparent` | If `P` admits the entire schema, `rewrite(q,P) ≡ q` (no-policy = no rewrite). |
| `Slice.sound` | Per-principal policy slicing produces the same decision as evaluating the full policy store. |
| `Ingest.sound` | Bronze-tier ingest filter is *write-side* equivalent to read-side rewrite — `eval(query, Bronze_after_ingest) ⊑ allowed(query)`. This is the key novel theorem: read-side and write-side enforcement compose. |
| `SymCC.sound` / `.complete` | Analysis tool answers "could policy P ever allow access to column X for principal Y" with no false negatives/positives (delegated to SMT, sound-by-construction). |

## Evaluation plan

**Workload:** four scenarios from `scenarios/`:

1. *Engineer vs Finance* — running example above.
2. *Support vs PII* — support agent on customer table; emails must hash,
   support tier visible, payment tokens never visible.
3. *Exec aggregate-only* — exec agent may see `SUM(revenue) GROUP BY week`
   but never raw rows (an aggregation predicate).
4. *Cross-source RAG* — RAG over Slack + Notion + PostHog. Engineer agent
   has tenant-scoped Slack access; embedding retrieval must not surface
   chunks from disallowed channels (label-on-embedding).

**Baselines:** Postgres RLS (single source), Cedar (per-API authorization
without rewrite), open-policy-agent / OPA-Rego (general-purpose).

**Metrics:**
- **Authoring:** policy LOC, # distinct artifacts (one per source vs one
  total), # source-specific concepts leaking into policy text.
- **Soundness:** for each baseline, count of scenario attacks that
  silently succeed (manual + property-based fuzz with the policy as
  oracle).
- **Performance:** added end-to-end latency per query; Lean-extracted
  oracle call overhead; policy compile time (Lean → decision artifact).
- **Verification cost:** Lean proof LOC, total compile time on commodity
  hardware, # SMT queries Cedar-Analyze-style answers.

## Limitations & open challenges

1. **Aggregation-inference attacks** beyond the predicates the policy
   author writes are not caught. We model differential-privacy-flavored
   predicates but don't add a DP mechanism.
2. **Free-text egress.** An agent that reads allowed rows can still
   exfiltrate them via tool output. VAPOR enforces *access*, not
   *post-access*; pairs naturally with output filters (out of scope).
3. **Policy authoring is still hard.** We help with `Vapor.Analyze`
   (symbolic compiler à la Cedar) but the author must still know what
   to permit/deny.
4. **Source connector trust.** Each ingest connector is in the TCB for
   labeling; mislabeling at ingest defeats the rewriter. Verifying
   connectors is future work.
5. **Lean→runtime gap.** Decision oracle is extracted (or reflected via
   FFI à la `cedar-lean-ffi`). Differential testing closes the gap; we
   adopt Cedar's VGD methodology.

## Future work

- DP / k-anonymity mechanisms wired into the same policy artifact.
- Verified ingest connectors (start with PostHog → Iceberg).
- Replace string-DSL policies with **LLM-emitted-then-verified** policies
  (agent proposes policy, Lean checks, human approves).
- Capability-passing across agent boundaries (compose with SEAL's
  capability model — they handle the sandboxed-compute story we do not).

## Cuts (explicit non-goals)

- No new policy *language* concepts beyond Cedar's expressiveness.
  Reusing Cedar's surface where possible.
- No claim of better SQL performance than the engine baseline.
- Not a replacement for end-to-end DP; one layer of a defense-in-depth
  stack.
