# Compliance regime → VAPOR control map

How each regulatory requirement compiles to a `Vapor.Spec` primitive.

| Regime | Requirement | VAPOR primitive | Scenario |
|---|---|---|---|
| MNPI / Chinese wall | "Trading must not see in-flight M&A pipeline data" | `forbid read on deals.* when principal.dept == TRADING and not MNPI_DEAL_TEAM in principal.clearances` | 05 |
| MNPI announcement window | "Public information after 30d post-announcement" | `row.labels.mnpi_until ≥ now()` — embedded in label, time-aware | 05 |
| GDPR Art. 5 (residency) | "EU personal data processed in EU" | `forbid read on customer.* when 'EU' in row.labels.residency and principal.country not in row.labels.residency` | 06 |
| GDPR Art. 17 (RTBF) | "Erase on request" | `mask <pk> using tombstone for row.id in $rtbf_set` — applied at ingest **and** egress | 06 |
| PCI-DSS 3.4 | "PAN unreadable wherever stored" | `mask pan using mask_pan_keep_last4`, `forbid read on cards.cvv` | (cross-cutting) |
| SOX §404 (SoD) | "Same person cannot create and approve a journal entry" | cross-row `forbid` predicate over `(initiator_id, approver_id)` matching `principal.id` | 07 |
| FINRA 3110 (supervision) | "Supervisor reads only their direct reports' comms" | `permit read on comms.* when row.from in principal.direct_reports` | (variant of 07) |
| BCBS 239 risk aggregation | "Risk data presented at sufficient aggregation" | `aggregate.is_grouped_by_at_least([book, region]) and aggregate.row_count ≥ 50` | (Scenario 3 from generic set, applied to Risk dept) |
| MiFID II Art. 16 record-keeping | "5-year retention of decision records" | resource label `retention: 5y`; `Vapor.Ingest` writes audit-log entry on every read | 08 |
| GLBA Safeguards | "Customer financial data only to authorized roles, with logged access" | `permit + log` rule; `LOG` is part of decision oracle output | 08 |
| Volcker Rule | "Prop-trading positions separated from client-flow desks" | `forbid read on prop_positions.* when principal.desk != 'PROP'` | (variant of 05) |
| Audit immutability | "Audit log is append-only, retention-locked" | log sink is outside agent's write path; verified `Log.append_only` | 08 |

## What VAPOR adds vs status quo

The status quo in most banks for these controls:

1. **Per-system ACLs.** Order management has its own RBAC; HRIS has its
   own; the lakehouse has Lake Formation tags; Snowflake has masking
   policies; Slack has channels. Each is correct in isolation.
2. **A spreadsheet ("Information Barriers Register") that maps people
   to walls.** Synced into IAM groups every quarter.
3. **A periodic audit by an external firm** that samples a handful of
   queries and asserts they look reasonable.
4. **Tribal knowledge** for new edge cases.

**Where this breaks once agents enter the picture:**

- The lakehouse ingest service account is *one* identity, not a
  spreadsheet. After ETL, the per-system ACL is gone.
- Agents make far more queries than humans. The "audit samples a
  handful" model breaks at agent QPS.
- LLM agents can be prompt-injected into queries no human would have
  authored. The audit-after-the-fact model can't catch this.
- The walls are written in English in the spreadsheet; their mechanical
  expression is divergent across systems.

VAPOR collapses all of this into one source of truth (`Vapor.Spec`),
proves the enforcement is sound (`Vapor.Thm`), and makes the audit log
a byproduct of the decision oracle (not a separate after-the-fact
process). For the regulator, that means:

> *"Show me every query in 2026-Q1 where a TRADING principal observed
> a column derived from deals.mna_pipeline."*

is one SQL query against the audit log, not a forensic engagement.
