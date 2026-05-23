# Scenario 07 — SOX segregation of duties

## Setting

Finance/Treasury runs a "Treasury Copilot" that drafts and approves
intercompany journal entries. Under SOX §404 the *initiator* of a
journal entry must not also be the *approver*; the segregation is
audited annually and is the most common SOX deficiency cited at
mid-size banks.

The agent itself is invoked by a treasury accountant. The accountant
asks: *"Approve all my pending entries under $10K."*

## What must not happen

- Any approval where `initiator_id == approver_id` must be impossible
  to express through the gateway — not "filtered" — *inexpressible*.
- The agent cannot exfiltrate the list of pending entries authored by
  *other* accountants and write its own approval over them either
  (variant: spoofing principal in `context`).
- An audit log entry exists for every approve action, keyed on
  (initiator, approver, entry_id, amount, timestamp).

## Policy fragment

```vapor
@rule R-SOX-SoD-001
forbid action approve on journal_entries.*
  when row.initiator_id == principal.id

@rule R-SOX-SoD-002         -- principal cannot impersonate someone else's approval
forbid action approve on journal_entries.*
  when row.approver_id != principal.id      -- approver column on write must match

@rule R-FINRA-SUP-001        -- variant: supervisor sees only own reports
permit read on comms.*
  when row.from_user in principal.direct_reports
   and principal.role == 'SUPERVISOR'
```

## Sequence (Mermaid)

```mermaid
sequenceDiagram
    autonumber
    participant U as Accountant Alice (principal)
    participant A as Treasury Copilot
    participant G as VAPOR Gateway
    participant D as Decision Oracle
    participant LH as Journal Entries

    U->>A: "Approve all my pending entries under $10K."
    A->>G: plan = UPDATE journal_entries SET approver_id=Alice WHERE pending AND amount<10000

    G->>D: authorize(principal=Alice, action=approve, touched=plan-rows-preview)
    Note right of D: preview = ([{initiator_id: Alice, ...},<br/>{initiator_id: Bob, ...},<br/>{initiator_id: Alice, ...}])
    D->>D: For each row:<br/>R-SOX-SoD-001 hits when initiator_id == Alice
    D-->>G: DENY for Alice-initiated rows; ALLOW for Bob-initiated rows
    G-->>A: PartialAuthorization(allowed=[Bob's row], denied=[two Alice-initiated], reason=R-SOX-SoD-001)
    A-->>U: "I can only approve 1 of 3 — two were initiated by you. <br/>Forward those to your manager?"

    G->>LH: rewritten UPDATE for allowed row only
    G->>L: append audit entries × 3 (1 allow, 2 deny)
```

## Lean obligation: cross-row predicates

This scenario exercises a *cross-row* `forbid` — the policy
predicate references both `principal.id` and `row.initiator_id` from
the *target* row of the write. This is harder than the per-row read
predicates in scenarios 05–06; the soundness theorem is:

```
∀ q P. q.action = approve →
  ∀ row ∈ eval(rewrite(q, P)).target_rows.
    row.initiator_id ≠ principal(q).id
```

This pushes us into a "write-rewrite" extension of `Vapor.Rewriter` —
currently scaffolded as future work; the scenario motivates promoting
it into v1 if SOX/SoD is part of the eval narrative.

## Why "filter" is not enough

A common-but-broken design: the gateway runs the query, then filters
SoD-violating rows out of the result. This is **wrong** for two
reasons:

1. The write happened *before* filtering. Side effects are not
   reversible.
2. An attacker can observe the difference between "row not in result"
   and "row never existed" — the SoD violation list itself is
   sensitive information.

VAPOR's *partial-authorization* response shape carries enough info for
the agent to be useful (knows which rows it cannot act on) without
leaking which specific rows would have violated which rule.

## Eval angle

- Lines of code in the typical bank's SoD enforcement: hundreds (ERP
  trigger + audit job + period-end reconciliation report) vs ~3 lines
  in `Vapor.Spec`.
- Time to add a new SoD rule (e.g. for a new entity type): minutes vs
  weeks of release engineering.
