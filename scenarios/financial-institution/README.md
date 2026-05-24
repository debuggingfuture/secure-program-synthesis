# Scenario: financial institution, three departments, one lake

Concrete worked example we use throughout the paper and as the
seed for the differential-test corpus.

## Dataset

[`computingvictor/transactions-fraud-datasets`](https://www.kaggle.com/datasets/computingvictor/transactions-fraud-datasets)
on Kaggle. We use a slimmed schema:

| relation              | columns                                                              |
| --------------------- | -------------------------------------------------------------------- |
| `users_data`          | `id, name, email, ssn, region, age`                                  |
| `cards_data`          | `card_id, user_id, card_number, card_type, limit, activated`         |
| `transactions_data`   | `txn_id, card_id, amount, merchant, timestamp`                       |

`users_data.email`, `users_data.ssn`, `cards_data.card_number` are PII /
PCI and must not leave the lake un-redacted.

## Departments (principals)

| principal   | mandate                                          |
| ----------- | ------------------------------------------------ |
| `CRM`       | demographics & segmentation. No PII / card data. |
| `CardOps`   | card inventory & limits. No PAN.                 |
| `FraudRisk` | investigate transactions. Minimum-necessary join with user identity. |

## Policy (Postern grants)

```text
grant CRM       on users_data        { id, name, region, age }
grant CardOps   on cards_data        { card_id, card_type, limit, activated }
grant FraudRisk on transactions_data { txn_id, card_id, amount, merchant, timestamp }
grant FraudRisk on users_data        { id, region }
```

Compiles 1:1 to the `Postern.Policy` list in `verifier/lean/Postern.lean`
(see `namespace Demo`).

## Expected behaviour

| principal   | input plan                                  | rewritten output schema                   |
| ----------- | ------------------------------------------- | ----------------------------------------- |
| `CRM`       | `Scan users_data`                           | `id, name, region, age`                   |
| `CRM`       | `Filter (Scan users_data) on region`        | `id, name, region, age`                   |
| `CRM`       | `Project (... users_data) [ssn, email]`     | `∅` (over-projection collapses)           |
| `CardOps`   | `Scan cards_data`                           | `card_id, card_type, limit, activated`    |
| `CardOps`   | `Scan users_data` (cross-dept attempt)      | `∅`                                       |
| `FraudRisk` | `Scan transactions_data`                    | all five columns                          |
| `FraudRisk` | `Scan users_data`                           | `id, region`                              |
| `Marketing` | `Scan users_data` (unknown principal)       | `∅`                                       |

All eight rows are concrete entries in the JSON corpus that Lean's
`postern-corpus` emits and the Rust harness verifies (see
`prototype/corpus/postern-corpus.json`).

## Threat scenarios captured

- **PII exfil through over-projection.** A CRM agent asks for
  `ssn, email` — the policy intersection drops them silently, so the
  downstream LLM never sees them.
- **Cross-department reach.** A CardOps agent attempting `users_data`
  receives the empty schema; the gateway never opens the file.
- **Minimum-necessary join.** FraudRisk legitimately needs to attach
  a region label to a flagged transaction but does not need the
  customer's name, email, or SSN to do so.
- **Unknown principal.** Capability tokens that don't decode to a
  known principal yield no grants — fail-closed.

## Where joins go

The Lean spec covers single-relation plans only — joins are the
headline future-work item (paper §6). The Rust prototype implements
per-leg rewriting for cross-relation queries; differential testing
covers only what Lean proves.
