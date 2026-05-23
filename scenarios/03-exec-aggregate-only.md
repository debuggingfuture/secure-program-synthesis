# Scenario 3 — Exec agent, aggregates only

## Setting

CEO/CFO agent for high-level dashboards. Reads `finance.invoices` and
`finance.payroll` — but only as aggregates with a grouping coarser than
a tunable threshold (e.g. week, region, dept).

## What VAPOR should do

```vapor
@principal(role: "exec")
permit
  aggregate on application_db.finance.invoices.*
  when
    aggregation.is_grouped_by_at_least(["region", "week"])
    and aggregation.row_count >= 50

forbid
  read on application_db.finance.invoices.*     -- no raw rows
```

The plan rewriter checks the relational algebra: the top of the plan
must be a `GROUP BY` containing the required keys, and a post-filter
enforces `count(*) >= 50` on each group; if not, the query is rejected.

## Why this is hard

The author of an SMT-style policy can express "principal X can never
read row r"; expressing "principal X can read aggregates but not raw
rows" requires the policy language to be a *first-class citizen of the
relational algebra*. This is precisely the gap between Cedar
(API-call-level) and VAPOR (plan-level).

## Lean obligation: `Aggregate.sound`

```
∀ q P. q.is_aggregate ∧ q.groups ⊇ P.required_groups(c) ∧ q.k ≥ P.k_anon(c)
       → c ∈ allowed(P, q)
∀ q P. ¬q.is_aggregate ∧ touches(q, c) ∧ c ∈ raw_forbid(P)
       → rewrite(q, P) = ⊥
```

We model the "min group size" predicate; we do not implement
differential privacy (out of scope, future work).

## Future-work hook

A DP mechanism (e.g. Laplace noise on the aggregate) could be wired
into the policy as a different *mask*, sharing the `Mask.sound`
machinery.
