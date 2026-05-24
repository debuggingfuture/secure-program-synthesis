# Postern — 10-line summary

1. **Problem.** Airbyte writes Slack threads, Salesforce contacts, and Stripe charges into one Parquet bucket — channel ACLs, field-level security, and customer-scoped tokens collapse into a single DuckDB service-account role, and the querying agent inherits the *union* of those permissions.
2. **Thesis.** Insert a verified gateway that *rewrites* every plan against a small column-grant policy; agents and their generated SQL stay untrusted.
3. **Lean 4 spec.** `Plan = Scan | Project | Filter`, column-grant `Policy`, `rewrite : ... → Option Plan` with explicit refusals.
4. **Headline theorems.** `rewrite_sound` (output-column ⊆ allowed) and `rewrite_filter_sound` (predicate-column ⊆ allowed) — the latter closes the `WHERE ssn = ?` side-channel.
5. **Proof discipline.** Nine theorems, no `sorry`. `CheckAxioms.lean` confirms the axiom set is bounded by `{propext, Quot.sound}` (Lean stdlib); two theorems depend on none.
6. **Rust mirror.** `postern-core` reimplements the same types and `rewrite` algorithm for a Polars / DuckDB gateway.
7. **Conformance testing.** Lean emits a JSON corpus of 18 cases; `postern-diff` runs Rust against it. **18 / 18 pass** — 15 accept, 3 refusal-regressions (unknown relation, forbidden filter, nested forbidden filter).
8. **Demo.** Kaggle `transactions-fraud-datasets`, three principals (CRM / CardOps / FraudRisk) — PII redaction, cross-department refusal, minimum-necessary disclosure.
9. **Repro.** `scripts/reproduce.sh` runs Lean → axiom audit → corpus → Rust → diff end-to-end in under two minutes.
10. **Open challenges.** Joins under proof; aggregation + DP boundary; biscuit attenuation modelled inside the proof (paper §6). Defense-in-depth: pair with agent-side capability tracking [Odersky et al. 2026, [arXiv:2603.00991](https://arxiv.org/abs/2603.00991)] — the two layers compose without re-verifying each other's TCB.
