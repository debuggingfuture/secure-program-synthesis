# Open questions — for user direction

Things I'd want input on, in rough priority order. None block work; all
shape it.

## 1. Target venue

The paper outline targets SACMAT (closest precedent — SEAL appeared
there in 2023) but the Lean / verification angle would also land at
PLDI/OOPSLA artifact tracks (where Cedar lives) or CIDR (the data-systems
view). My recommendation: **SACMAT** for first submission — the
access-control framing is the headline, and reviewers there will be
familiar with the Cedar/SEAL/RLS comparisons. Backup: CIDR.

Decision needed by: scoping the eval (SACMAT reviewers care about
authoring complexity; PLDI reviewers care about proof depth; CIDR cares
about throughput).

## 2. Project name

`VAPOR` is a working title — `docs/ADR-001-project-name.md` lists
alternatives. The rename is cheap; do it before any external mention.

## 3. Scope of the verified rewriter for the artifact

Three options, increasing in ambition:

a. **Reject-only.** Prove `rewriter_sound_reject` (the current
   skeleton). Practical, defensible, narrow.
b. **Reject + projection + WHERE injection.** Prove `Rewriter.sound`
   for filter+project rewrites. Covers Scenarios 1 + 2 properly.
c. **Above + masking + aggregation predicates.** Prove `Mask.sound`
   and `Aggregate.sound`. Covers all four scenarios. Significantly
   more Lean work.

Recommendation: **(b)** for first submission, **(c)** as a v2
artifact / extended journal. Going straight to (c) risks an
underdeveloped (b) layer.

## 4. Prototype's source-connector reality

Two paths:

- **Faithful mocks** — DuckDB tables seeded from fixtures that mirror
  Slack/PostHog/RDS/D1 schemas. Fast, reproducible, no creds needed.
  Reviewers can `git clone && pytest`.
- **Live connectors** — actual Slack API, PostHog HogQL, RDS, D1.
  More credible end-to-end but reproducibility suffers.

Recommendation: **mocks-first**, with one optional live demo (PostHog
since its query API is the friendliest).

## 5. Differential testing harness scope

Cedar's VGD methodology requires both the Lean spec and the production
decision oracle accept the same set of inputs and agree on outputs.
Two options:

- **FFI** — Lean exports decision oracle as `extern`-callable; Python
  calls it via `cedar-lean-ffi`-style binding. Higher integration cost.
- **Generate-and-compare** — Python and Lean both consume the same
  fuzz corpus written to JSONL; a third script diff-checks.
  Lower integration cost, weaker guarantee (Python may drift from
  Lean between regen runs).

Recommendation: **generate-and-compare** for the paper artifact;
FFI as a follow-on engineering effort.

## 6. Public vs private during development

Repo remote is `fractalboxdev/secure-program-synthesis`. Is this
intended public from the start, or kept private until paper
submission?  The Lean code + scenarios + outline are publishable; the
threat-model exhaustiveness and any future user-data-driven eval
would be the bits to gate.

If public from the start: I'd push `main` with the current scaffold
and continue work in feature PRs (current `research/initial-scaffold`
branch is ready). If private: same, with restricted visibility.

## 7. Engagement with upstream artifacts

The Cedar team's `cedar-spec` Lean repo is the closest model. Two
useful engagements:

- **Cite + diff.** Treat them as related work, articulate where we
  differ (plan-level vs API-level).
- **Contribute back.** If our `Plan` IR ↔ Cedar entity model has any
  general-purpose mapping, that's a candidate upstream PR.

Recommendation: **cite + diff** for the paper; revisit upstreaming
after acceptance.

## 8. LLM-emitted policy demo

Listed as future work but feasible inside the paper window: small loop
where an agent drafts a `Vapor.Spec` policy from English, `Vapor.Analyze`
checks for "could this ever leak X", a human approves. Whether this
goes in the headline contributions or in §7 (future work) shapes how
much eval is needed.

Recommendation: **future work** for v1; pilot during eval if there's
time.
