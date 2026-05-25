# Postern

> *A Lean-verified access gateway for agentic data lakehouses.*

Research artifact for Track 3 of the [Apart Research Secure Program
Synthesis Hackathon, 2026-05-22 → 2026-05-24](https://apartresearch.com/sprints/secure-program-synthesis-hackathon-2026-05-22-to-2026-05-24).

**Site.** [postern-web.pages.dev](https://postern-web.pages.dev) —
landing page, 7-slide deck (`/slides`), rendered paper
(`/paper`), and WASM rewriter demo (`/demo`). Deployed from
`web/dist` via `pnpm -C web deploy:cf` (`wrangler pages deploy`).

**Problem.** Agents querying a lakehouse aren't humans on stable
roles. Their effective rights are *context-driven* — which
principal the agent acts for, which task it was invoked under,
which scope the caller granted — and the same agent code may
legitimately need different views on different calls. RBAC's
static *identity → role → permission* chain encodes none of that;
per-engine RLS does not survive ETL into an engine-agnostic
Parquet store; physical tenant segregation forfeits the
cross-source joins that motivate the lakehouse in the first place.
Policy has to move to the *query plane*, gated under the agent's
task-scoped identity at query time.

**Solution.** Postern mediates every read at the plan boundary
against a column-grant policy. Its core — Plan IR, policy DSL,
rewriter — is **mechanized in Lean 4**, with eleven theorems
certifying that every accepted plan's output schema *and*
filter-predicate read-set *and* (for cross-relation joins) the
join-key are contained in the policy-allowed columns. A Rust
implementation mirrors the algorithm and is conformance-tested
against the Lean reference (21 / 21 cases).

## What's in the box

| Path                  | What                                                                                  |
| --------------------- | ------------------------------------------------------------------------------------- |
| `paper/`              | Pandoc-Markdown paper + BibTeX. Build with `paper/build.sh` (needs pandoc + xelatex). |
| `verifier/lean/`      | Lean 4 spec, **eleven** theorems (eight fully proved; three with `sorryAx` on the `Join` arm only), axiom audit, corpus emitter. |
| `prototype/`          | Rust workspace mirroring the Lean types (`postern-core`) and the conformance harness (`postern-diff`). |
| `scenarios/financial-institution/` | Kaggle transactions-fraud-datasets case study, three departments.        |
| `scripts/reproduce.sh` | One-shot reproduction.                                                               |

## Acceptance criteria, met

1. **Lean 4 theorems.** Eleven theorems span output-column
   soundness (generalised over `touchedRels` to cover the
   cross-relation join arm), **filter-predicate soundness**
   (closes the `WHERE ssn = ?` side-channel), schema subset,
   monotonicity in policy, idempotence, explicit-refusal lemmas
   for unknown relations and forbidden filter columns, the
   headline `rewrite_sound_join`, and the join-key-leak
   coverage condition `rewrite_refuses_unallowed_join_key`.
   Eight are fully `sorry`-free; three (`rewrite_idempotent`,
   `rewrite_monotone`, `rewrite_refuses_forbidden_filter`)
   carry a `sorryAx` on the `Join` arm only — non-Join cases
   are fully proved. `CheckAxioms.lean` reports the per-theorem
   axiom set.

2. **Conformance testing.** `postern-diff` runs the Rust rewriter
   against the Lean-emitted reference corpus; **21 / 21 cases pass**
   on the demo scenario (16 accept, 5 refuse — including three
   join cases exercising the cross-relation arm).

## Reproduce

```sh
scripts/reproduce.sh
```

Expected tail:

```
21/21 cases pass (Lean reference == Rust impl)
==> All green.
```

The script also runs the axiom audit (`#print axioms` on every
load-bearing theorem) and checks the committed corpus matches what
Lean emits today (catches drift).

Toolchains: **Lean 4.29.1** (pinned in `verifier/lean/lean-toolchain`),
**Rust stable** (tested with 1.93). Runs in under two minutes on an
M-series Mac on a warm cache.

## Design summary

- **Policy** is a list of column-grants $\langle p, r, C\rangle$ —
  "principal $p$ may read columns $C$ on relation $r$".
  Fail-closed, monotone grant-only (no deny-lists by design;
  see paper §6).
- **Plan IR** is `Scan(rel) | Project(plan, cols) | Filter(plan, col)`
  — single-relation by design so soundness stays small.
- **Rewriter** returns `Option Plan`. Refuses on unknown relation
  or forbidden filter column; on accept wraps the plan in a
  `Project` of `schema(q) ∩ allowed(P, prin, touched(q))`.
- **Capability distribution** is via biscuit tokens (prototype-side,
  outside the proof).
- **Surface** in the prototype is an MCP server over Polars / DuckDB.

See `paper/paper.md` §3–§5 for the full design and §6 for open
challenges (joins, aggregation + DP, biscuit attenuation in-proof).

## Defense-in-depth

Postern is the **plan-boundary** layer — last chance to bound what
a query can read. Pair it with an **agent-code-boundary** layer
like the Scala-3-capture-checking approach from Odersky et al.
2026 ([arXiv:2603.00991](https://arxiv.org/abs/2603.00991)), which
makes capabilities first-class program variables so agent-emitted
code cannot exfiltrate data it doesn't hold a capability for. The
two layers compose without re-verifying each other's TCB; see
paper §3 "Defense-in-depth with capability tracking".

## Status & scope

This is a research artifact, not production code. The Lean spec
covers single-relation plans; the Rust impl carries joins by per-leg
rewriting but those compositions are not yet under proof. Aggregation,
filter-timing side-channels, and the planner→executor lowering step
are out of scope for the current theorem set — see paper §2 (threat
model) and §6.

## License

MIT OR Apache-2.0 (workspace-wide).
