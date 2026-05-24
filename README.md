# Postern

> *A Lean-verified access gateway for agentic data lakehouses.*

Research artifact for Track 3 of the [Apart Research Secure Program
Synthesis Hackathon, 2026-05-22 → 2026-05-24](https://apartresearch.com/sprints/secure-program-synthesis-hackathon-2026-05-22-to-2026-05-24).

LLM agents read their context out of a single DuckDB-over-Parquet
lakehouse fed by Airbyte / mem0-style retrieval. The per-source RBAC
that protected each upstream SaaS does not survive the lake boundary.
Postern is a small policy DSL + plan rewriter that sits between
agents and the lake, with the **rewriter's correctness mechanized in
Lean 4** and a Rust implementation conformance-tested against the
Lean reference.

## What's in the box

| Path                  | What                                                                                  |
| --------------------- | ------------------------------------------------------------------------------------- |
| `paper/`              | Pandoc-Markdown paper + BibTeX. Build with `paper/build.sh` (needs pandoc + xelatex). |
| `verifier/lean/`      | Lean 4 spec, **nine** fully-proved theorems, axiom audit, corpus emitter.             |
| `prototype/`          | Rust workspace mirroring the Lean types (`postern-core`) and the conformance harness (`postern-diff`). |
| `scenarios/financial-institution/` | Kaggle transactions-fraud-datasets case study, three departments.        |
| `scripts/reproduce.sh` | One-shot reproduction.                                                               |

## Acceptance criteria, met

1. **Fully proved Lean 4 theorem(s).** Nine theorems span output-
   column soundness, **filter-predicate soundness** (closes the
   `WHERE ssn = ?` side-channel), schema subset, monotonicity in
   policy, idempotence, and explicit-refusal lemmas for unknown
   relations and forbidden filter columns. No `sorry`.
   `CheckAxioms.lean` reports the per-theorem axiom set is bounded
   by `{propext, Quot.sound}` — Lean's built-in foundational
   axioms; two theorems depend on *none*.

2. **Conformance testing.** `postern-diff` runs the Rust rewriter
   against the Lean-emitted reference corpus; **18 / 18 cases pass**
   on the demo scenario (15 accept, 3 refuse — including regression
   cases for known attack shapes).

## Reproduce

```sh
scripts/reproduce.sh
```

Expected tail:

```
18/18 cases pass (Lean reference == Rust impl)
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

## Status & scope

This is a research artifact, not production code. The Lean spec
covers single-relation plans; the Rust impl carries joins by per-leg
rewriting but those compositions are not yet under proof. Aggregation,
filter-timing side-channels, and the planner→executor lowering step
are out of scope for the current theorem set — see paper §2 (threat
model) and §6.

## License

MIT OR Apache-2.0 (workspace-wide).
