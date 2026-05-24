# Postern

> *A Lean-verified access gateway for agentic data lakehouses.*

Research artifact for Track 3 of the [Apart Research Secure Program
Synthesis Hackathon, 2026-05-22 → 2026-05-24](https://apartresearch.com/sprints/secure-program-synthesis-hackathon-2026-05-22-to-2026-05-24).

LLM agents read their context out of a single DuckDB-over-Parquet
lakehouse fed by Airbyte / mem0-style retrieval. The per-source RBAC
that protected each upstream SaaS does not survive the lake boundary.
Postern is a small policy DSL + plan rewriter that sits between
agents and the lake, with the **rewriter's correctness mechanized in
Lean 4** and a Rust implementation differentially tested against the
Lean reference.

## What's in the box

| Path                  | What                                                                                  |
| --------------------- | ------------------------------------------------------------------------------------- |
| `paper/`              | Pandoc-Markdown paper + BibTeX. Build with `paper/build.sh` (needs pandoc + xelatex). |
| `verifier/lean/`      | Lean 4 spec: policy DSL, Plan IR, rewriter, **three fully-proved theorems**.          |
| `verifier/lean/Main.lean` | Emits the differential-test JSON corpus.                                          |
| `verifier/lean/CheckAxioms.lean` | Compile-time audit of axiom dependencies.                                  |
| `prototype/`          | Rust workspace mirroring the Lean types (`postern-core`) and the diff harness (`postern-diff`). |
| `scenarios/financial-institution/` | Kaggle transactions-fraud-datasets case study, three departments.        |

## Acceptance criteria, met

1. **Fully proved Lean 4 theorem.** `Postern.rewrite_sound` — every
   column in the rewritten plan's output schema is allowed by the
   policy for the requesting principal. No `sorry`. `CheckAxioms.lean`
   confirms dependencies are only Lean's standard `propext` and
   `Quot.sound`.
2. **Differential testing.** `postern-diff` runs the Rust rewriter
   against the Lean-emitted reference corpus; **10 / 10 cases pass**
   on the demo scenario.

## Reproduce

```sh
# 1. Lean: build + axiom-audit + emit corpus.
cd verifier/lean
lake build                                # builds Postern + CheckAxioms
lake exe postern-corpus \
  > ../../prototype/corpus/postern-corpus.json

# 2. Rust: unit tests + differential test.
cd ../../prototype
cargo test --workspace
cargo run -p postern-diff -- corpus/postern-corpus.json
```

Expected tail of step 2:

```
10/10 cases pass (Lean reference == Rust impl)
```

## Design summary

- **Policy** is a list of column-grants $\langle p, r, C\rangle$ —
  "principal $p$ may read columns $C$ on relation $r$". Fail-closed.
- **Plan IR** is `Scan(rel) | Project(plan, cols) | Filter(plan, col)`
  — single-relation by design so the soundness proof stays small.
- **Rewriter** wraps the plan in a `Project` whose column list is
  `schema(q) ∩ allowed(P, principal, touched(q))`.
- **Capability** distribution is via biscuit tokens (prototype-side,
  outside the proof).
- **Surface** in the prototype is an MCP server over Polars/DuckDB.

See `paper/paper.md` §3–§5 for the full design and §6 for open
challenges (joins, filter side-channels, aggregation, policy
synthesis from NL).

## Status & scope

This is a research artifact, not production code. The Lean spec
covers single-relation plans; the Rust impl carries joins by per-leg
rewriting but those compositions are not yet under proof. Filter
side-channels are out of scope for the current theorem set — see
paper §6.

## License

MIT OR Apache-2.0 (workspace-wide).
