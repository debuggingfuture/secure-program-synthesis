# Postern — Rust prototype

Mirror of the Lean spec in `../verifier/lean/Postern.lean`. Two
crates in one workspace:

| crate | what |
| --- | --- |
| `postern-core` | Types (`Plan`, `Policy`, `Catalog`, `Grant`) and the `rewrite` function. Byte-for-byte mirror of the Lean reference; ships nine unit tests covering happy-path, refusal, and adversarial edges. |
| `postern-diff` | Conformance-test runner. Reads the JSON corpus emitted by `lake exe postern-corpus` and asserts the Rust rewriter produces the same `Option<Plan>` (plus schema, `filter_cols`, touched relation) as the Lean spec for every case. |

`Cargo.lock` is committed because this workspace ships a binary
(`postern-diff`) and we want reproducible builds across machines and
CI.

## Run

```sh
cargo test --workspace
cargo run -p postern-diff -- corpus/postern-corpus.json
```

Expected tail:

```
N/N cases pass (Lean reference == Rust impl)
```

If the Lean spec changes, regenerate the corpus:

```sh
cd ../verifier/lean
lake exe postern-corpus > ../../prototype/corpus/postern-corpus.json
```

`scripts/reproduce.sh` at the repo root chains all of this.

## Why mirror, not extract?

We considered Lean-to-Rust extraction. The JSON-corpus path was
chosen because:

- the corpus is a stable interface across Lean and Rust compiler
  churn — extraction breaks on toolchain updates,
- divergence surfaces as a CI signal, not a build failure, so we
  can catch regressions surgically,
- the corpus is ~17 KB and reviewable by humans.

Joins, biscuit-token attenuation, and a Polars/DuckDB execution
backend are paper §6 / future work — out of scope for the verified
core today.
