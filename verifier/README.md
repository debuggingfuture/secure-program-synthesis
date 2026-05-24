# Postern — Lean 4 verifier

Single-file Lean 4 artifact (`Postern.lean`) with the policy DSL,
Plan IR, and rewriter, plus all soundness theorems. Pinned to
Lean 4.29.1 (see `lean-toolchain`). No Mathlib.

| file | what |
| --- | --- |
| `Postern.lean` | Types and nine theorems. All `sorry`-free. |
| `CheckAxioms.lean` | `#print axioms` audit of every load-bearing theorem. |
| `Main.lean` | `postern-corpus` executable — emits the JSON conformance corpus. |
| `lakefile.toml` | Build config. |
| `lean-toolchain` | Lean version pin (4.29.1). |

## Theorems

| name | claim |
| --- | --- |
| `rewrite_touched` | `rewrite cat P p q = some q' ⇒ q'.touched = q.touched` |
| `rewrite_schema_subset` | output schema ⊆ input schema |
| `rewrite_sound` | every output column is policy-allowed for `p` on `q.touched` |
| `rewrite_filter_sound` | every column read by a `Filter` predicate is policy-allowed |
| `rewrite_no_new_columns` | contrapositive of schema-subset |
| `rewrite_idempotent` | a second rewrite admits the same column set |
| `rewrite_monotone` | strengthening the policy can only widen the output |
| `rewrite_refuses_unknown` | `cat q.touched = []` ⇒ refusal |
| `rewrite_refuses_forbidden_filter` | filter on a forbidden col ⇒ refusal |

## Run

```sh
lake build                 # builds Postern + CheckAxioms, runs #print axioms
lake exe postern-corpus    # emits the conformance corpus to stdout
```

The build log shows the axiom dependencies of every theorem; only
Lean's built-in `propext` and `Quot.sound` appear, no user-supplied
axioms and no `sorry`.

## Why these proofs?

The headline theorem is `rewrite_sound` (output-column soundness).
The reviewer-driven additions of `rewrite_filter_sound` and the two
`rewrite_refuses_*` lemmas close two real attack shapes that earlier
drafts left to "out of scope":

- A principal who cannot *read* `ssn` was previously able to use it
  as a `WHERE` predicate without ever projecting it (filter side-
  channel). `rewrite_filter_sound` plus
  `rewrite_refuses_forbidden_filter` make this impossible.
- A relation present in physical storage but absent from the
  catalog previously yielded an empty *schema* — silently vacuous
  if the executor resolves the scan against real Parquet.
  `rewrite_refuses_unknown` flips this to an explicit refusal.

`rewrite_idempotent` and `rewrite_monotone` are sanity-check
theorems that strengthen reviewer confidence at low marginal cost.
