//! `postern-diff` — reference-conformance test runner.
//!
//! Reads a JSON corpus produced by `lake exe postern-corpus` (Lean
//! reference behaviour) and, for every case, runs the Rust
//! `postern_core::rewrite` against the same (catalog, policy,
//! principal, plan) input. Per-case assertions:
//!
//!   1. Rust outcome kind (`accept`/`refuse`) matches Lean's.
//!   2. On `accept`: Rust plan == Lean plan (structural), Rust
//!      schema == Lean schema, Rust filterCols == Lean filterCols,
//!      Rust touched relation == Lean touched.
//!   3. On `refuse`: Rust `rewrite` returns `None`.
//!
//! Pre-rewrite assertion (independent of the rewriter): the input
//! plan's `filter_cols` matches `expected_filter_cols`, pinning the
//! IR helper's behaviour.
//!
//! Any mismatch fails the run with a diff printed to stderr and a
//! non-zero exit code. The Lean side is the source of truth (its
//! theorems are mechanically checked); the Rust side must follow.
//!
//! Invocation: `postern-diff <corpus.json>` (or stdin if no path).

use anyhow::{Context, Result};
use postern_core::{rewrite, Catalog, Plan, Policy};
use serde::Deserialize;
use std::env;
use std::fs;
use std::io::Read;
use std::process::ExitCode;

#[derive(Debug, Deserialize)]
struct Case {
    name: String,
    #[serde(default)]
    note: String,
    principal: String,
    catalog: Catalog,
    policy: Policy,
    plan: Plan,
    expected_filter_cols: Vec<String>,
    expected_outcome: Outcome,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum Outcome {
    Accept {
        rewrite: Plan,
        schema: Vec<String>,
        #[serde(rename = "filterCols")]
        filter_cols: Vec<String>,
        touched: String,
    },
    Refuse {},
}

fn load_corpus(path: Option<&str>) -> Result<Vec<Case>> {
    let raw = match path {
        Some(p) => fs::read_to_string(p).with_context(|| format!("reading corpus {p}"))?,
        None => {
            let mut buf = String::new();
            std::io::stdin().read_to_string(&mut buf)?;
            buf
        }
    };
    serde_json::from_str(&raw).context("parsing corpus JSON")
}

fn check(case: &Case) -> Result<()> {
    // Pre-rewrite: filter_cols matches Lean's reference.
    let rust_filter_cols = case.plan.filter_cols();
    if rust_filter_cols != case.expected_filter_cols {
        anyhow::bail!(
            "filter_cols mismatch on input plan: expected {:?}, got {:?}",
            case.expected_filter_cols,
            rust_filter_cols,
        );
    }

    let rw = rewrite(&case.catalog, &case.policy, &case.principal, &case.plan);

    match (&rw, &case.expected_outcome) {
        (None, Outcome::Refuse {}) => Ok(()),

        (Some(_), Outcome::Refuse {}) => anyhow::bail!(
            "outcome mismatch: expected refuse, Rust returned accept ({})",
            serde_json::to_string(rw.as_ref().unwrap())?,
        ),

        (None, Outcome::Accept { .. }) => {
            anyhow::bail!("outcome mismatch: expected accept, Rust refused")
        }

        (
            Some(plan),
            Outcome::Accept {
                rewrite: ref_plan,
                schema: ref_schema,
                filter_cols: ref_fcols,
                touched: ref_touched,
            },
        ) => {
            if plan != ref_plan {
                anyhow::bail!(
                    "plan mismatch:\n  expected: {}\n  got:      {}",
                    serde_json::to_string(ref_plan)?,
                    serde_json::to_string(plan)?,
                );
            }
            let schema = plan.schema(&case.catalog);
            if schema != *ref_schema {
                anyhow::bail!(
                    "schema mismatch: expected {:?}, got {:?}",
                    ref_schema,
                    schema
                );
            }
            let fcols = plan.filter_cols();
            if fcols != *ref_fcols {
                anyhow::bail!(
                    "rewritten filter_cols mismatch: expected {:?}, got {:?}",
                    ref_fcols,
                    fcols
                );
            }
            if plan.touched() != ref_touched {
                anyhow::bail!(
                    "touched mismatch: expected {}, got {}",
                    ref_touched,
                    plan.touched(),
                );
            }
            Ok(())
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    let path = args.get(1).map(String::as_str);

    let cases = match load_corpus(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: {e:#}");
            return ExitCode::from(2);
        }
    };

    let mut failed = 0usize;
    for c in &cases {
        match check(c) {
            Ok(()) => {
                let outcome = match &c.expected_outcome {
                    Outcome::Accept { .. } => "accept",
                    Outcome::Refuse {} => "refuse",
                };
                println!("ok   {:<8} {}", outcome, c.name);
            }
            Err(e) => {
                println!("FAIL          {}", c.name);
                eprintln!("  note: {}", c.note);
                eprintln!("  {e:#}");
                failed += 1;
            }
        }
    }

    let total = cases.len();
    let passed = total - failed;
    println!("\n{passed}/{total} cases pass (Lean reference == Rust impl)");

    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
