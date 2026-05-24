//! `postern-diff` — differential test runner.
//!
//! Reads a JSON corpus produced by `lake exe postern-corpus` (Lean
//! reference behaviour) and, for every case, runs the Rust
//! `postern_core::rewrite` against the same (catalog, policy,
//! principal, plan) input. Three equalities are asserted per case:
//!
//!   1. `rust_rewrite == expected_rewrite`         (structural plan eq)
//!   2. `rust_rewrite.schema(cat) == expected_schema`
//!   3. `rust_rewrite.touched() == expected_touched`
//!
//! Any mismatch fails the run with a diff printed to stderr and a
//! non-zero exit code, so CI can gate on it. The Lean side is the
//! source of truth (its `rewrite_sound` theorem is mechanically
//! checked); the Rust side has to follow.
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
    principal: String,
    catalog: Catalog,
    policy: Policy,
    plan: Plan,
    expected_rewrite: Plan,
    expected_schema: Vec<String>,
    expected_touched: String,
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
    let rw = rewrite(&case.catalog, &case.policy, &case.principal, &case.plan);

    if rw != case.expected_rewrite {
        anyhow::bail!(
            "plan mismatch:\n  expected: {}\n  got:      {}",
            serde_json::to_string(&case.expected_rewrite)?,
            serde_json::to_string(&rw)?,
        );
    }

    let schema = rw.schema(&case.catalog);
    if schema != case.expected_schema {
        anyhow::bail!(
            "schema mismatch: expected {:?}, got {:?}",
            case.expected_schema,
            schema,
        );
    }

    if rw.touched() != &case.expected_touched {
        anyhow::bail!(
            "touched mismatch: expected {}, got {}",
            case.expected_touched,
            rw.touched(),
        );
    }

    Ok(())
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
            Ok(()) => println!("ok   {}", c.name),
            Err(e) => {
                println!("FAIL {}", c.name);
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
