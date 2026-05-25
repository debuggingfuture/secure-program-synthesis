//! `postern-datalog-diff` — Lean Datalog reference vs.
//! `biscuit_auth::datalog::World` conformance test runner.
//!
//! Companion to `postern-diff`. Reads a JSON corpus emitted by
//! `lake exe postern-datalog-corpus` and, for every case, drives
//! `postern_core::datalog::allowed` (which wraps biscuit's
//! `World`) against the same `(Program, principal, relation)`
//! input. Asserts **mem-set equality** between Rust output and
//! the Lean reference's `expected_allowed` array.
//!
//! ### Why mem-set, not list?
//!
//! Lean's `Postern.Datalog.Program.allowed` is defined as
//! `(eval P).filterMap (fun a => …)` — a `List.filterMap` over
//! the `iterate` trace. The Lean spec explicitly treats the
//! mem-set of the resulting list as the semantics:
//!
//!   * `step` is `facts ++ rules.flatMap …` — no dedup, with a
//!     comment block calling this out as deliberate ("Dedup
//!     would only complicate the monotonicity lemmas; the
//!     semantics downstream only consults `∈ eval P`",
//!     `Datalog.lean` lines 168–171).
//!   * The rewriter-side bridge `Policy.allowed` is also
//!     `flatMap`-based and preserves duplicates — see
//!     `Postern.lean` `Policy.allowed` and its companion test
//!     `duplicate_grants_flat_union`.
//!
//! Biscuit's `FactSet`, by contrast, is a `HashSet<Fact>`
//! per origin, so derived facts dedup naturally on insertion.
//! Comparing as lists would surface a known semantic gap
//! (Lean = multiset, biscuit = set) on every rule-driven case,
//! which is *not* a conformance failure — it's a deliberate
//! design choice on both sides. We therefore canonicalise both
//! arrays via sort + dedup before comparing.
//!
//! Any other mismatch — derived column appears on one side but
//! not the other, or refusal mismatch — fails the case and
//! produces a non-zero exit code. The Lean side is the source
//! of truth (its `step`/`iterate` lemmas are mechanically
//! checked); biscuit's evaluator must agree on the mem-set.
//!
//! Invocation: `postern-datalog-diff <corpus.json>` (or stdin).

use anyhow::{Context, Result};
use postern_core::datalog::{allowed, Program};
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
    program: Program,
    principal: String,
    relation: String,
    expected_allowed: Vec<String>,
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

/// Canonicalise a `Vec<String>` to a sorted, deduplicated set
/// for mem-set comparison.
fn canon(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v.dedup();
    v
}

fn check(case: &Case) -> Result<usize> {
    let got = allowed(&case.program, &case.principal, &case.relation)
        .with_context(|| format!("biscuit backend on case {}", case.name))?;

    let lean_set = canon(case.expected_allowed.clone());
    let rust_set = canon(got.clone());

    if lean_set != rust_set {
        anyhow::bail!(
            "mem-set mismatch on {} ({}, {}):\n  Lean expected: {:?}\n  Rust got:      {:?}\n  (raw Lean list of length {}, raw Rust list of length {})",
            case.name,
            case.principal,
            case.relation,
            lean_set,
            rust_set,
            case.expected_allowed.len(),
            got.len(),
        );
    }

    Ok(lean_set.len())
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
            Ok(card) => {
                println!("ok   {:>3} cols  {}", card, c.name);
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
    println!(
        "\n{passed}/{total} datalog cases pass \
         (Lean Datalog reference == biscuit_auth::datalog::World)"
    );

    if failed == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
