//! Horn-fragment Datalog programs — Rust mirror of
//! `verifier/lean/Datalog.lean`.
//!
//! The types `Term`, `Atom`, `Rule`, `Program` here are the
//! structural mirror of the Lean inductives; the function
//! `Program::allowed` is the structural mirror of Lean's
//! `Program.allowed : Program → Symbol → Symbol → List Symbol`.
//!
//! Evaluation is delegated to **`biscuit_auth::datalog::World`** —
//! the same evaluator the production token-verification surface
//! drives — feature-gated behind `datalog-biscuit` so the WASM
//! crate stays slim. The compilation step `Program → World` is
//! deliberately minimal: each fact becomes a `Fact` over a
//! shared `SymbolTable`, each rule becomes a `Rule`, and we run
//! the world to saturation, then enumerate ground
//! `right(prin, rel, c)` atoms to produce the same column list
//! Lean's `Program.allowed` produces.
//!
//! Out of scope (paper §6) and **not** modelled in this module:
//! block attenuation, audience, expiry, key rotation. We use the
//! Datalog evaluator, not the token machinery.

use serde::{Deserialize, Serialize};

/// A Datalog term — either a (typed) variable or a string constant.
///
/// Matches Lean `Term`:
///   inductive Term where
///     | var   (name  : Symbol)
///     | const (value : Symbol)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum Term {
    /// Variable; the `name` is the printed identifier (e.g. `"c"`,
    /// `"prin"`). Same variable name appearing twice in a rule
    /// body unifies as expected.
    Var {
        /// Variable name as it appears in source.
        name: String,
    },
    /// Constant string symbol.
    Const {
        /// Constant value.
        value: String,
    },
}

impl Term {
    /// Smart constructor for a variable term.
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var { name: name.into() }
    }
    /// Smart constructor for a constant term.
    pub fn cst(value: impl Into<String>) -> Self {
        Self::Const {
            value: value.into(),
        }
    }
    /// `Term.isGround` — `const`s are ground, `var`s are not.
    #[must_use]
    pub fn is_ground(&self) -> bool {
        matches!(self, Self::Const { .. })
    }
}

/// A Datalog atom — a predicate symbol plus a list of terms.
/// Matches Lean `Atom`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Atom {
    /// Predicate name (e.g. `"right"`, `"in_region"`).
    pub pred: String,
    /// Term list. The number of terms is the arity.
    pub args: Vec<Term>,
}

impl Atom {
    /// Convenience: a fully-ground atom over `String` constants
    /// (Lean's `Atom.ground`).
    pub fn ground(pred: impl Into<String>, args: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self {
            pred: pred.into(),
            args: args.into_iter().map(|s| Term::cst(s)).collect(),
        }
    }

    /// `Atom.isGround` — true iff every argument is a constant.
    #[must_use]
    pub fn is_ground(&self) -> bool {
        self.args.iter().all(Term::is_ground)
    }
}

/// A Horn clause: `head ← body₁ ∧ … ∧ bodyₙ`.
/// Matches Lean `Rule`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Rule {
    /// Rule head.
    pub head: Atom,
    /// Rule body (conjunction of atoms; possibly empty for facts,
    /// though we keep ground facts in `Program::facts` separately).
    pub body: Vec<Atom>,
}

/// A Datalog program — a fact base plus a rule set.
/// Matches Lean `Program`.
#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, Serialize, Deserialize)]
pub struct Program {
    /// Ground facts seeding the evaluation.
    pub facts: Vec<Atom>,
    /// Rules to iterate to fixpoint.
    pub rules: Vec<Rule>,
}

impl Program {
    /// Construct an empty program.
    #[must_use]
    pub fn empty() -> Self {
        Self::default()
    }
}

/// Biscuit convention: the predicate name used for column grants
/// (`right(principal, relation, column)`). Matches Lean's
/// `Postern.Datalog.RIGHT`.
pub const RIGHT_PRED: &str = "right";

/// Errors raised by the backend.
#[derive(Debug)]
pub enum DatalogError {
    /// `biscuit-auth` returned an error while running the
    /// evaluator. Surfaced as a string because biscuit's
    /// `Execution` is not `Clone` / `Eq` and we just want to
    /// propagate the failure.
    Backend(String),
    /// The atom contains a free variable in a position that
    /// should have been a constant — only valid in rule bodies
    /// and heads, not in `Program::facts`.
    NonGroundFact {
        /// Which fact tripped the check.
        atom: Atom,
    },
}

impl std::fmt::Display for DatalogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Backend(msg) => write!(f, "biscuit datalog backend: {msg}"),
            Self::NonGroundFact { atom } => {
                write!(f, "non-ground fact: {atom:?}")
            }
        }
    }
}

impl std::error::Error for DatalogError {}

// =========================================================================
// Backend — biscuit_auth::datalog::World
// =========================================================================

#[cfg(feature = "datalog-biscuit")]
mod biscuit_backend {
    //! Compile a `Program` to a `biscuit_auth::datalog::World`,
    //! run it to saturation, then enumerate `right(prin, rel, c)`
    //! ground atoms.

    use super::*;
    use biscuit_auth::datalog::{
        Fact as BFact, Origin, Predicate as BPred, Rule as BRule, SymbolTable, Term as BTerm,
        TrustedOrigins, World,
    };

    /// Compile a single `Atom` whose arguments are all `Var` or
    /// `Const` into a biscuit `Predicate`. Variables are interned
    /// into the symbol table by their printed name (matching the
    /// Lean side — same variable name = same biscuit `u32` id).
    fn compile_atom(atom: &Atom, sym: &mut SymbolTable) -> BPred {
        let name = sym.insert(&atom.pred);
        let terms: Vec<BTerm> = atom
            .args
            .iter()
            .map(|t| match t {
                Term::Const { value } => BTerm::Str(sym.insert(value)),
                Term::Var { name } => BTerm::Variable(sym.insert(name) as u32),
            })
            .collect();
        BPred::new(name, &terms)
    }

    /// `Origin` used for facts and rules originating from the
    /// (single) policy block. Convention: block id 0 ("authority"
    /// in biscuit terms). The token machinery is out of scope so
    /// every fact and rule shares the same origin.
    fn block_origin() -> Origin {
        let mut o = Origin::default();
        o.insert(0);
        o
    }

    /// `TrustedOrigins` matching `block_origin` — used as the
    /// rule scope so rules see the authority block's facts.
    fn block_scope() -> TrustedOrigins {
        TrustedOrigins::default()
    }

    /// Evaluate `program` and return the columns `prin` may
    /// read on `rel` — the mem-set of derived
    /// `right(prin, rel, c)` ground atoms.
    pub fn allowed(
        program: &Program,
        prin: &str,
        rel: &str,
    ) -> Result<Vec<String>, DatalogError> {
        // Reject non-ground facts up front: Lean's `Program.facts`
        // is `List Atom` but only ground atoms are sensible there.
        for f in &program.facts {
            if !f.is_ground() {
                return Err(DatalogError::NonGroundFact { atom: f.clone() });
            }
        }

        let mut sym = SymbolTable::new();
        let mut world = World::new();
        let origin = block_origin();
        let scope = block_scope();

        for f in &program.facts {
            let pred = compile_atom(f, &mut sym);
            world.add_fact(&origin, BFact { predicate: pred });
        }

        for r in &program.rules {
            let head = compile_atom(&r.head, &mut sym);
            let body: Vec<BPred> = r.body.iter().map(|a| compile_atom(a, &mut sym)).collect();
            let brule = BRule {
                head,
                body,
                expressions: Vec::new(),
                scopes: Vec::new(),
            };
            world.add_rule(0, &scope, brule);
        }

        world
            .run(&sym)
            .map_err(|e| DatalogError::Backend(format!("{e:?}")))?;

        // Enumerate facts. Want all `right(prin, rel, c)` where the
        // first two args match the given constants. We iterate
        // `world.facts` directly — the public surface exposes
        // `iter_all` which is exactly what we need.
        let right_idx = sym.insert(RIGHT_PRED);
        let prin_idx = sym.insert(prin);
        let rel_idx = sym.insert(rel);

        let mut out = Vec::new();
        for (_origin, fact) in world.facts.iter_all() {
            let p = &fact.predicate;
            if p.name != right_idx || p.terms.len() != 3 {
                continue;
            }
            // Match constants on positions 0 and 1; extract
            // position 2 (the column).
            let (Some(BTerm::Str(p0)), Some(BTerm::Str(p1)), Some(BTerm::Str(c))) =
                (p.terms.first(), p.terms.get(1), p.terms.get(2))
            else {
                continue;
            };
            if *p0 != prin_idx || *p1 != rel_idx {
                continue;
            }
            // Resolve symbol → string.
            let col = sym
                .get_symbol(*c)
                .ok_or_else(|| DatalogError::Backend(format!("unknown symbol {c:?}")))?
                .to_string();
            out.push(col);
        }
        Ok(out)
    }
}

/// `Program.allowed prin rel` — the columns `prin` may read on
/// `rel` according to `program`. Order is **not specified**:
/// biscuit's `FactSet` is hash-keyed by origin and contents, so
/// iteration order is intentional non-determinism. Callers that
/// need a canonical order should `sort_unstable_dedup` (a set is
/// what the Lean spec means anyway — `Program.allowed` returns a
/// `List Symbol` whose mem-set is the semantics).
///
/// **Feature-gated.** Available only with the `datalog-biscuit`
/// feature; without it this function returns a clear error so
/// callers get a deterministic compile-or-runtime failure rather
/// than silently degraded behaviour.
pub fn allowed(
    program: &Program,
    prin: &str,
    rel: &str,
) -> Result<Vec<String>, DatalogError> {
    #[cfg(feature = "datalog-biscuit")]
    {
        biscuit_backend::allowed(program, prin, rel)
    }
    #[cfg(not(feature = "datalog-biscuit"))]
    {
        let _ = (program, prin, rel);
        Err(DatalogError::Backend(
            "postern-core compiled without `datalog-biscuit` feature; \
             re-enable to use the Datalog backend"
                .to_string(),
        ))
    }
}

#[cfg(all(test, feature = "datalog-biscuit"))]
mod tests {
    use super::*;

    fn fin_inst_program() -> Program {
        Program {
            facts: vec![
                Atom::ground("right", ["CRM", "users_data", "id"]),
                Atom::ground("right", ["CRM", "users_data", "name"]),
                Atom::ground("right", ["CRM", "users_data", "region"]),
                Atom::ground("right", ["CRM", "users_data", "age"]),
                Atom::ground("right", ["FraudRisk", "users_data", "id"]),
                Atom::ground("right", ["FraudRisk", "users_data", "region"]),
            ],
            rules: vec![],
        }
    }

    #[test]
    fn ground_facts_crm_users_data() {
        let mut got = allowed(&fin_inst_program(), "CRM", "users_data").unwrap();
        got.sort();
        got.dedup();
        assert_eq!(got, vec!["age", "id", "name", "region"]);
    }

    #[test]
    fn refuses_unknown_principal() {
        let got = allowed(&fin_inst_program(), "Marketing", "users_data").unwrap();
        assert!(got.is_empty());
    }

    /// Programs with one transitive rule: `right(p,r,c) :-
    /// member(p,g), grant(g,r,c)` — the canonical Datalog test
    /// case. Stresses the LFP beyond what column-grant DSL can
    /// express.
    #[test]
    fn one_rule_transitive_right() {
        let program = Program {
            facts: vec![
                Atom::ground("member", ["Alice", "CRM"]),
                Atom::ground("grant", ["CRM", "users_data", "id"]),
                Atom::ground("grant", ["CRM", "users_data", "name"]),
            ],
            rules: vec![Rule {
                head: Atom {
                    pred: "right".into(),
                    args: vec![Term::var("p"), Term::var("r"), Term::var("c")],
                },
                body: vec![
                    Atom {
                        pred: "member".into(),
                        args: vec![Term::var("p"), Term::var("g")],
                    },
                    Atom {
                        pred: "grant".into(),
                        args: vec![Term::var("g"), Term::var("r"), Term::var("c")],
                    },
                ],
            }],
        };

        let mut got = allowed(&program, "Alice", "users_data").unwrap();
        got.sort();
        got.dedup();
        assert_eq!(got, vec!["id", "name"]);
    }
}
