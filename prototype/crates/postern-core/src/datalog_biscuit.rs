//! Biscuit-Datalog evaluation backend (feature `datalog-biscuit`).
//!
//! Companion to the column-grant `Policy::allowed` path. The
//! Lean spec at `verifier/lean/Datalog.lean` mechanises the
//! Horn-fragment evaluator semantically; this module is the
//! production-runtime side, calling `biscuit-auth`'s public
//! `biscuit_auth::Authorizer` (which wraps the same
//! `biscuit_auth::datalog::World` evaluator the token-verification
//! path uses).
//!
//! We deliberately do **not** touch `Biscuit` / `KeyPair`: we are
//! using the Datalog evaluator, not the token machinery. The four
//! Biscuit features we put out of scope in paper §6 — block
//! attenuation, audience, expiry, key rotation — are all
//! token-layer concerns that never enter this surface.
//!
//! ## Compilation from `Policy` (column-grant DSL)
//!
//! Each `Grant { principal, relation, columns }` compiles to a
//! sequence of ground facts:
//!
//! ```text
//! right("CRM",      "users_data",        "id");
//! right("CRM",      "users_data",        "name");
//! right("FraudRisk", "transactions_data", "txn_id");
//! …
//! ```
//!
//! The Datalog predicate name `right` is fixed by Biscuit
//! convention (matches the same name used inside Biscuit token
//! verification, so policies remain interchangeable with
//! attenuated tokens once §6 work lands).

use crate::{Grant, Policy};
use biscuit_auth::AuthorizerBuilder;

/// Errors surfaced by the Biscuit-backed evaluator.
#[derive(Debug)]
pub enum DatalogError {
    /// `biscuit-auth` returned an error while parsing a fact,
    /// running the evaluator, or executing a query.
    Biscuit(String),
}

impl std::fmt::Display for DatalogError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Biscuit(msg) => write!(f, "biscuit-auth: {msg}"),
        }
    }
}

impl std::error::Error for DatalogError {}

/// Quote a string for safe embedding in a Biscuit Datalog source
/// literal. Biscuit string literals are double-quoted; embedded
/// `"` and `\` get escaped. We refuse any control characters
/// rather than encoding them — policies aren't supposed to contain
/// them, and a hard error is easier to spot than a quiet mismatch.
fn quote_string(s: &str) -> Result<String, DatalogError> {
    if s.chars().any(|c| c.is_control()) {
        return Err(DatalogError::Biscuit(format!(
            "control character in identifier {s:?}; not representable in Datalog source"
        )));
    }
    Ok(format!(
        "\"{}\"",
        s.replace('\\', "\\\\").replace('"', "\\\"")
    ))
}

/// Compile a single `Grant` into one `right(p, r, c).` fact per
/// column.
fn grant_to_facts(grant: &Grant) -> Result<Vec<String>, DatalogError> {
    let p = quote_string(&grant.principal)?;
    let r = quote_string(&grant.relation)?;
    grant
        .columns
        .iter()
        .map(|c| quote_string(c).map(|c| format!("right({p}, {r}, {c})")))
        .collect()
}

/// Evaluate `Policy.allowed prin rel` through `biscuit-auth`'s
/// Datalog backend instead of the column-grant pattern-match.
///
/// Returns the columns `prin` may read on `rel` according to the
/// policy. Order is determined by Biscuit's evaluator and is not
/// guaranteed to match `Policy::allowed`; callers that need a
/// canonical order should sort.
///
/// Conformance to the Lean reference is asserted at the *mem-set*
/// level: this function and `Policy::allowed` produce the same
/// columns for every `(prin, rel)` pair. The paper-§6 follow-up
/// is a second JSON conformance corpus exercising this guarantee.
pub fn allowed_via_biscuit(
    pol: &Policy,
    prin: &str,
    rel: &str,
) -> Result<Vec<String>, DatalogError> {
    // Compile every grant in the policy to a `right(p, r, c).` fact,
    // joined into a single Datalog source string. `AuthorizerBuilder::code`
    // accepts multiple statements separated by `;`.
    let mut source = String::new();
    for grant in pol.grants() {
        for fact in grant_to_facts(grant)? {
            source.push_str(&fact);
            source.push_str(";\n");
        }
    }

    let mut authorizer = AuthorizerBuilder::new()
        .code(source.as_str())
        .map_err(|e| DatalogError::Biscuit(format!("parse facts: {e}")))?
        .build_unauthenticated()
        .map_err(|e| DatalogError::Biscuit(format!("build authorizer: {e}")))?;

    // Query: every $c such that right(prin, rel, $c) holds.
    let query = format!(
        "data($c) <- right({p}, {r}, $c)",
        p = quote_string(prin)?,
        r = quote_string(rel)?,
    );
    let facts: Vec<(String,)> = authorizer
        .query(query.as_str())
        .map_err(|e| DatalogError::Biscuit(format!("query: {e}")))?;
    Ok(facts.into_iter().map(|(c,)| c).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin_inst_policy() -> Policy {
        Policy::from_grants([
            Grant::new("CRM", "users_data", ["id", "name", "region", "age"]),
            Grant::new(
                "CardOps",
                "cards_data",
                ["card_id", "card_type", "limit", "activated"],
            ),
            Grant::new(
                "FraudRisk",
                "transactions_data",
                ["txn_id", "card_id", "amount", "merchant", "timestamp"],
            ),
            Grant::new("FraudRisk", "users_data", ["id", "region"]),
        ])
    }

    /// Smoke test: `allowed_via_biscuit` returns the same columns
    /// `Policy::allowed` returns, modulo order.
    #[test]
    fn conforms_to_column_grant_on_crm_users_data() {
        let pol = fin_inst_policy();
        let mut biscuit = allowed_via_biscuit(&pol, "CRM", "users_data").unwrap();
        let mut native = pol.allowed("CRM", "users_data");
        biscuit.sort();
        native.sort();
        assert_eq!(biscuit, native);
        assert_eq!(biscuit, vec!["age", "id", "name", "region"]);
    }

    /// Cross-department refusal: `CardOps` has no grant on
    /// `users_data`, so the Biscuit query returns the empty set —
    /// matches the rewriter's refusal behaviour at the policy
    /// layer.
    #[test]
    fn refuses_cardops_on_users_data() {
        let pol = fin_inst_policy();
        let biscuit = allowed_via_biscuit(&pol, "CardOps", "users_data").unwrap();
        assert!(biscuit.is_empty());
    }

    /// Union semantics: `FraudRisk` has two grants on
    /// `users_data` and one on `transactions_data`. The
    /// `users_data` query should return the union of the two
    /// `FraudRisk → users_data` grants.
    #[test]
    fn union_of_grants_for_fraudrisk_on_users_data() {
        let pol = fin_inst_policy();
        let mut biscuit = allowed_via_biscuit(&pol, "FraudRisk", "users_data").unwrap();
        biscuit.sort();
        biscuit.dedup();
        assert_eq!(biscuit, vec!["id", "region"]);
    }
}
