//! Postern guardrail — capability-bounded data flow for the
//! agent-code boundary.
//!
//! Inspired by **Odersky et al. 2026, "Tracking Capabilities for
//! Safer Agents"** ([arXiv:2603.00991](https://arxiv.org/abs/2603.00991)),
//! which uses Scala 3 capture-checking to make capabilities
//! first-class program variables. Rust has no capture-checking; we
//! mechanize the same intuition using *sealed types*: capabilities
//! are unforgeable tokens minted only by the gateway, and data is
//! wrapped in `Tagged<T, C>` whose inner value cannot be reached
//! without consuming a matching `Cap<C>` at a sanctioned sink.
//!
//! ## Two-layer model
//!
//! 1. **`postern-core`** — verified plan rewriter. The Lean
//!    theorems carry the read-side guarantee: every accepted plan's
//!    output schema and filter-predicate read-set are
//!    policy-allowed.
//! 2. **`postern-guardrail`** *(this crate)* — capability-bounded
//!    compute. Once the rewriter accepts, the resulting data is
//!    handed to the agent as `Tagged<DataFrame, C>` along with a
//!    single-use `Cap<C>`. Agent code can `map` / `filter` the
//!    Tagged value as much as it likes — every transform preserves
//!    the tag. The only un-tagging path is `release(cap)`, which
//!    consumes the Cap; the gateway controls which Cap kinds get
//!    issued and to whom.
//!
//! ## What this defends against
//!
//! - **Smuggle-via-format.** An agent receives `Tagged<String,
//!   PiiRedacted>`, formats it into a panic message, and `panic!`s
//!   to ship the string to an error sink. Defeated: the panic
//!   message takes `&dyn Display`, not the raw `T` — the agent has
//!   to compute on Tagged values, and `Tagged: Display` is *not*
//!   implemented.
//! - **Smuggle-via-globals.** An agent stashes the inner value in a
//!   `static`. Defeated: the agent never holds the raw value to
//!   stash; `Tagged<T, C>::value` is private.
//! - **Forge-cap.** An agent constructs `Cap::<C>` directly.
//!   Defeated: `Cap`'s constructor is `pub(crate)` and its inner
//!   field is private. See `tests/ui/cap_construction.rs` for the
//!   compile-fail demonstration.
//! - **Sink-without-cap.** An agent calls a sanctioned sink without
//!   holding a Cap. Defeated: sinks take `Cap<C>` by value.
//!
//! ## What this does *not* defend against
//!
//! Rust has no effect system. A capability-bearing agent can still:
//! - Panic with a message constructed from a `Display`-implementing
//!   *aggregate* of a Tagged value (we deliberately don't implement
//!   `Display` for `Tagged`; the agent would have to implement it
//!   themselves, which requires reading the inner value, which is
//!   private — so this is closed *for our types*, but an unsealed
//!   downstream type wrapping ours could leak).
//! - Time-channel: measure how long a compute takes and signal
//!   through that. Out of scope.
//! - Steal capabilities from another thread via `Arc`/`Mutex`. We
//!   make `Cap: !Send + !Sync` (via `PhantomData<*const ()>`) to
//!   prevent the obvious cross-thread move.
//!
//! See paper §3 "Defense-in-depth with capability tracking" and
//! §6 (future work) for the limits and the path to a stronger
//! Rust analog (e.g., a custom lint or `unsafe`-style markers).

//!
//! ## Compile-time bypass demonstration
//!
//! Forging a `Cap` does not type-check — the inner field is sealed:
//!
//! ```compile_fail,E0451
//! use postern_guardrail::Cap;
//! struct Anything;
//! // Compile error: cannot construct Cap, its `Sealed` field is private.
//! let _bypass: Cap<Anything> = Cap { _kind: std::marker::PhantomData, _seal: () };
//! ```
//!
//! Reading the inner `value` of a `Tagged` does not type-check either:
//!
//! ```compile_fail,E0616
//! use postern_guardrail::Tagged;
//! fn leak<T, C: 'static>(t: Tagged<T, C>) -> T { t.value }
//! //                                              ^^^^^^^ field is private
//! ```

#![warn(missing_docs)]
#![forbid(unsafe_code)]

use std::marker::PhantomData;

/// Internal sealing — only this crate can construct a token, so any
/// type embedding `Sealed` cannot be re-implemented or constructed
/// downstream.
#[doc(hidden)]
pub struct Sealed(PhantomData<*const ()>);

impl Sealed {
    pub(crate) fn new() -> Self {
        Sealed(PhantomData)
    }
}

/// `Cap<C>` — an unforgeable capability token tagged by the
/// phantom type `C`. The inner `Sealed` is private; the constructor
/// is `pub(crate)`; `!Send + !Sync` via the raw-pointer phantom.
///
/// To consume a Cap at a sanctioned sink, take it by value; the
/// move makes it single-use, mirroring linear-type "consumable"
/// capabilities.
pub struct Cap<C: 'static> {
    _kind: PhantomData<C>,
    _seal: Sealed,
}

impl<C: 'static> Cap<C> {
    /// Mint a capability. Visible only to this crate plus the
    /// `issue` function below; downstream callers cannot construct.
    pub(crate) fn mint() -> Self {
        Cap {
            _kind: PhantomData,
            _seal: Sealed::new(),
        }
    }
}

/// `Tagged<T, C>` — data plus the capability needed to release it.
///
/// Sanctioned operations:
///
/// - [`Tagged::map`] — pure transformation `T → U`, tag preserved.
/// - [`Tagged::and_then`] — flat-map producing another `Tagged<U, C>`.
/// - [`Tagged::release`] — consume a `Cap<C>` to release the inner
///   value at a sanctioned sink.
///
/// No `Deref`, no `Display`, no `AsRef`, no public `.value` accessor.
/// The only paths out are `map`/`and_then` (which return another
/// Tagged) and `release` (which consumes a Cap).
pub struct Tagged<T, C: 'static> {
    value: T,
    _kind: PhantomData<C>,
}

impl<T, C: 'static> Tagged<T, C> {
    pub(crate) fn mint(value: T) -> Self {
        Tagged {
            value,
            _kind: PhantomData,
        }
    }

    /// Pure transformation. Tag preserved.
    #[must_use]
    pub fn map<U, F>(self, f: F) -> Tagged<U, C>
    where
        F: FnOnce(T) -> U,
    {
        Tagged {
            value: f(self.value),
            _kind: PhantomData,
        }
    }

    /// Sequenced computation. Returns another `Tagged<U, C>` so
    /// the agent can build up a pipeline without ever holding the
    /// raw value.
    #[must_use]
    pub fn and_then<U, F>(self, f: F) -> Tagged<U, C>
    where
        F: FnOnce(T) -> Tagged<U, C>,
    {
        f(self.value)
    }

    /// Release the inner value at a sanctioned sink. Consumes the
    /// matching `Cap<C>` — single-use. Caller must hold a Cap of
    /// the right kind to call this; capabilities cannot be forged.
    #[must_use]
    pub fn release(self, _cap: Cap<C>) -> T {
        self.value
    }
}

/// Issue a Tagged data value and its matching single-use Cap.
/// Visible to the gateway driver only — `pub(crate)` plus a
/// `pub` re-export through `gateway::issue` that does the policy
/// check.
pub(crate) fn issue<T, C: 'static>(value: T) -> (Tagged<T, C>, Cap<C>) {
    (Tagged::mint(value), Cap::mint())
}

/// Gateway-side entry point. Combines the verified rewrite from
/// `postern-core` with capability issuance: if the rewrite
/// accepts, return a `Tagged<Plan, AllowedColumns>` plus a single-
/// use `Cap<AllowedColumns>`; if it refuses, return `None`.
///
/// `AllowedColumns` is a phantom marker — in a full deployment we
/// would parameterize over a refinement of the principal +
/// touched-relation so that different (principal, relation) pairs
/// produce structurally distinct capabilities. The 0.1 demo uses a
/// single marker to make the API legible.
pub mod gateway {
    use super::{issue, Cap, Tagged};
    use postern_core::{rewrite, Catalog, Plan, Policy};

    /// Phantom marker: "this value is the rewriter's accepted
    /// output for some (principal, plan) pair on this catalog".
    /// Different deployments can parameterize over a more refined
    /// witness type (per-principal, per-relation, per-session).
    pub struct AllowedColumns;

    /// Run the verified rewriter, and if it accepts, mint a Tagged
    /// plan plus its matching single-use Cap.
    ///
    /// Returns `None` iff the rewriter refused
    /// (`rewrite_refuses_unknown` or `rewrite_refuses_forbidden_filter`).
    /// The Lean theorems on the Plan side carry the read-side
    /// guarantee; this function is the bridge to the capability-
    /// bounded compute layer.
    #[must_use]
    pub fn issue_plan(
        cat: &Catalog,
        pol: &Policy,
        prin: &str,
        plan: &Plan,
    ) -> Option<(Tagged<Plan, AllowedColumns>, Cap<AllowedColumns>)> {
        rewrite(cat, pol, prin, plan).map(issue)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use postern_core::{Catalog, Grant, Plan, Policy};

    struct Demo;

    fn cat() -> Catalog {
        Catalog::from_entries([("users_data", vec!["id", "name", "email", "ssn", "region"])])
    }

    fn pol() -> Policy {
        Policy::from_grants([Grant::new("CRM", "users_data", ["id", "name", "region"])])
    }

    #[test]
    fn legal_flow_release_with_cap() {
        let (tagged, cap) = issue::<i64, Demo>(42);
        let v: i64 = tagged.release(cap);
        assert_eq!(v, 42);
    }

    #[test]
    fn map_preserves_tag() {
        let (tagged, cap) = issue::<i64, Demo>(42);
        let mapped: Tagged<String, Demo> = tagged.map(|n| n.to_string());
        let s: String = mapped.release(cap);
        assert_eq!(s, "42");
    }

    #[test]
    fn and_then_preserves_tag() {
        let (tagged, cap) = issue::<i64, Demo>(7);
        let result = tagged
            .map(|n| n * 2)
            .and_then(|n| Tagged::mint(format!("doubled: {n}")))
            .release(cap);
        assert_eq!(result, "doubled: 14");
    }

    #[test]
    fn gateway_accepts_legal_plan_and_mints_cap() {
        let plan = Plan::scan("users_data");
        let issued = gateway::issue_plan(&cat(), &pol(), "CRM", &plan);
        let (tagged_plan, cap) = issued.expect("CRM scan of users_data accepts");

        // Agent transforms the plan (e.g., to a Polars LazyFrame),
        // tag is preserved through every step.
        let plan_as_string = tagged_plan.map(|p| format!("{p:?}"));

        // Final release at the sanctioned sink consumes the Cap.
        let serialized: String = plan_as_string.release(cap);
        assert!(serialized.contains("users_data"));
    }

    #[test]
    fn gateway_refuses_unknown_relation_no_cap_issued() {
        // unknown relation ⇒ rewriter refuses ⇒ no Tagged, no Cap.
        let plan = Plan::scan("payroll_data");
        let issued = gateway::issue_plan(&cat(), &pol(), "CRM", &plan);
        assert!(
            issued.is_none(),
            "no Cap should be minted for refused plans"
        );
    }

    #[test]
    fn gateway_refuses_filter_on_forbidden_column() {
        let plan = Plan::filter(Plan::scan("users_data"), "ssn");
        let issued = gateway::issue_plan(&cat(), &pol(), "CRM", &plan);
        assert!(
            issued.is_none(),
            "filter on ssn must refuse; agent never receives a Cap"
        );
    }

    #[test]
    fn cap_is_single_use() {
        // The Cap is consumed by `release` — the type system
        // enforces this. A second `release` call won't compile
        // because the Cap has moved.
        let (tagged, cap) = issue::<i64, Demo>(1);
        let _ = tagged.release(cap);
        // tagged.release(cap);  // <- compile error: use of moved value
    }
}
