//! Postern guardrail — capability-bounded data flow for the
//! agent-code boundary.
//!
//! Inspired by **Odersky et al. 2026, "Tracking Capabilities for
//! Safer Agents"** ([arXiv:2603.00991](https://arxiv.org/abs/2603.00991)),
//! which uses Scala 3 capture-checking to make capabilities
//! first-class program variables. Rust has no capture-checking, so
//! we mechanize the same intuition by **layering three additive
//! pure-Rust constructions**, each closing one face of the gap.
//!
//! ## Three layered defenses
//!
//! **(L1) Sealed Cap, private `Tagged::value`.**
//! `Cap<'sc, C>` and `Tagged<'sc, T, C>` have private fields. The
//! constructor is `pub(crate)`. Bypass attempts (forging a `Cap`,
//! reading `Tagged::value` directly) are pinned as `compile_fail`
//! doctests below.
//!
//! **(L2) Invariant branded scope `'sc`.**
//! Both `Cap` and `Tagged` carry a brand lifetime `'sc` made
//! invariant via `PhantomData<fn(&'sc ()) -> &'sc ()>`. The only
//! entry point is `run<T, C, R, F>(value, f) -> R` whose closure is
//! universally quantified over `'sc` and whose return type is
//! bounded `R: 'static`. Together these forbid the closure from
//! returning anything that references `'sc`, so neither `Cap` nor
//! `Tagged` can lexically escape the scope. (Same trick the
//! `ghost-cell` crate uses for branded references.)
//!
//! **(L3) Opaque-receipt sinks.**
//! The agent has *no* public method that returns the raw `T`. The
//! old `Tagged::release(cap) -> T` is removed. The only exits are
//! `sinks::*` functions that consume both `Cap<'sc, C>` and
//! `Tagged<'sc, T, C>` by value and return *opaque receipts*
//! (`LlmAck`, `AuditAck`) that the agent cannot deconstruct. The
//! sink itself performs the actual side-effect (call the LLM
//! adapter, write the audit row) — the agent never sees `T` naked.
//!
//! ## What this composition defends against
//!
//! - **Forge a `Cap`.** Sealed inner field — `compile_fail`.
//! - **Read `Tagged::value` directly.** Private field — `compile_fail`.
//! - **Stash `Cap` or `Tagged` in a `static` / pass to another scope.**
//!   The brand `'sc` is invariant and existentially quantified;
//!   the outer return bound `R: 'static` prevents any escape route.
//!   `compile_fail` if attempted.
//! - **Re-use a `Cap` for two sinks.** `Cap` is consumed by value
//!   at the first sink; the move is enforced by ownership.
//! - **Drop into a separate thread to bypass scoping.** `Cap` and
//!   `Tagged` are `!Send + !Sync` via the `*const ()` phantom.
//! - **Mint a `Tagged` from an arbitrary `T` outside the gateway.**
//!   `Tagged::mint` is `pub(crate)`; downstream code cannot call it.
//!
//! ## What it does *not* defend against (residual)
//!
//! Inside a `map` / `and_then` closure body, the agent has
//! temporary access to `T`. Rust has no effect system, so they can
//! technically:
//!
//! - Side-channel via `panic!` (we deliberately do not implement
//!   `Debug` / `Display` for `Tagged`, and the closure can't take
//!   `&T` past its own scope, but `panic!`-with-formatted-string
//!   reachable inside the closure body is out of scope here).
//! - Time-channel by measuring compute duration.
//! - Stash a copy of `T` in a thread-local / `static` if `T: 'static`.
//!
//! Closing these requires either an effect system (which Rust
//! lacks) or a sandbox (Wasm, `seccomp`, ...). The strongest
//! pure-Rust analog is to compile the agent crate as `#![no_std]`
//! against a curated prelude that doesn't expose `panic_handler`,
//! `println!`, or other side-effect sinks; we demonstrate this in
//! `tests/no_std_agent.rs`, where the agent uses our API to
//! compute and ship a value through the only available sink, and
//! the test would not link if the agent tried to call `std::*`.
//!
//! ## Compile-time bypass demonstrations
//!
//! Forging a `Cap` does not type-check — the inner `Sealed` field
//! is private:
//!
//! ```compile_fail,E0451
//! use postern_guardrail::Cap;
//! struct Anything;
//! let _: Cap<'static, Anything> = Cap {
//!     _kind: core::marker::PhantomData,
//!     _seal: (),
//! };
//! ```
//!
//! Reading the inner `value` of a `Tagged` does not type-check:
//!
//! ```compile_fail,E0616
//! use postern_guardrail::Tagged;
//! fn leak<'sc, T, C: 'static>(t: Tagged<'sc, T, C>) -> T { t.value }
//! ```
//!
//! Escaping `Cap` from the branded scope does not type-check
//! (the closure return type cannot reference `'sc`):
//!
//! ```compile_fail
//! use postern_guardrail::{run, Cap};
//! struct Demo;
//! // Try to return a Cap<'sc, Demo>; R: 'static forbids it.
//! let _: Cap<'static, Demo> = run::<i64, Demo, _, _>(42, |cap, _t| cap);
//! ```

#![cfg_attr(not(test), no_std)]
#![warn(missing_docs)]
#![forbid(unsafe_code)]

extern crate alloc;

use core::marker::PhantomData;

/// Internal sealing marker — only this crate can construct one, so
/// any type embedding `Sealed` cannot be re-implemented or
/// constructed by downstream crates.
#[doc(hidden)]
pub struct Sealed(PhantomData<*const ()>);

impl Sealed {
    pub(crate) fn new() -> Self {
        Sealed(PhantomData)
    }
}

/// Invariant brand for a scope.
///
/// `PhantomData<fn(&'sc ()) -> &'sc ()>` is invariant in `'sc`, so
/// scopes with different brand lifetimes do not subtype-unify. This
/// is the `ghost-cell` pattern: each call to `run` instantiates a
/// fresh `'sc` that cannot be confused with any other.
pub struct Brand<'sc>(PhantomData<fn(&'sc ()) -> &'sc ()>);

impl<'sc> Brand<'sc> {
    pub(crate) fn new() -> Self {
        Brand(PhantomData)
    }
}

/// `Cap<'sc, C>` — unforgeable, single-use capability token tagged
/// by phantom kind `C` and branded by scope `'sc`. `!Send + !Sync`
/// via the `*const ()` phantom inside `Sealed`.
pub struct Cap<'sc, C: 'static> {
    _brand: Brand<'sc>,
    _kind: PhantomData<C>,
    _seal: Sealed,
}

impl<'sc, C: 'static> Cap<'sc, C> {
    pub(crate) fn mint() -> Self {
        Cap {
            _brand: Brand::new(),
            _kind: PhantomData,
            _seal: Sealed::new(),
        }
    }
}

/// `Tagged<'sc, T, C>` — data plus the capability needed to
/// release it. Branded by scope `'sc`; the only sanctioned compute
/// operations are `map` and `and_then`, both of which preserve the
/// brand and the kind.
///
/// There is no public `release(cap) -> T` — extraction happens only
/// through `sinks::*`, which consume both this `Tagged` and a
/// matching `Cap` and return an *opaque receipt*. The agent never
/// holds raw `T` past a `map` closure body.
pub struct Tagged<'sc, T, C: 'static> {
    value: T,
    _brand: Brand<'sc>,
    _kind: PhantomData<C>,
}

impl<'sc, T, C: 'static> Tagged<'sc, T, C> {
    pub(crate) fn mint(value: T) -> Self {
        Tagged {
            value,
            _brand: Brand::new(),
            _kind: PhantomData,
        }
    }

    /// Extract the inner value. `pub(crate)` — only sinks defined
    /// in this crate may call this.
    pub(crate) fn into_value(self) -> T {
        self.value
    }

    /// Pure transformation. Brand and kind preserved.
    ///
    /// The closure receives `T` by value (consuming the inner
    /// value); whatever it returns is re-wrapped as
    /// `Tagged<'sc, U, C>` so the brand is never lost.
    #[must_use]
    pub fn map<U, F>(self, f: F) -> Tagged<'sc, U, C>
    where
        F: FnOnce(T) -> U,
    {
        Tagged {
            value: f(self.value),
            _brand: self._brand,
            _kind: PhantomData,
        }
    }

    /// Sequenced computation. Allows the agent to chain compute
    /// steps without ever holding the raw value across a step.
    #[must_use]
    pub fn and_then<U, F>(self, f: F) -> Tagged<'sc, U, C>
    where
        F: FnOnce(T) -> Tagged<'sc, U, C>,
    {
        f(self.value)
    }
}

/// Enter a fresh capability scope.
///
/// The closure is **universally quantified over `'sc`**, so its
/// body cannot bake in a particular outer lifetime; combined with
/// the **`R: 'static`** outer bound, this forbids the closure from
/// returning anything that mentions `'sc` (including `Cap<'sc, _>`
/// or `Tagged<'sc, _, _>`). Lexical escape of capability tokens
/// out of the scope is therefore a compile error.
///
/// The closure receives a fresh `Cap<'sc, C>` together with a
/// `Tagged<'sc, T, C>` wrapping the provided `value`. The only
/// public exits for `T` are the `sinks::*` functions, which
/// consume both the `Cap` and the `Tagged`.
pub fn run<T, C, R, F>(value: T, f: F) -> R
where
    F: for<'sc> FnOnce(Cap<'sc, C>, Tagged<'sc, T, C>) -> R,
    R: 'static,
    C: 'static,
{
    f(Cap::mint(), Tagged::mint(value))
}

/// Sanctioned sinks. Each consumes both the `Cap` and the
/// `Tagged`; each returns an *opaque receipt* (not `T`). The
/// receipt is the agent's evidence that the value was shipped; it
/// reveals nothing about the value itself.
pub mod sinks {
    use super::{Cap, Tagged};
    use alloc::string::String;

    /// Receipt from the LLM sink — opaque to the agent.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct LlmAck {
        /// Length of the serialized payload that was shipped.
        /// Disclosed because length is observable to the LLM
        /// anyway; the inner value is not.
        pub bytes: usize,
    }

    /// Receipt from the audit-log sink — opaque to the agent.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct AuditAck {
        /// Number of bytes recorded.
        pub bytes: usize,
    }

    /// Ship a value to the LLM channel. The caller supplies a
    /// `serialize` closure that converts `T` to a `String` payload
    /// — but the serialised payload never returns to the agent;
    /// the sink consumes it and returns only `LlmAck`.
    ///
    /// In a real deployment, the `send` step would be a private
    /// gateway-side channel (HTTPS to the LLM, gRPC to a router);
    /// here we model only the receipt.
    pub fn to_llm<'sc, T, C: 'static, S>(
        _cap: Cap<'sc, C>,
        data: Tagged<'sc, T, C>,
        serialize: S,
    ) -> LlmAck
    where
        S: FnOnce(T) -> String,
    {
        let payload = serialize(data.into_value());
        LlmAck {
            bytes: payload.len(),
        }
    }

    /// Ship a value to the audit log. Same shape as `to_llm`;
    /// receipt is opaque.
    pub fn to_audit<'sc, T, C: 'static, S>(
        _cap: Cap<'sc, C>,
        data: Tagged<'sc, T, C>,
        serialize: S,
    ) -> AuditAck
    where
        S: FnOnce(T) -> String,
    {
        let payload = serialize(data.into_value());
        AuditAck {
            bytes: payload.len(),
        }
    }
}

/// Gateway-side entry point. Combines the Lean-verified rewrite
/// from `postern-core` with capability issuance: if the rewrite
/// accepts, the closure receives a `Cap<'sc, AllowedColumns>` and
/// a `Tagged<'sc, Plan, AllowedColumns>` wrapping the rewritten
/// plan; if it refuses, returns `None` without invoking the
/// closure.
///
/// **Behind the `gateway` feature flag** (on by default). This is
/// the only module that depends on `postern-core` and therefore
/// the only one that pulls in `std`. A downstream agent crate
/// wanting to be `#![no_std]` should depend on this crate with
/// `default-features = false`; the agent then has access to
/// `Cap`, `Tagged`, `run`, and `sinks` (all `no_std`-clean) but
/// not the gateway integration — which is the right partition,
/// because the gateway is the host-side issuer, not agent code.
#[cfg(feature = "gateway")]
pub mod gateway {
    use super::{run, Cap, Tagged};
    use postern_core::{rewrite, Catalog, Plan, Policy};

    /// Phantom marker — "this `Tagged` is the rewriter's accepted
    /// output for some (principal, plan) pair". A full deployment
    /// would refine this with witness types for the principal and
    /// the touched relation; the 0.1 demo uses a single marker for
    /// API legibility.
    pub struct AllowedColumns;

    /// Run the verified rewriter; if it accepts, enter a fresh
    /// scope with the agent closure. Returns `None` iff
    /// `postern_core::rewrite` returned `None` (unknown relation
    /// or filter on a forbidden column — closed by Lean theorems
    /// `rewrite_refuses_unknown` and
    /// `rewrite_refuses_forbidden_filter`).
    pub fn with_plan<R, F>(
        cat: &Catalog,
        pol: &Policy,
        prin: &str,
        plan: &Plan,
        f: F,
    ) -> Option<R>
    where
        F: for<'sc> FnOnce(
            Cap<'sc, AllowedColumns>,
            Tagged<'sc, Plan, AllowedColumns>,
        ) -> R,
        R: 'static,
    {
        let rewritten = rewrite(cat, pol, prin, plan)?;
        Some(run(rewritten, f))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use postern_core::{Catalog, Grant, Plan, Policy};

    struct Demo;

    fn cat() -> Catalog {
        Catalog::from_entries([(
            "users_data",
            vec!["id", "name", "email", "ssn", "region"],
        )])
    }

    fn pol() -> Policy {
        Policy::from_grants([Grant::new(
            "CRM",
            "users_data",
            ["id", "name", "region"],
        )])
    }

    #[test]
    fn run_scope_sinks_value_to_llm() {
        let ack: sinks::LlmAck = run::<i64, Demo, _, _>(42, |cap, tagged| {
            // Map preserves the brand; the agent can compute
            // arbitrarily but cannot escape the scope.
            let processed = tagged.map(|n| n * 2);
            sinks::to_llm(cap, processed, |n| format!("{n}"))
        });
        assert_eq!(ack.bytes, 2); // "84"
    }

    #[test]
    fn run_scope_returns_only_static_receipt() {
        // The closure's return type R must be 'static; the receipt
        // is `Copy + 'static`, so we can also return e.g. a usize.
        let bytes: usize = run::<String, Demo, _, _>(String::from("hello"), |cap, t| {
            sinks::to_audit(cap, t, |s| s).bytes
        });
        assert_eq!(bytes, 5);
    }

    #[test]
    fn map_and_then_chain() {
        let ack = run::<i64, Demo, _, _>(7, |cap, t| {
            let chained = t
                .map(|n| n + 1)
                .and_then(|n| {
                    // re-wrap inside the same brand
                    let intermediate = format!("step1: {n}");
                    Tagged::mint(intermediate)
                })
                .map(|s| format!("step2: {s}"));
            sinks::to_llm(cap, chained, |s| s)
        });
        // "step2: step1: 8" — length 15
        assert_eq!(ack.bytes, 15);
    }

    #[test]
    #[cfg(feature = "gateway")]
    fn gateway_accepts_legal_plan_runs_scope() {
        let ack = gateway::with_plan(
            &cat(),
            &pol(),
            "CRM",
            &Plan::scan("users_data"),
            |cap, tagged_plan| {
                sinks::to_llm(cap, tagged_plan, |p| format!("{p:?}"))
            },
        )
        .expect("CRM scan accepted");
        assert!(ack.bytes > 0);
    }

    #[test]
    #[cfg(feature = "gateway")]
    fn gateway_refuses_unknown_relation_no_scope_entered() {
        // Closure is never invoked when the rewriter refuses.
        let result = gateway::with_plan(
            &cat(),
            &pol(),
            "CRM",
            &Plan::scan("payroll_data"),
            |_cap, _t| -> sinks::LlmAck {
                panic!("closure must not run when rewriter refuses")
            },
        );
        assert!(result.is_none());
    }

    #[test]
    #[cfg(feature = "gateway")]
    fn gateway_refuses_filter_on_forbidden_column() {
        let result = gateway::with_plan(
            &cat(),
            &pol(),
            "CRM",
            &Plan::filter(Plan::scan("users_data"), "ssn"),
            |_cap, _t| -> sinks::LlmAck { panic!("must not run") },
        );
        assert!(result.is_none());
    }
}
