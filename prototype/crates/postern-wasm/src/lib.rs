//! Postern WASM surface — minimum bindings the Astro demo needs.
//!
//! Exposes a single function `rewrite_plan(request)` that takes a
//! JSON value of shape:
//!
//! ```jsonc
//! {
//!   "catalog": { "users_data": ["id", "name", ...], ... },
//!   "policy":  [ { "principal": "CRM", "relation": "users_data", "columns": ["id", "name"] }, ... ],
//!   "principal": "CRM",
//!   "plan": { "op": "scan", "rel": "users_data" }
//! }
//! ```
//!
//! and returns:
//!
//! ```jsonc
//! {
//!   "ok": true,
//!   "allowed":     ["id", "name", "region", "age"],
//!   "input_plan":  { ... },          // echoed for the UI
//!   "output_plan": { "op": "project", "sub": ..., "cols": [...] }
//! }
//! ```
//!
//! or on refusal:
//!
//! ```jsonc
//! { "ok": false, "reason": "unknown relation" | "filter on forbidden column", "allowed": [...] }
//! ```

use postern_core::{rewrite, Catalog, Plan, Policy};
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

#[derive(Debug, Deserialize)]
struct Request {
    catalog: Catalog,
    policy: Policy,
    principal: String,
    plan: Plan,
}

#[derive(Debug, Serialize)]
#[serde(untagged)]
enum Response {
    Accept {
        ok: bool,
        allowed: Vec<String>,
        input_plan: Plan,
        output_plan: Plan,
    },
    Refuse {
        ok: bool,
        reason: String,
        allowed: Vec<String>,
    },
}

/// Rewrite a plan under the supplied catalog + policy + principal.
///
/// Accepts a JS value (deserialised via `serde-wasm-bindgen`),
/// returns a JS value with the result. JS-side typing is intentionally
/// loose — the demo treats this as a JSON-shaped function.
#[wasm_bindgen]
pub fn rewrite_plan(request: JsValue) -> Result<JsValue, JsValue> {
    let req: Request = serde_wasm_bindgen::from_value(request)
        .map_err(|e| JsValue::from_str(&format!("invalid request: {e}")))?;

    let allowed = req.policy.allowed(&req.principal, req.plan.touched());

    let response = match rewrite(&req.catalog, &req.policy, &req.principal, &req.plan) {
        Some(output_plan) => Response::Accept {
            ok: true,
            allowed: allowed.clone(),
            input_plan: req.plan.clone(),
            output_plan,
        },
        None => {
            // Reproduce the refusal-reason logic from postern_core::rewrite
            // so the UI can show "why".
            let touched = req.plan.touched();
            let cat_cols = req.catalog.columns(touched);
            let reason = if cat_cols.is_empty() {
                format!("unknown relation: {touched}")
            } else {
                let bad: Vec<String> = req
                    .plan
                    .filter_cols()
                    .into_iter()
                    .filter(|c| !allowed.contains(c))
                    .collect();
                if bad.is_empty() {
                    "refused (unspecified)".into()
                } else {
                    format!("filter on forbidden column(s): {}", bad.join(", "))
                }
            };
            Response::Refuse {
                ok: false,
                reason,
                allowed,
            }
        }
    };

    serde_wasm_bindgen::to_value(&response)
        .map_err(|e| JsValue::from_str(&format!("serialize: {e}")))
}
