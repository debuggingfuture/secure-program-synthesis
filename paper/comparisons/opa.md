# VAPOR vs Open Policy Agent (OPA)

> Why OPA matters in this comparison: of all the systems VAPOR resembles,
> OPA is the only one with a production-grade **data-filtering** story
> via *Partial Evaluation* — and that mechanism is the closest existing
> analogue to VAPOR's verified plan rewriter. The differences matter
> exactly where Cedar-style verification meets dataframe-shaped policy.

## TL;DR

| | OPA + Rego | VAPOR |
|---|---|---|
| Policy language | Rego (Datalog-inspired, general-purpose) | `Vapor.Spec` (Cedar-shaped + dataframe predicates) |
| Verification of language | none — testable, not mechanized | Lean 4 denotational semantics + theorems |
| Decision model | "given input doc, allow/deny" | "given query plan + principal, accept-plan or reject" |
| Data-shaped rewriting | **Partial Evaluation → SQL WHERE / Elasticsearch DSL** (production, unverified) | **Plan rewriter** with Lean soundness theorem |
| Cross-source labels | data is opaque JSON to OPA | first-class `Resource.labels` (residency, PII class, MNPI, retention) |
| Aggregation predicates | author writes Rego rule; no first-class aggregation grammar | `aggregation.row_count`, `is_grouped_by_at_least` first-class |
| Masking / projection | not in core; author marshals manually | `mask … using fn` as a primitive |
| Audit log | custom — depends on caller wrapping each `Eval` call | verified `Log.complete` over the oracle |
| Deployment | sidecar / Go SDK / WASM | dataframe gateway intercepting Ibis/Substrait plans |
| Status (mid-2026) | maintainer acquisition by Apple in 2025-08; enterprise offerings sunsetting [@osohq2025] | research artifact |

## Where OPA already does what VAPOR does

**Partial Evaluation (PE)** is OPA's compile-time technique for taking a
Rego policy plus a partial input (some keys marked `unknown`) and
returning a *residual* — a smaller Rego AST whose remaining unknowns
correspond to the runtime values not yet bound. The residual can be
walked to emit a `WHERE` clause, an Elasticsearch query, a MongoDB
filter, etc. [@opa-pe]. A canonical example: the Rego rule

```rego
allow {
    input.action == "read"
    input.user.role == "support"
    data.tickets[_].owner == input.customer_id
}
```

with `input.customer_id` left unknown produces a residual that
compiles to `WHERE tickets.owner = ?` — exactly the row-level filter
that VAPOR's rewriter would inject.

**This is the technique.** VAPOR is not introducing the concept of
"policy as query rewrite" — OPA shipped it years ago. What VAPOR
introduces is a **mechanically verified** version of that technique
over a **dataframe-typed** plan IR.

## Where they diverge

### 1. Verification

OPA's correctness story is testing: `opa test`, coverage reports,
property-based testing via `rego.v1`. Idiomatic and excellent for
catching bugs, but does not produce a soundness theorem. The
data-filtering compiler in particular is "the residual that OPA emits
is sound *if* the translator from residual → SQL is sound" — and that
translator is hand-written per backend.

VAPOR's bet: write the policy semantics in Lean (à la `cedar-spec`),
prove the rewriter sound against those semantics, extract or
differentially-test the production oracle. The headline theorems
(`Rewriter.sound`, `Ingest.compose`, `Log.complete`) have direct
analogues in the *use-cases for which OPA shipped no theorem*.

Cedar makes a similar diagnosis of Rego and has been demonstrated to
be 42–60× faster *with* verified soundness — same diagnosis is what
motivates VAPOR's choice to keep the surface Cedar-shaped, not
Rego-shaped [@osohq2025]. (We are not advocating Cedar over OPA in
general — only noting the diagnostic.)

### 2. The data plane is first-class

To OPA, input data is opaque JSON. The Rego programmer writes
predicates that look inside it, but OPA has no privileged understanding
of "this field is PII" or "this row has residency labels." Labels are a
convention layered on top.

To VAPOR, **labels are policy primitives.** A `Vapor.Spec` policy can
say `forbid read on customers.* when 'EU' in row.labels.residency and
principal.country not in row.labels.residency` — and the label schema
(`residency: ISO2[]`, `pii_class: enum`, `mnpi_ticker: String`,
`mnpi_until: Timestamp`, `retention: Duration`) is part of the
language, not a convention. The Lean semantics quantify over these
typed labels.

The practical consequence: in OPA you can express the same residency
rule, but the burden of "every ingest pipeline must tag every row
with the right residency label, and every Rego policy must look it
up" lives entirely in the application. In VAPOR the burden is the
same conceptually but the *language* enforces shape, and the *Lean
spec* lets us prove things like `Ingest.compose` — that the same
label, used at write-side and read-side, yields the same observable
output.

### 3. Plan-shape vs decision-shape

OPA's decision API answers `(input) → decision`. The "decision" can be
a boolean, an object, or — with PE — a residual that the caller is
responsible for compiling and combining with their actual query.

VAPOR's gateway *is* the query path. A dataframe call from an agent
serializes to a Substrait plan; the gateway hands the plan to the
oracle, which returns either an accepted (possibly rewritten) plan or
a rejection. There is no integration burden on the caller to
"remember to apply the filter" — applying the filter *is* what
calling the gateway means.

Two ways to see this:

- **Pro OPA:** the integration is more flexible. You can drop OPA into
  any application without restructuring the query path.
- **Pro VAPOR:** the integration is the security boundary. If an agent
  bypasses the gateway, the bypass is visible architecturally; in an
  OPA deployment, a forgotten `eval_partial` call is a silent
  authorization hole.

### 4. Aggregation, masking, and write rewrites

OPA can express aggregation thresholds as Rego predicates, but the
*translation* to SQL `GROUP BY` constraints is per-backend and not
part of the OPA core. Masking is not a Rego concept; you express it
as "if condition, return the masked value" in application code.

VAPOR makes these primitives:

- `aggregation.is_grouped_by_at_least([...])` and
  `aggregation.row_count >= k` are typed predicates the rewriter
  understands.
- `mask <col> using <fn>` is a top-level effect on par with `permit`
  and `forbid`; the projection-rewrite path emits the masking call
  into the plan.
- Cross-row predicates (e.g. SOX SoD where the rule mentions both
  `principal.id` and `row.initiator_id`) drive the write-rewrite
  extension currently scaffolded as future work.

### 5. Audit

OPA decision logs are excellent — every evaluation can be shipped to
a decision-log sink with input, output, policy, and timestamp. But
the **completeness** of that log depends on every caller turning the
feature on and routing every decision through OPA. In an OPA deployment
where some queries are gated by OPA and others bypass it (e.g.
because they don't yet have a Rego policy), the audit log is silent
on the bypassed paths.

VAPOR's `Log.complete` theorem makes this guarantee architectural:
the only path to the lake is through the gateway, the only path
through the gateway calls the oracle, the oracle emits one log
record per call. There is no "forgot to log" path — see
`scenarios/financial-institution/08-regulator-audit.md`.

## Where they could compose

The interesting overlap is **PE-flavored mechanics**:

- OPA's PE is the existence proof that policy-as-rewriting works in
  production. VAPOR's rewriter could borrow PE's residual-AST
  approach (rather than the eager case-split approach our Lean stub
  uses), and prove the residual translation sound *once*.
- A migration path for an OPA shop: keep Rego for non-data
  authorization decisions (K8s admission, Envoy, Terraform — the
  things VAPOR doesn't try to do), adopt `Vapor.Spec` only for the
  agent-context data path. The two coexist on a typical bank's
  infrastructure.
- A backend strategy for VAPOR: target OPA's Compile API as one
  output, so an existing OPA decision-log pipeline can consume VAPOR
  decisions. The reverse — Rego frontend for VAPOR — would require
  Rego type-narrowing that's currently out of scope.

## Where neither helps yet

Both OPA and VAPOR are silent on:

- **LLM agent output filtering.** Once the allowed rows leave the
  oracle, both systems trust the agent to use them appropriately. A
  prompt-injected agent can still leak via tool output, screenshot,
  generated text. Defense-in-depth requires a complementary output
  layer.
- **Aggregation-inference attacks** beyond k-min-group-size. Neither
  ships a DP mechanism; both rely on the policy author to encode the
  right threshold.
- **Supply chain of the policy itself.** Both presume the policy
  artifact reaches the engine intact.

## One-paragraph positioning for the paper

> **OPA is the closest production system to VAPOR.** Its Partial
> Evaluation feature already does what VAPOR's plan rewriter does in
> spirit — turn a policy into a residual that becomes a `WHERE`
> clause. VAPOR differs on three load-bearing axes: (1) the policy
> language is small and Cedar-shaped, with denotational semantics
> mechanized in Lean 4, so the rewriter has a soundness theorem the
> PE compiler does not; (2) labels (residency, PII class, MNPI,
> retention) are first-class primitives of the language, not a
> convention layered on opaque JSON; (3) the gateway *is* the query
> path, making the audit log a verified property of the oracle rather
> than a feature the caller might forget to enable. The two systems
> are not exclusive: a bank already invested in OPA for K8s and
> Envoy admission can adopt VAPOR for the agent-context data path
> without retiring Rego.

## References (not yet in `references.bib`)

- `@opa-pe` — *Partial Evaluation for OPA*,
  https://www.openpolicyagent.org/docs/filtering/partial-evaluation
- `@osohq2025` — *OPA vs Cedar vs Zanzibar: 2025 Policy Engine Guide*,
  https://www.osohq.com/learn/opa-vs-cedar-vs-zanzibar
- `@opa-repo` — https://github.com/open-policy-agent/opa
- `@opa-data-filtering` — *Writing Valid Data Filtering Policies*,
  https://www.openpolicyagent.org/docs/filtering/fragment
