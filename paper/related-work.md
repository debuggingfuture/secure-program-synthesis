# Related work — map

Five axes we differentiate on:

1. **Formal guarantee** — none / machine-checked / SMT-backed.
2. **Granularity** — API-call / row / column / cell / aggregate / embedding.
3. **Deployment surface** — per-DB extension / app framework / gateway / sandbox.
4. **Agentic-aware** — does the model account for prompt-injected,
   tool-calling agents and cross-source aggregation?
5. **Author surface** — DSL coupled to one store, or decoupled.

| Work | Guarantee | Granularity | Surface | Agentic | Decoupled |
|---|---|---|---|---|---|
| Postgres RLS | none | row | DB extension | no | no |
| Cedar (AWS) [PLDI'24, OOPSLA'25] | Lean-verified policy semantics + SMT analysis | API call | embedded library | no | yes |
| **OPA + Rego** (CNCF) | none (tested, not verified); **PE → SQL/ES filters** is closest existing analogue to our rewriter | row via Partial Evaluation; opaque JSON otherwise | sidecar / Go SDK / WASM | no | yes |
| SEAL (SACMAT'23) | capability-based runtime, no formal proof | computation on data | sandbox VM | partial | yes |
| Jeeves/Jacqueline (PLDI'16) | policy-agnostic IFC, paper-level proofs | row + value | Python web framework | no | yes-ish |
| MemArchitect (arXiv 2603.18330) | governance rules, no formal proof | memory record | mem layer | yes | yes |
| Object-capability SQL sandbox for LLM agents (blog) | unverified | row+column via cap classes | tool/library | yes | yes |
| IFC for ML pipelines (arXiv 2311.15792) | non-interference, paper-level | model output | architectural | partial | n/a |
| **VAPOR (this work)** | **Lean-verified DSL + rewriter** | **row/column/aggregate, plus embedding label** | **dataframe gateway** | **yes** | **yes** |

## Detailed pointers

### Cedar (AWS) — direct ancestor
- Disselkoen et al., *Cedar: A New Language for Expressive, Fast, Safe, and
  Analyzable Authorization*, OOPSLA 2024 — defines language, Lean
  formalization, validation soundness.
  https://dl.acm.org/doi/10.1145/3649835
- Wells et al., *How We Built Cedar: A Verification-Guided Approach*,
  arXiv 2407.01688 — VGD methodology (proofs + differential random
  testing). Quote: "VGD … found 4 bugs in the validator via proof and 21
  more via DRT/PBT."
- Cedar Symbolic Compiler / Cedar Analysis: Lean-implemented sound +
  complete SMT encoding; answers equivalence, "more permissive than",
  shadowed-permit, never-true.
  https://aws.amazon.com/blogs/opensource/introducing-cedar-analysis-open-source-tools-for-verifying-authorization-policies/
- `cedar-spec/cedar-lean` layout we mirror: `Cedar/Spec` (semantics),
  `Cedar/Validation`, `Cedar/Thm` (theorems), `Cedar/SymCC` (symbolic
  compiler), `DiffTest` / `SymTest` / `UnitTest`.

**Difference vs VAPOR.** Cedar authorizes *one API call at a time* on
opaque entities. VAPOR's policies *evaluate against query plans over
relational data* — the same DSL must talk about rows, columns, and
aggregates, and the rewriter must transform `q` not just decide
allow/deny. Cedar's slicing theorem is the closest analogue; our
`Rewriter.sound` theorem generalizes it to relational outputs.

### OPA + Rego (CNCF)
*Open Policy Agent*, CNCF graduated project (2018–present); core
maintainers acquired by Apple in August 2025, enterprise offerings
sunsetting.

- Rego — Datalog-inspired declarative policy language.
- Decision API: caller supplies an `input` JSON document; OPA returns a
  decision (boolean / object).
- **Partial Evaluation (PE)** — given a policy and an input doc with
  some keys marked `unknown`, OPA emits a *residual AST* that downstream
  code can compile to SQL `WHERE` clauses, Elasticsearch DSL,
  MongoDB filters, etc.
  https://www.openpolicyagent.org/docs/filtering/partial-evaluation
- Deployment: sidecar process, Go SDK library, WASM, or as a plugin to
  Envoy, K8s admission, Terraform validators.
- No formal verification; correctness story is `opa test` + coverage.

**Difference vs VAPOR.** Detailed in `paper/comparisons/opa.md`. One
line: OPA's PE → SQL is the closest existing analogue to VAPOR's plan
rewriter, but it's unverified, opaque to data shape (labels are a
convention not a primitive), and decision-shaped rather than
plan-shaped (caller responsible for applying the residual). VAPOR's
position is "what OPA-PE could be if its semantics were mechanized in
Lean and the data plane were first-class."

### SEAL (Rasifard et al., SACMAT 2023)
*"SEAL: Capability-Based Access Control for Data-Analytic Scenarios."*
Hamed Rasifard, Rahul Gopinath, Michael Backes, Hamed Nemati.
- Premise: data owner publishes data + capabilities (callable functions)
  in a sandbox; analyst's computation runs *inside* the sandbox under
  capability constraints; owner data never leaves.
- Mechanism: WebAssembly-style sandbox, capability tokens.
- No formal proofs in the paper; trust resides in the sandbox.

**Difference vs VAPOR.** SEAL is the "where do I run untrusted compute"
story; VAPOR is the "is the policy itself correct" story. They compose
naturally — VAPOR's verified policy decision could mint SEAL capabilities.

### Jeeves / Jacqueline (Yang et al., POPL'12, PLDI'16)
Policy-agnostic programming: programmer writes policies once, runtime
*faceted values* enforce. Jacqueline applies this to SQL-backed Python
web apps with rewrite at the ORM layer.
- https://projects.csail.mit.edu/jeeves/

**Difference vs VAPOR.** Jeeves predates LLM agents; no formal Lean
artifact, no SMT analysis, no cross-source story. The faceted-value
runtime is heavyweight (every value carries a label). VAPOR's
plan-rewriter approach is closer to RLS in spirit — no per-value tags —
but with Lean-verified correctness instead of trust in the DB engine.

### MemArchitect (arXiv 2603.18330)
Governance layer over agent memory: rule-based decay, contradiction
resolution, "right-to-be-forgotten." Identifies the governance gap we
also identify but ships rules, not a verified policy artifact.

**Difference vs VAPOR.** MemArchitect = lifecycle governance; VAPOR =
access governance. Complementary; could share a policy spec.

### Object-capability SQL sandboxing for LLM agents
Rasti, blog (2025). Capability classes that wrap tables and gate access
via typed object references; "dangerous queries are inexpressible."
https://ryanrasti.com/blog/object-capability-sql-sandboxing-for-llm-agents/

**Difference vs VAPOR.** Same spirit (capabilities baked into the agent's
tool surface). Differences: (a) no formal proof; (b) hand-written
capability classes per table instead of a declarative DSL; (c) SQL-only,
no cross-source / dataframe / embedding story; (d) author explicitly
flags formal-verification + cross-system policies as future work.

### IFC for ML pipelines (Wutschitz et al., arXiv 2311.15792)
Frames ML training/inference as information flows; advocates per-user
fine-tuning and retrieval as architectural enforcement of user-level
non-interference.

**Difference vs VAPOR.** ML-system-architectural rather than
policy-language-level. We borrow the non-interference framing for the
RAG / embedding scenario.

### Mem0 (arXiv 2504.19413)
Production memory architecture (vector + KG + KV) for LLM agents.
Authorization is not the focus; mentions multi-tenant isolation
operationally but doesn't formalize. VAPOR is the layer mem0-style
systems would call before serving a memory record to an agent.

### Prompt-injection / agent-exfil literature (2025–2026)
- OWASP LLM Top 10 (2025) — prompt injection #1.
- EchoLeak (CVE-2025-32711) — zero-click exfil in M365 Copilot.
- "Your AI, My Shell" (arXiv 2509.22040) — injection in agentic coding
  editors.

These motivate the *threat model*. None of them propose a verified
mediation layer; defenses are pattern-matching or sandbox-based.

## Items still to read (for the camera-ready)

- *Precise, Dynamic Information Flow for Database-Backed Applications*,
  Yang et al., PLDI'16 — Jacqueline full paper. https://arxiv.org/pdf/1507.03513
- Cedar full Lean repo `cedar-policy/cedar-spec/cedar-lean` — directly
  inspect theorem statements to mirror style.
- IFDB / Resin (older IFC-on-DB systems) — completeness pass on prior art.
- OPA / Rego — operational baseline only.
- Substrait extension YAML for typing custom relational ops (where our
  policy-decorated relops would live).
- arXiv 2603.13181 *Verification of Robust Properties for Access Control
  Policies* — compositional property persistence under extension; possibly
  useful for our `Ingest ∘ Rewrite` composition theorem.
