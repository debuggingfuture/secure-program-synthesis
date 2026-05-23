# Scenario 4 — Cross-source RAG: labels on embeddings

## Setting

A "Knowledge Copilot" runs RAG over Slack, Notion, and PostHog event
descriptions. All three sources are chunked and embedded into a single
pgvector / Turbopuffer index. The engineer principal is allowed to read
Slack channels they belong to, all Notion pages with `Audience:
engineering`, and all PostHog events — but not channels they don't
belong to and not Notion pages marked `Confidential: HR`.

## The attack

Standard cross-tenant / cross-permission embedding leak. The retriever
returns the top-k by vector distance; without a label-aware filter, a
chunk from `#exec-leadership` (engineer is not a member) can surface
just because its embedding is close to the query.

## What VAPOR should do

The ingest path attaches a **labels** column to every embedding row
(`source`, `channel`, `audience`, `confidential`, etc.). The policy
expresses:

```vapor
@principal(role: "engineer", user_id: $u)
permit
  read on memory.embeddings.*
  when
    row.labels.source == "slack"
      and row.labels.channel in $u.slack_channels
    or row.labels.source == "notion"
      and row.labels.audience == "engineering"
      and not row.labels.confidential == "hr"
    or row.labels.source == "posthog"
```

The plan rewriter pushes the label predicate into the vector retrieval
(as a metadata filter) *before* top-k; the gateway forbids issuing the
raw `embedding <-> query LIMIT k` without that filter.

## Lean obligation: `EmbeddingLabel.sound`

A row in the output of an `ANN(k, query)` operator must satisfy the
label predicate. Because the vector store evaluates filter-then-rank,
this is straightforward — but the policy must *force* the filter; the
soundness theorem is exactly that no rewrite path yields an ANN op
without the metadata filter inserted.

## Insight worth foregrounding in the paper

The vector store's metadata-filter feature is normally an *optimization
toggle*. By treating it as the lone enforcement primitive for embedded
data, the policy author gets cross-source RAG access control for free —
and gets it *verified* in the same Lean artifact as the SQL paths.
