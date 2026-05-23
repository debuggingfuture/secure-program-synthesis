"""Dataframe gateway — accepts an Ibis expression from an agent tool,
walks the plan to enumerate touched resources, calls the decision oracle,
and either rewrites or rejects."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any

from .policy import Action, Effect, Policy, Principal, ResourcePath


class Decision(str, Enum):
    allow = "allow"
    deny = "deny"


@dataclass
class GatewayResult:
    decision: Decision
    rewritten: Any | None
    reason: str


def _authorize(policy: Policy, principal: Principal, resource: ResourcePath, action: Action) -> Decision:
    """Mirror of `Vapor.Spec.authorize`. Forbid-wins, then permit, else deny.

    Resource matching is exact-column or whole-table (`column is None` in
    the rule's resource list matches any column of that table). The full
    semantics live in Lean; this implementation must agree on every
    input under differential testing."""

    def matches(r) -> bool:
        if r.action != action:
            return False
        for rp in r.resources:
            same_table = (
                rp.source == resource.source
                and rp.schema == resource.schema
                and rp.table == resource.table
            )
            if not same_table:
                continue
            if rp.column is None or rp.column == resource.column:
                if r.cond(principal):
                    return True
        return False

    if any(r.effect == Effect.forbid and matches(r) for r in policy.rules):
        return Decision.deny
    if any(r.effect == Effect.permit and matches(r) for r in policy.rules):
        return Decision.allow
    return Decision.deny


class Gateway:
    """Intercepts dataframe operations from agent tools."""

    def __init__(self, policy: Policy) -> None:
        self.policy = policy

    def authorize(self, principal: Principal, resource: ResourcePath, action: Action) -> Decision:
        return _authorize(self.policy, principal, resource, action)

    def evaluate_plan(self, principal: Principal, touched: list[ResourcePath]) -> GatewayResult:
        """Reject-only variant matching `Vapor.Rewriter.rewrite`.

        Real implementation will walk an Ibis / Substrait plan to
        compute `touched`; here we let the caller pass it explicitly so
        unit tests can exercise the policy core without spinning DuckDB."""

        for r in touched:
            if self.authorize(principal, r, Action.read) == Decision.deny:
                return GatewayResult(
                    decision=Decision.deny,
                    rewritten=None,
                    reason=f"forbid on {r}",
                )
        return GatewayResult(decision=Decision.allow, rewritten=None, reason="ok")
