"""Smoke tests for the policy core. Will be extended into a property-
based differential harness against the Lean kernel (see Cedar's DRT)."""

from vapor import Effect, Gateway, Policy, Principal, ResourcePath, Rule
from vapor.gateway import Decision
from vapor.policy import Action


def _engineer_policy() -> Policy:
    return Policy(
        rules=[
            Rule(
                effect=Effect.permit,
                action=Action.read,
                resources=[ResourcePath("slack", "raw", "messages")],
            ),
            Rule(
                effect=Effect.forbid,
                action=Action.read,
                resources=[ResourcePath("rds", "finance", "payroll")],
            ),
        ]
    )


def test_engineer_can_read_slack() -> None:
    g = Gateway(_engineer_policy())
    eng = Principal(id="alice", role="platform-engineer")
    out = g.evaluate_plan(eng, [ResourcePath("slack", "raw", "messages", "text")])
    assert out.decision == Decision.allow


def test_engineer_cannot_read_payroll() -> None:
    g = Gateway(_engineer_policy())
    eng = Principal(id="alice", role="platform-engineer")
    out = g.evaluate_plan(eng, [ResourcePath("rds", "finance", "payroll", "amount")])
    assert out.decision == Decision.deny
    assert "forbid" in out.reason


def test_join_with_one_denied_resource_is_denied() -> None:
    g = Gateway(_engineer_policy())
    eng = Principal(id="alice", role="platform-engineer")
    out = g.evaluate_plan(
        eng,
        [
            ResourcePath("slack", "raw", "messages", "user_id"),
            ResourcePath("rds", "finance", "payroll", "user_id"),
        ],
    )
    assert out.decision == Decision.deny
