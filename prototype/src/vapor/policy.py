"""Python mirror of `Vapor.Spec` — used by the gateway, and the side of
the differential testing harness that compares against the Lean kernel.

The shape of these dataclasses tracks `verifier/lean/Vapor/Spec.lean`.
When the Lean side changes, change here too; tests will catch drift via
the differential harness."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Callable


class Effect(str, Enum):
    permit = "permit"
    forbid = "forbid"


class Action(str, Enum):
    read = "read"
    aggregate = "aggregate"
    write = "write"


@dataclass(frozen=True)
class ResourcePath:
    source: str
    schema: str
    table: str
    column: str | None = None

    def __str__(self) -> str:
        base = f"{self.source}.{self.schema}.{self.table}"
        return f"{base}.{self.column}" if self.column else f"{base}.*"


@dataclass(frozen=True)
class Principal:
    id: str
    role: str


@dataclass
class Rule:
    effect: Effect
    action: Action
    resources: list[ResourcePath]
    # Placeholder for the WHEN clause; the real artifact will marshal an
    # expression AST identical to `Vapor.Spec.Rule.cond`.
    cond: Callable[[Principal], bool] = field(default=lambda _p: True)


@dataclass
class Policy:
    rules: list[Rule] = field(default_factory=list)
