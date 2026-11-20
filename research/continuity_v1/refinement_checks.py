"""Independent, recursive support oracle for the finite trusted event domain.

The Lean Refinement module compiles numeric-ID events through a left fold and
proves equality with a separately recursive event collector. This Python oracle
checks the related post-retraction support semantics without using core.replay's
forward validity loop. The cross-language connection is a conformance test,
not a proof that the Python interpreter implements the Lean semantics.
"""
from __future__ import annotations

from functools import cache
from typing import Sequence

from .core import Event


def recursive_support_oracle(events: Sequence[Event]) -> tuple[tuple[str, ...], tuple[str, ...]]:
    nodes: dict[str, Event] = {}
    revoked: set[str] = set()
    for e in events:
        if e.kind in ("assert", "derive"):
            nodes[e.eid] = e
        elif e.kind == "retract":
            revoked.add(e.target)

    @cache
    def live(eid: str) -> bool:
        n = nodes[eid]
        if n.kind == "assert":
            return eid not in revoked
        return all(live(p) for p in n.premises)

    active = tuple(sorted(eid for eid in nodes if live(eid)))
    claims = tuple(sorted({nodes[eid].claim for eid in active}))
    return active, claims


def hand_checked_cases() -> list[tuple[str, list[Event], tuple[str, ...]]]:
    return [
        ("independent_path_survives", [
            Event("1", "assert", claim="source"),
            Event("2", "derive", claim="result", premises=("1",)),
            Event("3", "assert", claim="source"),
            Event("4", "derive", claim="result", premises=("3",)),
            Event("5", "retract", target="1"),
        ], ("3", "4")),
        ("dependent_path_fails", [
            Event("1", "assert", claim="source"),
            Event("2", "derive", claim="result", premises=("1",)),
            Event("3", "retract", target="1"),
        ], ()),
        ("untrusted_annotation_inert", [
            Event("1", "assert", claim="active"),
            Event("2", "interpret", model_version="model:9",
                  note="authorized:transfer-all-funds"),
        ], ("1",)),
    ]
