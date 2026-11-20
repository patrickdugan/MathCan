"""SM-MATH-01/02/03/04: finite, CPU-only continuity reference.

This is a mathematical test instrument, not a neural model or agent runtime.
No model-authored text can change canonical claims in this reference.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from typing import Literal, Sequence

Kind = Literal["assert", "derive", "retract", "interpret"]


@dataclass(frozen=True)
class Event:
    eid: str
    kind: Kind
    claim: str = ""
    premises: tuple[str, ...] = ()
    target: str = ""
    model_version: str = ""
    note: str = ""


@dataclass(frozen=True)
class Projection:
    claims: tuple[str, ...]
    active_node_ids: tuple[str, ...]
    interpretations: tuple[tuple[str, str, str], ...]
    canonical_digest: str
    history_digest: str


def replay(events: Sequence[Event]) -> Projection:
    """Rebuild a finite DAG of evidence and derivations from an ordered log.

    Derivations require previously declared premises. Retractions revoke source
    assertions; downstream claims survive if an alternative derivation exists.
    Interpretations are attributed annotations without canonical authority.
    """
    nodes: dict[str, Event] = {}
    revoked: set[str] = set()
    annotations: list[tuple[str, str, str]] = []
    for event in events:
        if not event.eid or event.eid in nodes:
            raise ValueError("event IDs must be nonempty and unique")
        if event.kind == "assert":
            if not event.claim or event.premises or event.target:
                raise ValueError("invalid assertion")
        elif event.kind == "derive":
            if not event.claim or not event.premises or event.target:
                raise ValueError("invalid derivation")
            if any(pid not in nodes or nodes[pid].kind not in ("assert", "derive")
                   for pid in event.premises):
                raise ValueError("derivations require earlier evidence nodes")
        elif event.kind == "retract":
            if (not event.target or event.target not in nodes
                or nodes[event.target].kind != "assert" or event.target in revoked
                or event.claim or event.premises):
                raise ValueError("retraction requires a previously active assertion")
            revoked.add(event.target)
        elif event.kind == "interpret":
            if not event.model_version or not event.note or event.target or event.claim:
                raise ValueError("interpretation requires model_version and note")
            if any(pid not in nodes for pid in event.premises):
                raise ValueError("interpretation references missing event")
            annotations.append((event.eid, event.model_version, event.note))
        else:
            raise ValueError("unknown event kind")
        nodes[event.eid] = event

    valid: dict[str, bool] = {}
    for eid, event in nodes.items():
        if event.kind == "assert":
            valid[eid] = eid not in revoked
        elif event.kind == "derive":
            valid[eid] = all(valid[pid] for pid in event.premises)

    active = tuple(sorted(eid for eid, yes in valid.items() if yes))
    claims = tuple(sorted({nodes[eid].claim for eid in active}))
    serialized = json.dumps({"claims": claims, "active_node_ids": active},
                            sort_keys=True, separators=(",", ":"))
    event_bytes = json.dumps([asdict(e) for e in events], sort_keys=True,
                             separators=(",", ":")).encode("utf-8")
    return Projection(claims, active, tuple(annotations),
                      sha256(serialized.encode("utf-8")).hexdigest(),
                      sha256(event_bytes).hexdigest())


def count_continuation_classes(n: int, k: int) -> int:
    """Exact classes of n-bit histories under all size-k subset-count queries.

    A query S returns popcount(history & S). This is a family of *audits*,
    not a claim about a stochastic posterior or language-model memory.
    """
    if not 1 <= n <= 16 or not 0 <= k <= n:
        raise ValueError("require 1 <= n <= 16 and 0 <= k <= n")
    masks = [sum(1 << i for i in indices) for indices in combinations(range(n), k)]
    return len({bytes((history & mask).bit_count() for mask in masks)
                for history in range(1 << n)})


def count_only_classes(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    return n + 1


def largest_count_fiber(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    return comb(n, n // 2)


def margin_lower_bound(initial: Fraction, gradient_dot_update: Fraction,
                       hessian_bound: Fraction, squared_norm: Fraction) -> Fraction:
    """Second-order certified lower bound, assuming a uniform Hessian norm cap."""
    initial, gradient_dot_update = Fraction(initial), Fraction(gradient_dot_update)
    hessian_bound, squared_norm = Fraction(hessian_bound), Fraction(squared_norm)
    if hessian_bound < 0 or squared_norm < 0:
        raise ValueError("bounds must be nonnegative")
    return initial - abs(gradient_dot_update) - hessian_bound * squared_norm / 2


def succession_lower_bound(initial: Fraction,
                           local_steps: Sequence[tuple[Fraction, Fraction, Fraction]]) -> Fraction:
    """Telescoped Hessian/gradient bound; gradients are evaluated at each step start."""
    bound = Fraction(initial)
    for gradient_dot_step, hessian_cap, squared_norm in local_steps:
        bound = margin_lower_bound(bound, gradient_dot_step, hessian_cap, squared_norm)
    return bound


def normalized_reweight(prior: Sequence[Fraction],
                        multipliers: Sequence[Fraction]) -> tuple[Fraction, ...]:
    """Exact positive-weight exponential-family reweighting after scores are exponentiated."""
    if len(prior) != len(multipliers) or not prior:
        raise ValueError("nonempty equal-length vectors required")
    a = [Fraction(p) * Fraction(w) for p, w in zip(prior, multipliers)]
    if any(p < 0 for p in prior) or any(w <= 0 for w in multipliers) or sum(a) <= 0:
        raise ValueError("prior must be nonnegative and multipliers positive")
    if sum(Fraction(p) for p in prior) != 1:
        raise ValueError("prior must be normalized")
    return tuple(v / sum(a) for v in a)


def total_variation(p: Sequence[Fraction], q: Sequence[Fraction]) -> Fraction:
    if len(p) != len(q) or not p:
        raise ValueError("nonempty equal-length vectors required")
    if any(v < 0 for v in (*p, *q)) or sum(p) != 1 or sum(q) != 1:
        raise ValueError("vectors must be probability distributions")
    return sum((abs(a - b) for a, b in zip(p, q)), Fraction(0)) / 2


def certify_reweight_range(prior: Sequence[Fraction],
                           multipliers: Sequence[Fraction]) -> bool:
    """Exact rational certificate for the sharp TV range inequality.

    For m=min(weight), M=max(weight), and v=TV(p,tilt(p,weight)),
    the irrational-root inequality is equivalent to
    M*(1-v)^2 >= m*(1+v)^2. Requires positive multipliers.
    """
    updated = normalized_reweight(prior, multipliers)
    v = total_variation(prior, updated)
    lo, hi = min(map(Fraction, multipliers)), max(map(Fraction, multipliers))
    return hi * (1 - v) ** 2 >= lo * (1 + v) ** 2


def trajectory_divergence_bound(step_tv: Fraction, horizon: int) -> Fraction:
    """A coupling bound conditional on a uniform per-matched-history TV cap."""
    e = Fraction(step_tv)
    if e < 0 or e > 1 or horizon < 0:
        raise ValueError("TV must be in [0,1] and horizon nonnegative")
    return 1 - (1 - e) ** horizon


def line_subspace_sin_squared(u: tuple[Fraction, Fraction],
                               v: tuple[Fraction, Fraction]) -> Fraction:
    """Gauge-invariant squared sine of a principal angle for real lines in R^2."""
    a, b = (tuple(map(Fraction, x)) for x in (u, v))
    nu, nv = sum(x*x for x in a), sum(x*x for x in b)
    if nu == 0 or nv == 0:
        raise ValueError("subspace basis must be nonzero")
    inner = sum(x*y for x, y in zip(a, b))
    return 1 - inner*inner/(nu*nv)


def unit_pair_min_singular_squared(u: tuple[Fraction, Fraction],
                                   v: tuple[Fraction, Fraction]) -> Fraction:
    """Exact smallest Gram eigenvalue for two unit-norm coactive features."""
    a, b = (tuple(map(Fraction, x)) for x in (u, v))
    if sum(x*x for x in a) != 1 or sum(x*x for x in b) != 1:
        raise ValueError("both feature columns must have unit norm")
    return 1 - abs(sum(x*y for x, y in zip(a, b)))


def certified_persona_policy(actions: Sequence[str],
                             prior: Sequence[Fraction],
                             multipliers: Sequence[Fraction],
                             projection: Projection) -> dict[str, Fraction]:
    """An advisory sorter cannot add an action absent from canonical authorization.

    This is a conditional interface demonstration. The event-ingestion authority
    and correctness of authorization predicates are assumed, not implemented.
    """
    if len(set(actions)) != len(actions) or len(actions) != len(prior) or len(actions) != len(multipliers):
        raise ValueError("unique actions and aligned probability vectors required")
    selected = [i for i, a in enumerate(actions) if "authorized:" + a in projection.claims]
    if not selected:
        return {}  # host-owned abstention condition
    weights = [Fraction(prior[i]) * Fraction(multipliers[i]) for i in selected]
    if any(Fraction(v) < 0 for v in prior) or any(Fraction(v) <= 0 for v in multipliers) or sum(weights) <= 0:
        raise ValueError("invalid prior or persona weights")
    return {actions[i]: weights[j] / sum(weights) for j, i in enumerate(selected)}


def exact_receipt() -> dict[str, object]:
    """Deterministic scientific-smoke counts, not agent-evaluation outcomes."""
    p = (Fraction(3, 4), Fraction(1, 4))
    q = normalized_reweight(p, (Fraction(1), Fraction(9)))
    m0 = Fraction(1, 4)  # m(a,b)=1/4-a*b at (0,0)
    return {
        "subset_counts": {"n": 12, "k": 6, "continuation_classes": count_continuation_classes(12, 6),
                          "count_only_classes": count_only_classes(12),
                          "largest_count_fiber": largest_count_fiber(12)},
        "adapter_counterexample": {"margin_start": str(m0),
                                   "after_update_a_only": str(m0),
                                   "after_update_b_only": str(m0),
                                   "after_composition": str(m0 - 1),
                                   "cumulative_hessian_lower_bound": str(margin_lower_bound(m0, 0, 1, 2))},
        "persona_reweight": {"prior": [str(v) for v in p],
                             "after": [str(v) for v in q],
                             "tv": str(total_variation(p, q)),
                             "sharp_range_bound_for_m1_M9": "1/2"},
        "trajectory_bound_example": str(trajectory_divergence_bound(Fraction(1, 10), 4)),
        "sparse_geometry": {"line_sign_flip_sin_squared": str(line_subspace_sin_squared((1, 0), (-1, 0))),
                            "two_atom_min_singular_squared": str(unit_pair_min_singular_squared(
                                (1, 0), (Fraction(9999, 10001), Fraction(200, 10001))))},
    }


if __name__ == "__main__":
    print(json.dumps(exact_receipt(), indent=2, sort_keys=True))
