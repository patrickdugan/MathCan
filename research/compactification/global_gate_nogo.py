"""NRF-05: exact-rational full-linear-observation gate-collapse audit.

This checks sufficient matrix hypotheses for the full-domain tanh residual
factorization no-go theorem. A finite-field rank certificate for binary32
weights is handled by the private checkpoint verifier.
"""
from fractions import Fraction as Q

from research.compactification.observable_closure import (
    rref_basis, robust_gate_closure,
)


def _square(value, label: str):
    if not value or any(len(row) != len(value) for row in value):
        raise ValueError(f"{label} must be a nonempty square matrix")
    return tuple(tuple(Q(x) for x in row) for row in value)


def _product(w1, w2):
    n = len(w1)
    return tuple(
        tuple(sum((w1[i][k] * w2[k][j] for k in range(n)), Q(0))
              for j in range(n))
        for i in range(n)
    )


def full_linear_collapse_hypotheses(w1, w2):
    """Sufficient criterion applying to every nonzero linear observation.

    Requiring both weights invertible and every W1W2 entry nonzero forces
    the only globally exact linear observation rowspaces to have dimension
    zero or n for tanh recurrence on all R^n with nonzero branch scale.
    """
    a = _square(w1, "W1")
    b = _square(w2, "W2")
    if len(a) != len(b):
        raise ValueError("weight dimensions differ")
    n = len(a)
    prod = _product(a, b)
    return {
        "dimension": n,
        "w1_rank": len(rref_basis(a, n)),
        "w2_rank": len(rref_basis(b, n)),
        "zero_interaction_entries": sum(v == 0 for row in prod for v in row),
        "full_linear_no_go": (
            len(rref_basis(a, n)) == n
            and len(rref_basis(b, n)) == n
            and all(v != 0 for row in prod for v in row)
        ),
    }


def test_observation_closure(w1, w2, observation):
    """Return the *actual* exact rational rowspace closure for a small case."""
    a = _square(w1, "W1")
    b = _square(w2, "W2")
    n = len(a)
    if len(b) != n or not observation:
        raise ValueError("dimension or observation mismatch")
    rows = tuple(tuple(Q(x) for x in row) for row in observation)
    if any(len(row) != n for row in rows):
        raise ValueError("observation is the wrong width")
    if len(rref_basis(rows, n)) == 0:
        raise ValueError("a nonzero observation is required")
    return robust_gate_closure(rows, a, b)["rank"]
