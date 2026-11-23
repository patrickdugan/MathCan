"""Exact full-space oracle in Qiskit basis |internal,z,y,x>."""
from dataclasses import dataclass
from itertools import pairwise

import numpy as np

I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)
AXIS = {"x": X, "z": Z}
A = (0, 1, 3, 2, 0)
B = (0, 1, 5, 4, 0)
ALPHA, BETA = np.pi / 4, np.pi / 2
LABELS = ("AB", "BA")
STRESS_ANGLE_SEED = 6042027


@dataclass(frozen=True)
class Case:
    id: str
    arm: str
    label: str
    alpha: float = ALPHA
    beta: float = BETA
    dwell_us: float = 0.
    prepared: int = 0


def rotation(axis, angle):
    return np.cos(angle) * I + 1j * np.sin(angle) * AXIS[axis]


def edge_link(u, v, unitary):
    distance = (u ^ v).bit_count()
    if not (0 <= u < 8 and 0 <= v < 8 and distance == 1):
        raise ValueError("an edge must join neighboring cube vertices")
    if np.shape(unitary) != (2, 2) or not np.allclose(unitary.conj().T @ unitary, I):
        raise ValueError("internal link must be unitary")
    a, b = [u, u + 8], [v, v + 8]
    block = np.eye(16, dtype=complex)
    block[np.ix_(a, a)] = 0
    block[np.ix_(b, b)] = 0
    block[np.ix_(b, a)] = unitary
    block[np.ix_(a, b)] = unitary.conj().T
    return block


def routes(case):
    first, second = (A, B) if case.label == "AB" else (B, A)
    if case.arm == "reverse":
        return first[::-1], second[::-1]
    if case.arm == "inverse":
        return first, first[::-1]
    return first, second


def link_rotation(case, u, v):
    if case.arm == "pure_gauge":
        vertex_frame = [0., -.21, .18, .46, -.32, .14, .11, -.31]
        return "x", vertex_frame[v] - vertex_frame[u]
    marked = {
        (1, 3): ("x", case.alpha),
        (1, 5): ("x" if case.arm == "commuting" else "z", case.beta),
    }
    if case.arm == "identity":
        return "z", 0.
    if case.arm == "same_link":
        marked.pop((1, 5))
    axis, angle = marked.get(tuple(sorted((u, v))), ("z", 0.))
    return axis, angle if u < v else -angle


def walk(case, route):
    unitary = np.eye(16, dtype=complex)
    for u, v in pairwise(route):
        unitary = edge_link(u, v, rotation(*link_rotation(case, u, v))) @ unitary
    return unitary


def oracle(case):
    vector = np.zeros(16, dtype=complex)
    vector[0] = 1.
    log = []
    for route in routes(case):
        for u, v in pairwise(route):
            operator = edge_link(u, v, rotation(*link_rotation(case, u, v)))
            vector = operator @ vector
            log.append({"from": u, "to": v, "site_probability": float(
                abs(vector[v])**2 + abs(vector[8+v])**2)})
    internal = vector[[0, 8]]
    return vector, internal, log


def audit():
    pilot = [Case(label, "signal", label) for label in LABELS]
    outcomes = [oracle(case) for case in pilot]
    y = [float((state.conj() @ Y @ state).real) for _, state, _ in outcomes]
    np.testing.assert_allclose(y, [-1, 1], atol=1e-13)
    assert all(len(steps) == 8 and all(r["site_probability"] > 1 - 1e-13 for r in steps)
               for _, _, steps in outcomes)
    max_distance_error = 0.
    for alpha, beta in np.random.default_rng(41421).uniform(-np.pi, np.pi, (20, 2)):
        cases = [Case(label, "signal", label, alpha, beta) for label in LABELS]
        states = [oracle(c)[1] for c in cases]
        # The two pure states are normalized; the determinant is stable near 0.
        d = abs(np.linalg.det(np.column_stack(states)))
        max_distance_error = max(max_distance_error, abs(d - abs(np.sin(2*alpha)*np.sin(beta))))
        for route in (A, B):
            forward = walk(cases[0], route)
            np.testing.assert_allclose(walk(cases[0], route[::-1]), forward.conj().T, atol=2e-14)
    assert max_distance_error < 1e-12
    return {"route_steps": {c.label: o[2] for c, o in zip(pilot, outcomes)},
            "orthogonal_y": y, "angle_pairs": 20, "max_trace_distance_error": max_distance_error}


def cases():
    result = [Case(f"{arm}/{label}", arm, label) for arm in
              ("signal", "commuting", "identity", "reverse", "inverse", "same_link", "pure_gauge",
               "direct", "order_register") for label in LABELS]
    result += [Case(f"memory/{d}/{label}", "signal", label, dwell_us=d)
               for d in (2, 8, 24) for label in LABELS]
    result += [Case(f"{arm}_memory/{d}/{label}", arm, label, dwell_us=d)
               for arm in ("direct", "order_register") for d in (2, 8, 24) for label in LABELS]
    angles = np.random.default_rng(STRESS_ANGLE_SEED).uniform(
        [.2, .45], [1.35, 2.65], size=(6, 2))
    result += [Case(f"heldout/{k}/{label}", "signal", label, float(a), float(b))
               for k, (a, b) in enumerate(angles) for label in LABELS]
    result += [Case(f"heldout_direct/{k}/{label}", "direct", label, float(a), float(b))
               for k, (a, b) in enumerate(angles) for label in LABELS]
    result += [Case(f"prepare/{k:04b}", "prepare", "AB", prepared=k) for k in range(16)]
    return result
