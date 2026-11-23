"""AHR-QPU-01 square, endianness and protocol fixtures."""

from dataclasses import asdict, dataclass
from itertools import product
from math import pi

import numpy as np

PRIMES = (2, 3)
ENERGIES = (0.0, np.log(2), np.log(3), np.log(6))
GENERIC_MATCH = (0.0, np.log(6), np.log(3), np.log(2))
EDGES = ((0, 1), (0, 2), (1, 3), (2, 3))
CLOSING = (1, 3)
FULL_MASK = (True,) * 4
TREE_MASK = (True, True, True, False)
OFFSETS = np.arange(4) * pi/2
TIMES = (0.8, 1.2, 1.6)
PRIMARY_TIME = 1.6
PLANTED_PHASE = 0.73
REFERENCE_OFFSET = 0.19
ORDER_SEED = 144739


@dataclass(frozen=True)
class Case:
    arm: str
    time: float
    quadrant: int
    theta: float
    energy: tuple = ENERGIES
    mask: tuple = FULL_MASK
    reference_offset: float = REFERENCE_OFFSET

    @property
    def phase(self):
        return float(self.theta + self.reference_offset + OFFSETS[self.quadrant])

    @property
    def id(self):
        return f"{self.arm}_t{self.time:.1f}_q{self.quadrant}"

    def record(self):
        return {"id": self.id, **asdict(self), "programmed_phase": self.phase}


def pilot():
    cases = [Case(arm, time, q, theta) for time in TIMES
             for arm, theta in (("reference", 0), ("signal", PLANTED_PHASE)) for q in range(4)]
    cases += [Case(arm, PRIMARY_TIME, q, theta, energies, mask) for arm, theta, energies, mask in (
        ("reversed", -PLANTED_PHASE, ENERGIES, FULL_MASK),
        ("tree", PLANTED_PHASE, ENERGIES, TREE_MASK),
        ("matched_detuning", PLANTED_PHASE, GENERIC_MATCH, FULL_MASK),
    ) for q in range(4)]
    indices = np.random.default_rng(ORDER_SEED).permutation(len(cases))
    return [cases[index] for index in indices]


def square(phi, energies=ENERGIES, mask=FULL_MASK, j=1.0):
    """H[dest, source] is positive-phase hopping along (1,3)."""
    h = np.diag(energies).astype(complex)
    for edge, active in zip(EDGES, mask, strict=True):
        if active:
            low, high = edge
            value = j * np.exp(1j * phi) if edge == CLOSING else j
            h[high, low], h[low, high] = value, np.conj(value)
    return h


def square_paulis(phi, energies=ENERGIES, mask=FULL_MASK, j=1.0):
    """Direct projector expansion. The left Pauli character acts on q1=y."""
    a, b, c, d = energies
    coefficients = {
        "II": (a+b+c+d)/4, "IZ": (a-b+c-d)/4,
        "ZI": (a+b-c-d)/4, "ZZ": (a-b-c+d)/4,
    }
    for (low, high), active in zip(EDGES, mask, strict=True):
        if not active:
            continue
        axis = (high ^ low).bit_length() - 1
        control = 1 - axis
        angle = phi if (low, high) == CLOSING else 0.0
        for axis_pauli, strength in (("X", j*np.cos(angle)), ("Y", j*np.sin(angle))):
            for projector in ("I", "Z"):
                label = ["I", "I"]
                label[1-axis], label[1-control] = axis_pauli, projector
                sign = -1 if projector == "Z" and (low >> control) & 1 else 1
                key = "".join(label)
                coefficients[key] = coefficients.get(key, 0.0) + strength*sign/2
    return [(label, float(value)) for label, value in coefficients.items() if abs(value) > 1e-15]


def masks():
    return tuple(product((False, True), repeat=4))


def rephase(h, vertex_angles):
    phase = np.exp(1j * np.asarray(vertex_angles))
    return phase[:, None] * h * phase.conj()[None, :]
