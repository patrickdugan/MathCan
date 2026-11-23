"""Addressable Fourier measurements and independent exact-matrix response."""
from dataclasses import dataclass
from itertools import product

import numpy as np
from scipy.linalg import expm

from q3_hamiltonian import D1, EDGE_INDEX, EDGES, ENERGIES, FACES, face_flux, face_weight, matrix

MARKS = ((0, 1), (2, 6), (5, 7))


@dataclass(frozen=True)
class Setting:
    face: int
    start: int
    edge: int
    direction: int
    offset: float
    time: float
    offset_index: int
    offset_count: int

    @property
    def id(self):
        return f"f{self.face}_x{self.start}_e{self.edge}_t{self.time:.6f}_q{self.offset_index}of{self.offset_count}"


def selector(index):
    i, j, u = FACES[index]
    on_face = D1[index]
    edge = next(e for e in sorted(MARKS) if on_face[EDGE_INDEX[e]])
    direction = int(on_face[EDGE_INDEX[edge]])
    other_axis = (1 << i) ^ (1 << j) ^ (edge[0] ^ edge[1])
    # Use the facing away corner, so only one of the two incident squares is
    # accessible in four steps. Both orientations use the same convention.
    return edge[0] ^ other_axis, EDGE_INDEX[edge], direction


def settings(times, count=4):
    return [Setting(f, *selector(f), float(2 * np.pi * k / count), float(t), k, count)
            for f, t, k in product(range(6), times, range(count))]


def probability(phases, cases, magnitudes=1.0, energies=ENERGIES):
    """Evaluate an arbitrary batch of fields against a common setting list."""
    phases = np.asarray(phases)
    shifts = np.zeros((len(cases), 12))
    shifts[np.arange(len(cases)), [c.edge for c in cases]] = [c.direction * c.offset for c in cases]
    h = matrix(phases[..., None, :] + shifts, magnitudes, energies)
    values, vectors = np.linalg.eigh(h)
    starts = np.array([c.start for c in cases])
    weights = abs(vectors[..., np.arange(len(cases)), starts, :]) ** 2
    time = np.asarray([c.time for c in cases])
    return np.abs(np.sum(weights * np.exp(-1j * values * time[:, None]), axis=-1)) ** 2


def direct_probability(phases, case, magnitudes=1.0, energies=ENERGIES):
    field = np.array(phases, dtype=float, copy=True)
    field[case.edge] += case.direction * case.offset
    u = expm(-1j * case.time * matrix(field, magnitudes, energies))
    return float(abs(u[case.start, case.start]) ** 2)


def harmonic(p, order=1):
    count = np.shape(p)[-1]
    offsets = 2 * np.pi * np.arange(count) / count
    return (2 / count) * (np.asarray(p) @ np.exp(-1j * order * offsets))


def short_time_audit(phases, magnitudes):
    expected = np.array([face_weight(magnitudes, f) for f in range(len(FACES))])
    expected = expected * np.exp(1j * face_flux(phases))
    errors = []
    for time in (.12, .06, .03):
        cases = settings([time])
        p = probability(phases, cases, magnitudes)
        independent = [direct_probability(phases, c, magnitudes) for c in cases]
        np.testing.assert_allclose(p, independent, atol=2e-14, rtol=0)
        errors.append(abs(6 * harmonic(p.reshape(6, 4)) / time**4 - expected))
    assert np.all(errors[-1] < .28 * errors[-2])
    return {"selectors": [{"face": f, "start": selector(f)[0], "edge": EDGES[selector(f)[1]],
                           "direction": selector(f)[2]} for f in range(6)],
            "times": [.12, .06, .03], "scaled_complex_errors": np.asarray(errors).tolist()}
