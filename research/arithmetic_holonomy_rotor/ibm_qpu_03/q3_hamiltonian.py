"""Oriented three-prime cube in Qiskit's |zyx> basis."""
from math import prod

import numpy as np

EDGES = tuple(sorted((u, u ^ (1 << axis)) for u in range(8)
                     for axis in range(3) if not u >> axis & 1))
EDGE_INDEX = {edge: i for i, edge in enumerate(EDGES)}
FACES = tuple((i, j, u) for i in range(3) for j in range(i + 1, 3)
              for u in range(8) if not (u >> i & 1 or u >> j & 1))
TREE = ((0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 6), (3, 7))
CHORDS = tuple(edge for edge in EDGES if edge not in TREE)
CHORD_COLUMNS = [EDGE_INDEX[edge] for edge in CHORDS]
BIANCHI = np.array([-1, 1, 1, -1, -1, 1], dtype=int)
BITS = np.array([[(u >> axis) & 1 for axis in range(3)] for u in range(8)])
ENERGIES = BITS @ np.log([2, 3, 5])
EDGE_U, EDGE_V = np.asarray(EDGES).T
# The first five face rows in the AHR-09 tree gauge have a unimodular inverse.
CHORD_INVERSE = np.array([[-1, 0, 0, 0, 0], [0, 0, -1, 0, 0],
                          [0, 0, 0, 0, -1], [-1, 1, 1, -1, -1],
                          [-1, 0, 0, -1, 0]], dtype=int)


def route(face):
    i, j, u = face
    return [u, u ^ (1 << i), u ^ (1 << i) ^ (1 << j), u ^ (1 << j), u]


def chain():
    d0 = np.zeros((12, 8), dtype=int)
    d0[np.arange(12), EDGE_U] = -1
    d0[np.arange(12), EDGE_V] = 1
    d1 = np.zeros((6, 12), dtype=int)
    for f, face in enumerate(FACES):
        vertices = route(face)
        for u, v in zip(vertices, vertices[1:]):
            d1[f, EDGE_INDEX[tuple(sorted((u, v)))]] = 1 if u < v else -1
    return d0, d1, BIANCHI[None, :]


D0, D1, D2 = chain()


def wrap(angles):
    return (np.asarray(angles) + np.pi) % (2 * np.pi) - np.pi


def chord_field(chords):
    chords = np.asarray(chords)
    phases = np.zeros((*chords.shape[:-1], 12))
    phases[..., CHORD_COLUMNS] = chords
    return phases


def gauge_transform(phases, vertex_phases):
    return np.asarray(phases) - np.asarray(vertex_phases) @ D0.T


def phases_from_faces(faces):
    return np.asarray(faces)[..., :5] @ CHORD_INVERSE.T


def face_flux(phases):
    return wrap(np.asarray(phases) @ D1.T)


def face_weight(magnitudes, index):
    return prod(np.asarray(magnitudes)[D1[index] != 0])


def matrix(phases, magnitudes=1.0, energies=ENERGIES):
    phases = np.asarray(phases, dtype=float)
    if phases.shape[-1] != 12 or np.any(np.asarray(magnitudes) < 0):
        raise ValueError("expected twelve oriented edge phases and nonnegative hoppings")
    values = magnitudes * np.exp(1j * phases)
    h = np.zeros((*phases.shape[:-1], 8, 8), dtype=complex)
    diagonal = np.arange(8)
    h[..., diagonal, diagonal] = energies
    h[..., EDGE_U, EDGE_V] = values
    h[..., EDGE_V, EDGE_U] = values.conj()
    return h


def audit():
    # Integer witnesses prove the claimed ranks and all five unit Smith factors.
    # The incidence submatrix of a rooted tree has determinant +/-1 (delete
    # leaves recursively). A unit minor and the left null vector bound d1.
    assert not np.any(D1 @ D0) and not np.any(D2 @ D1)
    minor = D1[:5, CHORD_COLUMNS]
    assert np.array_equal(minor @ CHORD_INVERSE, np.eye(5, dtype=int))
    assert np.array_equal(CHORD_INVERSE @ minor, np.eye(5, dtype=int))
    assert np.array_equal(D0 @ np.ones(8, dtype=int), np.zeros(12, dtype=int))
    tree_rows = [EDGE_INDEX[e] for e in TREE]
    assert round(np.linalg.det(D0[tree_rows, 1:])) in (-1, 1)
    assert np.any(D2)
    return {"ranks": [7, 5, 1], "d1_smith_diagonal": [1, 1, 1, 1, 1, 0],
            "edges": EDGES, "faces": FACES, "tree": TREE, "chords": CHORDS,
            "boundary": BIANCHI.tolist(), "chord_inverse": CHORD_INVERSE.tolist()}
