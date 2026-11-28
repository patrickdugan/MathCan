"""Independent arithmetic oracles for SPC-02 finite phase arithmetic.

Tests over F_7 are exact, and independent of complex SVD tests in
LoopedTransformers. The complex noise-bound theorem is paper-level.
"""
import itertools
import math
import unittest

ROOTS6 = (1, 3, 2, 6, 4, 5)


def synth6(coeff, s):
    return sum(coeff[f] * ROOTS6[(s*f) % 6] for f in range(6)) % 7


def singleton(frequency, amplitude=1):
    return tuple(amplitude if r == frequency else 0 for r in range(6))


def pair_support(pair):
    return tuple(int(r in pair) for r in range(6))


def det_mod7(rows):
    n = len(rows)
    a = [[v % 7 for v in row] for row in rows]
    det = 1
    for col in range(n):
        pivot = next((i for i in range(col, n) if a[i][col] != 0), None)
        if pivot is None:
            return 0
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        d = a[col][col] % 7
        det = det * d % 7
        inv = pow(d, -1, 7)
        for r in range(col + 1, n):
            q = a[r][col] * inv % 7
            for c in range(col, n):
                a[r][c] = (a[r][c] - q * a[col][c]) % 7
    return det % 7


class FiniteExactSeparation(unittest.TestCase):
    def test_primitive_root_and_character_orthogonality(self):
        self.assertEqual(tuple(pow(3, x, 7) for x in range(6)), ROOTS6)
        for frequency in range(6):
            total = sum(ROOTS6[(frequency * s) % 6] for s in range(6)) % 7
            self.assertEqual(total, 6 if frequency == 0 else 0)

    def test_coprime_two_phase_codes_are_one_sparse_injective(self):
        for stride in (1, 5):
            signatures = []
            for freq in range(6):
                for amplitude in range(1, 7):
                    a = singleton(freq, amplitude)
                    signatures.append((synth6(a, 0), synth6(a, stride)))
            self.assertEqual(len(set(signatures)), 36)

    def test_non_coprime_step_collisions_are_exact(self):
        for step, equal_frequency in ((2, 3), (3, 2), (4, 3)):
            for amplitude in range(1, 7):
                a = singleton(0, amplitude)
                b = singleton(equal_frequency, amplitude)
                self.assertEqual(synth6(a, 0), synth6(b, 0))
                self.assertEqual(synth6(a, step), synth6(b, step))
                self.assertNotEqual(a, b)

    def test_consecutive_four_phase_minors_are_nonzero(self):
        for frequencies in itertools.combinations(range(6), 4):
            rows = [[ROOTS6[(s*f) % 6] for f in frequencies]
                    for s in range(4)]
            self.assertNotEqual(det_mod7(rows), 0)

    def test_an_irregular_schedule_is_singular(self):
        phases = (0, 1, 2, 4)
        found = []
        for frequencies in itertools.combinations(range(6), 4):
            rows = [[ROOTS6[(s*f) % 6] for f in frequencies]
                    for s in phases]
            if det_mod7(rows) == 0:
                found.append(frequencies)
        self.assertTrue(found)

    def test_deferred_family_cardinality_and_phase_zero_collision(self):
        d, k, m = 6, 2, 2
        supports = list(itertools.combinations(range(d), k))
        self.assertEqual(len(supports), math.comb(d, k))
        complete = set()
        first = set()
        for s0, s1 in itertools.product(supports, repeat=m):
            a = [pair_support(s0), pair_support(s1)]
            first.add((synth6(a[0], 0), synth6(a[1], 0)))
            complete.add(tuple(synth6(a[j], phase)
                               for j in range(m) for phase in range(d)))
        self.assertEqual(len(first), 1)
        self.assertEqual(first.pop(), (2, 2))
        self.assertEqual(len(complete), 15**2)


if __name__ == "__main__":
    unittest.main()
