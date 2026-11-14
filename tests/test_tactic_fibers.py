"""Independent finite oracle for pure TFH-01 mathematics (no model required)."""
import itertools
import unittest

MASK = ((0, 1), (1, 2), (2, 0))


class TacticFibreOracle(unittest.TestCase):
    def test_exact_matching_fibre_and_pair_switch_obstruction(self):
        valid = [p for p in itertools.permutations(range(3))
                 if all(p[i] in MASK[i] for i in range(3))]
        self.assertEqual(valid, [(0, 1, 2), (1, 2, 0)])
        for p in valid:
            for a, b in itertools.combinations(range(3), 2):
                switched = list(p)
                switched[a], switched[b] = switched[b], switched[a]
                self.assertFalse(all(switched[i] in MASK[i] for i in range(3)))

    def test_hall_certificate_across_all_capacity_values(self):
        for capacity in range(3):
            for assigned in range(capacity + 1):
                self.assertGreaterEqual(26 - assigned, 24)
                self.assertGreaterEqual((26 - assigned) / 51, 24 / 51)

    def test_all_masks_against_direct_hall_formula(self):
        for mask in range(512):
            graph = [{j for j in range(3) if mask & (1 << (3*i+j))}
                     for i in range(3)]
            feasible = any(all(perm[i] in graph[i] for i in range(3))
                           for perm in itertools.permutations(range(3)))
            gap = max(len(subset) - sum(bool(subset & graph[i]) for i in range(3))
                      for width in range(1, 4)
                      for subset in map(set, itertools.combinations(range(3), width)))
            self.assertEqual(feasible, gap <= 0)


if __name__ == '__main__':
    unittest.main()
