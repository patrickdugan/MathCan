import unittest
from itertools import permutations
from math import gcd
from research.collatz_resonance.collatz_core import analyze, modular_labels
from research.collatz_resonance.donor_census import count_root, census, branch


def same_trace(core, a, b):
    seen = set()
    while (a,b) not in seen:
        if branch(a) != branch(b):
            return False
        seen.add((a,b))
        a, b = core.successors[a], core.successors[b]
    return True


def brute(d,h):
    core = analyze(d)
    q = modular_labels(d)
    def future(n):
        for _ in range(h):
            n = core.successors[n]
        return branch(n)
    ordinary = strong = 0
    for a,b,c in permutations(core.states,3):
        if len({(q[n%d],branch(n),core.basin[n]) for n in (a,b,c)}) != 1:
            continue
        if future(a) == future(b) or future(a) != future(c):
            continue
        ordinary += 1
        strong += same_trace(core,a,c)
    return {"ordinary_triplets": ordinary, "infinite_sham_triplets": strong}


class DonorTests(unittest.TestCase):
    def test_brute_force(self):
        for d in (1,5,13,17,25,29,37,73):
            for h in (1,2):
                self.assertEqual(count_root(d)["horizons"][str(h)],brute(d,h))

    def test_reference_census(self):
        r = census()
        self.assertEqual(r["states"],44204)
        self.assertEqual(r["horizons"]["1"]["ordinary_roots"],169)
        self.assertEqual(r["horizons"]["1"]["ordinary_triplets"],138645894)
        self.assertEqual(r["horizons"]["2"]["ordinary_triplets"],138543826)
        self.assertEqual(r["horizons"]["1"]["infinite_sham_triplets"],5942)
        self.assertEqual(r["horizons"]["2"]["infinite_sham_triplets"],5570)
        self.assertEqual(r["infinite_sham_root_union"],41)
        self.assertEqual(r["infinite_sham_root_intersection"],38)
