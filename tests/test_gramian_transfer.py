"""SPC-07 exact standard-library oracles for phase-gauge Gramian transfer."""
from fractions import Fraction as F
from itertools import product, permutations
import unittest


def top_indices(values, rank):
    if not (1<=rank<=len(values)):
        raise ValueError('invalid rank')
    return tuple(sorted(range(len(values)),key=lambda i:(-values[i],i))[:rank])


def diagonal_capture(values, ids):
    return sum((values[i] for i in ids),F(0))


def transfer_regret(s,t,rank):
    p=top_indices(s,rank)
    best=top_indices(t,rank)
    epsilon=max(abs(F(a)-F(b)) for a,b in zip(s,t))
    return diagonal_capture(t,best)-diagonal_capture(t,p),2*rank*epsilon


class ExactTransferTests(unittest.TestCase):
    def test_rank_one_regret_bound_is_sharp(self):
        s=(F(1),F(1));t=(F(0),F(2))
        regret,bound=transfer_regret(s,t,1)
        self.assertEqual(regret,F(2))
        self.assertEqual(regret,bound)

    def test_all_small_diagonal_gramians(self):
        choices=range(4)
        for n in (2,3,4):
            vectors=list(product(choices,repeat=n))
            for s in vectors:
                for t in vectors:
                    for rank in range(1,n):
                        regret,bound=transfer_regret(s,t,rank)
                        self.assertGreaterEqual(regret,0)
                        self.assertLessEqual(regret,bound)

    def test_orthogonal_permutation_gauge_exact_conjugacy(self):
        values=(F(9),F(5),F(3),F(1))
        for perm in permutations(range(4)):
            # Target diagonal entry i is source entry perm[i].
            transformed=tuple(values[i] for i in perm)
            src_opt=top_indices(values,2)
            mapped={perm.index(i) for i in src_opt}
            tgt_opt=top_indices(transformed,2)
            self.assertEqual(diagonal_capture(transformed,mapped),
                             diagonal_capture(transformed,tgt_opt))

    def test_raw_basis_depends_on_coordinate_labels(self):
        src=(F(10),F(0));tgt=(F(0),F(10))
        raw_regret,_=transfer_regret(src,tgt,1)
        self.assertEqual(raw_regret,10)
        # Conjugating the source by a coordinate swap removes the gap.
        swapped_src=src[::-1]
        self.assertEqual(transfer_regret(swapped_src,tgt,1)[0],0)

    def test_gauge_rotation_two_by_two_preserves_quadratic_energy(self):
        # The integer orthogonal map (x,y) -> (-y,x) has inverse (y,-x).
        for a,b in product(range(-5,6),repeat=2):
            x,y=-b,a
            self.assertEqual(x*x+y*y,a*a+b*b)
            self.assertEqual((y,-x),(a,b))

    def test_phase_margin_nearest_neighbor_certificate(self):
        # If the correct phase is within e of the perturbed state, and each
        # wrong phase is at distance >2e from it, the nearest phase stays put.
        for radius in range(1,9):
            for e in range(0,radius):
                correct=radius
                wrong=-radius
                perturbed=correct-e
                if 2*e < abs(correct-wrong):
                    self.assertLess(abs(perturbed-correct),abs(perturbed-wrong))

if __name__=='__main__':unittest.main()
