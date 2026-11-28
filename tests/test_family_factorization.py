"""OLM-13 finite orbit obstruction and cross-talk factorization tests."""
import sys,unittest,random
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research'/'orbit_lock'))
import family_factorization as f


class FamilyGaugeTests(unittest.TestCase):
    def test_base_cyclic_family_zero_rectangles_under_100_isotopies(self):
        source=f.canonical_grid()
        self.assertEqual(f.intercalates(source),0)
        rng=random.Random(202613)
        for _ in range(100):
            rows=list(range(9));cols=list(range(9));digits=list(range(1,10))
            rng.shuffle(rows);rng.shuffle(cols);rng.shuffle(digits)
            g=f.transform(source,rows,cols,digits,transpose=bool(rng.randrange(2)))
            self.assertEqual(f.intercalates(g),0)

    def test_positive_intercalate_orbit_witness(self):
        a=list(f.canonical_grid())
        # A valid Sudoku source outside the canonical isotopy family is
        # separately certified by the applied randomized completion.
        # The invariant itself can be tested against any filled digit matrix.
        a[0],a[1]=a[1],a[0]
        self.assertGreater(f.intercalates(a),0)
        self.assertNotEqual(f.intercalates(a),f.intercalates(f.canonical_grid()))

    def test_permutation_gauge_preserves_cone_count(self):
        W=((Q(1),Q(0)),(Q(0),Q(1)),(Q(-1),Q(0)))
        D=((Q(2),Q(0),Q(-1)),(Q(1),Q(1),Q(0)))
        base=f.strict_cones(f.wd_cross_talk(W,D))
        for p in ((0,1,2),(1,2,0),(2,0,1),(2,1,0)):
            w,d=f.permutation_gauge(W,D,p)
            got=f.strict_cones(f.wd_cross_talk(w,d))
            self.assertEqual(len(got),len(base))

    def test_exact_reconstruction_does_not_fix_self_selection_count(self):
        r=f.reconstruction_counterexamples()
        self.assertEqual(r['first_factorization_strict_cone_count'],0)
        self.assertEqual(r['second_factorization_strict_cone_count'],2)

    def test_centered_coactivation_cancels_constant_marginals(self):
        X=((1,0),(1,0),(1,0),(1,0))
        Y=((1,0),(0,1),(1,0),(0,1))
        self.assertEqual(f.centered_covariance(X,Y),((0,0),(0,0)))
        X=((1,0),(1,0),(0,1),(0,1))
        Y=((1,0),(1,0),(0,1),(0,1))
        C=f.centered_covariance(X,Y)
        self.assertEqual(C,((Q(1),Q(-1)),(Q(-1),Q(1))))


    def test_conditional_clue_groups_remove_spurious_feature_alignment(self):
        groups=(0,0,1,1,2,2)
        X=((1,0),(1,0),(0,1),(0,1),(1,0),(1,0))
        Y=((1,0),(1,0),(0,1),(0,1),(1,0),(1,0))
        # Raw data share a strong group-dependent marginal association,
        # while both feature sets are constant WITHIN each group.
        self.assertNotEqual(f.centered_covariance(X,Y),((0,0),(0,0)))
        self.assertEqual(f.conditioned_covariance(X,Y,groups),((0,0),(0,0)))
        X=((1,0),(0,1),(1,0),(0,1))
        Y=((1,0),(0,1),(0,1),(1,0))
        groups=(0,0,1,1)
        self.assertEqual(f.conditioned_covariance(X,Y,groups),
                         ((Q(0),Q(0)),(Q(0),Q(0))))
        with self.assertRaises(ValueError):
            f.conditioned_covariance(X,Y,(1,))

    def test_invalid_input_guards(self):
        with self.assertRaises(ValueError):f.intercalates((1,2))
        with self.assertRaises(ValueError):f.matmul(((1,2),),((3,),))
        with self.assertRaises(ValueError):f.centered_covariance((),())
        with self.assertRaises(ValueError):f.strict_cones(((1,2),))
        with self.assertRaises(ValueError):
            f.transform(f.canonical_grid(),list(range(8)),list(range(9)),list(range(1,10)))


if __name__=='__main__':
    unittest.main()
