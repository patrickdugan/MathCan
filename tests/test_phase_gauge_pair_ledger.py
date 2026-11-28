"""Independent exact finite oracles for COE-07 pairwise clock-gauge identities."""
from itertools import combinations
from math import comb
import unittest


def necklace(word, T):
    mask=(1<<T)-1
    return min(((word<<shift)|(word>>(T-shift)))&mask for shift in range(T))


def sharp_capacity(n,T,w):
    reps={necklace(sum(1<<j for j in c),T) for c in combinations(range(T),w)}
    if not n:return 0
    q=min(n,len(reps));a,r=divmod(n,q)
    return comb(n,2)-(q-r)*comb(a,2)-r*comb(a+1,2)


def pair_count(words,fn):
    return sum(fn(a)!=fn(b) for a,b in combinations(words,2))


class TestPhaseGaugePairLedger(unittest.TestCase):
    def test_length_eight_weight_four_has_ten_necklaces(self):
        self.assertEqual(len({necklace(sum(1<<j for j in c),8)
                              for c in combinations(range(8),4)}),10)

    def test_one_weight_capacity_sharp_on_tiny_instances(self):
        # An explicit balanced allocation achieves the written formula.
        for T in range(3,9):
            for w in range(T+1):
                reps=sorted({necklace(sum(1<<j for j in c),T)
                             for c in combinations(range(T),w)})
                for n in range(1,12):
                    q=min(n,len(reps)); selected=[reps[i%q] for i in range(n)]
                    self.assertEqual(pair_count(selected,lambda x:x),sharp_capacity(n,T,w))

    def test_pairwise_merging_cost(self):
        for a in range(25):
            for b in range(25):
                self.assertEqual(comb(a+b,2)-comb(a,2)-comb(b,2),a*b)

    def test_nested_quotient_ledger(self):
        for T in range(2,9):
            words=list(range(1<<T))
            N=lambda w:necklace(w,T)
            C=lambda w:w.bit_count()
            order=pair_count(words,lambda x:x)
            cyc=pair_count(words,N)
            cnt=pair_count(words,C)
            self.assertGreaterEqual(order,cyc)
            self.assertGreaterEqual(cyc,cnt)
            self.assertEqual(order,cnt+(cyc-cnt)+(order-cyc))

    def test_native_arithmetic_cell(self):
        self.assertEqual(1414-1389,25)
        self.assertEqual(1389-1369,20)
        self.assertLess(1414,1795)

if __name__=='__main__':unittest.main()
