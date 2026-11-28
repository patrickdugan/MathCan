"""Independent standard-library finite checks for the dihedral observer ledger."""
from collections import Counter, defaultdict
from itertools import product, combinations
from math import comb
import unittest


def rot(word,T,j):
    j %= T
    return ((word << j) | (word >> (T-j))) & ((1 << T)-1)

def rev(word,T):
    return sum(((word >> i)&1) << (T-1-i) for i in range(T))

def neck(word,T):return min(rot(word,T,j) for j in range(T))
def brace(word,T):return min(neck(word,T),neck(rev(word,T),T))

def exact_formula(words, labels, descriptor):
    classes=defaultdict(list)
    for word,label in zip(words,labels):classes[descriptor(word)].append(label)
    eligible=sum(a!=b for a,b in combinations(labels,2))
    collisions=sum(comb(len(g),2)-sum(comb(v,2) for v in Counter(g).values())
                   for g in classes.values())
    return eligible-collisions


class TestDihedralLedger(unittest.TestCase):
    def test_burnside_count_at_eight_visits(self):
        for weight,counts in ((3,(7,5)),(4,(10,8)),(5,(7,5))):
            xs=[word for word in range(256) if word.bit_count()==weight]
            n={neck(x,8) for x in xs};b={brace(x,8) for x in xs}
            fixed=sum(neck(rev(x,8),8)==x for x in n)
            self.assertEqual((len(n),len(b)),counts)
            self.assertEqual(len(n)+fixed,2*len(b))

    def test_all_labelled_small_quotients(self):
        for words in product(range(4),repeat=3):
            for labels in product((1,2),repeat=3):
                T=2
                funcs=(lambda x:x,lambda x:neck(x,T),lambda x:brace(x,T),int.bit_count)
                by=[exact_formula(words,labels,fn) for fn in funcs]
                self.assertEqual(by,sorted(by,reverse=True))
                self.assertEqual(by[0]-by[3],sum(by[i]-by[i+1] for i in range(3)))

    def test_class_majority_merge(self):
        for a,b,c,d in product(range(6),repeat=4):
            self.assertLessEqual(max(a+c,b+d),max(a,b)+max(c,d))
            self.assertEqual((a+b)*(c+d),a*c+b*d+a*d+b*c)

    def test_pinned_arithmetic_cells(self):
        for T,vals in ((8,(1414,1389,1389,1369)),(16,(1447,1428,1428,1422))):
            o,c,d,h=vals
            self.assertEqual(o-h,(o-c)+(c-d)+(d-h))
            self.assertTrue(1795>=o>=c>=d>=h)

if __name__=='__main__':unittest.main()
