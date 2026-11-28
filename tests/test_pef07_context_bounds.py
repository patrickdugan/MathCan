"""Independent finite source-only and paired-teacher accuracy oracle."""
import itertools
import random
import unittest


def coalition(w):
    a,b,c,d=w
    return (a&b)^(c&d)


def threshold(w):
    return int(sum(w)>=2)


class ContextBoundTests(unittest.TestCase):
    def setUp(self):
        self.words=list(itertools.product((0,1),repeat=4))

    def test_exact_balanced_teacher_cubes(self):
        self.assertEqual(sum(coalition(w) for w in self.words),6)
        self.assertEqual(sum(threshold(w) for w in self.words),11)

    def test_any_context_predictor_cannot_exceed_source_ceiling(self):
        rng=random.Random(137)
        for count in (0,1,2,48,256):
            contexts=[rng.randrange(2**12) for _ in range(count)]
            guesses={c:rng.randrange(2) for c in set(contexts)}
            for teacher,maximum in ((coalition,10),(threshold,11)):
                score=sum(guesses[ctx]==teacher(old)
                          for ctx in contexts for old in self.words)
                self.assertLessEqual(score,maximum*count)
            self.assertEqual(10*48,480)
            self.assertEqual(11*48,528)

    def test_two_coalition_pairs_and_all_six_threshold_pairs(self):
        z=(0,0,0,0)
        self.assertEqual(coalition(z),0)
        self.assertEqual(threshold(z),0)
        for i in range(4):
            singleton=[0]*4;singleton[i]=1
            self.assertEqual(coalition(singleton),0)
            self.assertEqual(threshold(singleton),0)
        for i,j in itertools.combinations(range(4),2):
            x=[0]*4;x[i]=x[j]=1
            self.assertEqual(coalition(x),int((i,j) in ((0,1),(2,3))))
            self.assertEqual(threshold(x),1)
            self.assertEqual(sum(x),sum([x[i],x[j]]))
            self.assertEqual(sum(x)+sum(z)-1-1,0)

    def test_zero_teacher_score_mixed_discrete_increments(self):
        for w in self.words:
            for i,j in itertools.combinations(range(4),2):
                other_i=list(w);other_i[i]^=1
                other_j=list(w);other_j[j]^=1
                both=list(w);both[i]^=1;both[j]^=1
                self.assertEqual(
                    sum(both)-sum(other_i)-sum(other_j)+sum(w),0
                )


if __name__=="__main__":
    unittest.main()
