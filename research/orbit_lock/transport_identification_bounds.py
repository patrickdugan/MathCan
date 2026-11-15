"""OLM-04: standalone exact arithmetic audit of the six-vertex overlap histogram.

Histograms are fixture data enumerated independently in Compactification-Theory
SMC-04. The checker audits the reported counts and exact survival expectation;
it does not itself regenerate the underlying 10,800 group-action comparisons.
"""
from fractions import Fraction
from math import sqrt

# Number of candidate hypotheses with exactly j agreement cases among N
# uniformly sampled permutation inputs, including the one true hypothesis.
FULL_HIST = {
    0:768, 16:540, 24:720, 32:270, 36:1280, 40:864, 48:2460,
    60:1152, 72:2000, 80:540, 96:90, 144:100, 336:15, 720:1,
}
TRAIN_HIST = {
    0:868, 8:144, 12:96, 16:396, 18:512, 24:1056, 30:384,
    32:666, 36:1344, 40:576, 42:768, 48:1152, 54:896,
    56:432, 60:480, 64:612, 72:192, 80:108, 96:54,
    144:48, 192:3, 288:12, 576:1,
}


def check_histogram(hist, support, candidates=10800):
    if any(type(k) is not int or k < 0 or k > support
           or type(v) is not int or v < 0 for k,v in hist.items()):
        raise ValueError("invalid histogram")
    if sum(hist.values()) != candidates or hist.get(support) != 1:
        raise ValueError("histogram must contain every candidate and one true model")
    return Fraction(max(k for k in hist if k < support and hist[k]), support)


def expected_false(hist, support, n):
    check_histogram(hist, support)
    if n < 1:
        raise ValueError("positive example count required")
    return sum((Fraction(k,support)**n *
                (count - (1 if k == support else 0))
                for k,count in hist.items()),Fraction(0))


def noisy_union_bound(hist, support, n, eps=Fraction(1,4), m=15):
    check_histogram(hist, support)
    if not (0 <= eps <= 1) or n < 1 or m < 2:
        raise ValueError("invalid parameters")
    a=float(1-eps+eps/m)
    b=float(eps/m)
    factor=(sqrt(a)-sqrt(b))**2
    risk=sum(
        (count-(1 if j==support else 0)) *
        (1-(1-j/support)*factor)**n
        for j,count in hist.items()
    )
    return min(1.0,risk)


def audit():
    alpha_full=check_histogram(FULL_HIST,720)
    alpha_train=check_histogram(TRAIN_HIST,576)
    assert alpha_full == Fraction(7,15)
    assert alpha_train == Fraction(1,2)
    assert expected_false(TRAIN_HIST,576,1) == 719
    assert expected_false(TRAIN_HIST,576,2) == Fraction(572,9)
    assert expected_false(TRAIN_HIST,576,12) == Fraction(
        207626724431490125202001, 70663864180791861451948032)
    assert 15**3 < 10800 <= 15**4
    return {
        "hypotheses":10800,
        "full_alpha_max":str(alpha_full),
        "restricted_alpha_max":str(alpha_train),
        "first_positive_remaining":1+int(expected_false(TRAIN_HIST,576,1)),
        "expected_false_n8":str(expected_false(TRAIN_HIST,576,8)),
        "expected_false_n12":str(expected_false(TRAIN_HIST,576,12)),
        "noisy_25pct_union_n24":noisy_union_bound(TRAIN_HIST,576,24),
        "noisy_25pct_union_n32":noisy_union_bound(TRAIN_HIST,576,32),
        "independent_queries_require_n_at_least":4,
        "scope":"Exact post-enumeration arithmetic and Chernoff upper bounds",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(audit(),indent=2))
