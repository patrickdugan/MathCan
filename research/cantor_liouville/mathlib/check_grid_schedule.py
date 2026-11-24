"""Exact finite regression controls for CLN06C / CLN07A (not a Lean proof)."""
from fractions import Fraction
from itertools import product


def check_grid():
    cases = 0
    for Q in range(2, 10):
        for M in range(1, 65):
            for J in range(1, 17):
                grid = [M + j*M//J for j in range((Q-1)*J)]
                assert all(M <= t < Q*M for t in grid)
                for N in range(M, Q*M):
                    j = J*(N-M)//M
                    N0 = M+j*M//J
                    assert j < len(grid) and M <= N0 <= N
                    assert J*(N-N0) < M+J
                    cases += 1
    assert cases == 1198080
    return cases


def check_schedule():
    for j in range(14):
        d = 2**(j+2)
        m = 2**d
        assert m >= 2*d+j+2
        assert 2*m < m*m
        # Exponent comparison avoids constructing 2**m.
        assert 1+2*d+(j+1) <= m
    return 14


def check_means():
    cases = 0
    for L in range(1, 10):
        for u in product((-1, 0, 1), repeat=L):
            ss = [0]
            for v in u:
                ss.append(ss[-1]+v)
            for k in range(1, L+1):
                assert Fraction(abs(ss[L]), L) <= Fraction(abs(ss[k]), k)+Fraction(L-k,L)
                cases += 1
    assert cases == 250959
    return cases


if __name__ == "__main__":
    print("grid cases", check_grid())
    print("schedule exponent certificates", check_schedule())
    print("mean interpolation cases", check_means())
