"""DEL-04: exact Lagrange isolators for weighted power-trace sequences.

An algebraic witness for a finite-index spectral-growth proof. All
calculations here are rational and exact. The same polynomial identity
holds over any characteristic-zero field.
"""
from fractions import Fraction as F
from research.deligne_sign_audit.power_sum_poles import spectrum, power_trace


def polynomial_mul_linear(coefficients, root):
    """Multiply a coefficient list by X-root, in ascending degree."""
    c = tuple(F(x) for x in coefficients)
    r = F(root)
    output = [F(0) for _ in range(len(c) + 1)]
    for j, a in enumerate(c):
        output[j] -= a * r
        output[j + 1] += a
    return tuple(output)


def polynomial_eval(coefficients, x):
    result = F(0)
    for coefficient in reversed(coefficients):
        result = result * F(x) + F(coefficient)
    return result


def isolating_polynomial(entries, target):
    """Q_i(X) = product_(j != i) (X-lambda_j)."""
    sp = spectrum(entries)
    root = F(target)
    if root not in dict(sp):
        raise ValueError("target eigenvalue has zero aggregated multiplicity")
    coeffs = (F(1),)
    for eigenvalue, _ in sp:
        if eigenvalue != root:
            coeffs = polynomial_mul_linear(coeffs, eigenvalue)
    if polynomial_eval(coeffs, root) == 0:
        raise AssertionError("distinctness invariant broken")
    return coeffs


def isolator_identity(entries, target, n):
    """Return both sides of sum_r c_r t_(n+r) = m_i lambda_i^n Q_i(lambda_i)."""
    if n < 1:
        raise ValueError("positive trace powers only")
    sp = spectrum(entries)
    root = F(target)
    q = isolating_polynomial(sp, root)
    left = sum((c * power_trace(sp, n + r)
                for r, c in enumerate(q)), F(0))
    right = dict(sp)[root] * root ** n * polynomial_eval(q, root)
    return left, right


def isolation_certificate(entries, target, powers=(1, 2, 5, 11)):
    sp = spectrum(entries)
    root = F(target)
    coeffs = isolating_polynomial(sp, root)
    scale = dict(sp)[root] * polynomial_eval(coeffs, root)
    if scale == 0:
        raise AssertionError("spectral pole was not isolated")
    for n in powers:
        left, right = isolator_identity(sp, root, n)
        if left != right or right != scale * root**n:
            raise AssertionError("isolation identity failed")
    return {"eigenvalue": str(root), "nonzero_scale": str(scale),
            "polynomial": [str(c) for c in coeffs],
            "powers_checked": list(powers)}


def scalar_geometric_counterexample(a, b, K):
    """For a>b>0, exhibit n with a^n > K*b^n, all rational arithmetic."""
    a, b, K = F(a), F(b), F(K)
    if not 0 < b < a:
        raise ValueError("require 0 < b < a")
    if K < 0:
        return 0
    n = 0
    ratio = a/b
    value = F(1)
    while value <= K:
        n += 1
        value *= ratio
        if n > 10000:
            raise AssertionError("unexpected geometric witness search limit")
    if not a**n > K * b**n:
        raise AssertionError("incorrect geometric-growth witness")
    return n
