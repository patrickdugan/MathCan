#!/usr/bin/env python3
"""Independent generic chart and local-expansion checks with SymPy.

All chart identities are checked after clearing rational denominators over ZZ.
The local expansion checks apply in characteristic >3; their displayed rational
coefficients only invert 2 and 3. Global residue and divisor results remain
written geometric obligations, recorded in proof_review.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import time

import sympy as s

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE / 'audit_symbolic.json')
    args = ap.parse_args()
    checks = []
    started = time.monotonic()

    def check(label, difference, variables):
        numerator, denominator = s.fraction(s.cancel(difference))
        assert numerator == 0, (label, numerator, denominator)
        checks.append(label)

    r, t = s.symbols('r t')
    h = r*t-2*r+1
    j = r-t*t+t-1
    k = r*t*t-3*r*t+r+t*t
    b, c = r*t*(r-1), t*(r-1)
    x, y = {1: s.Integer(0), 2: b}, {1: s.Integer(0), 2: b*c}
    for i in range(2, 9):
        slope = s.cancel(y[i]/x[i])
        x[i+1] = s.cancel(slope*slope+(1-c)*slope+b-x[i])
        y[i+1] = s.cancel(b-(slope+1-c)*x[i+1])
    expected_x = {
        3: t*(r-1), 4: r*(r-1), 5: r*t*(t-1),
        6: t*(r-1)*(r-t)/(t-1)**2,
        7: r*t*(r-1)*(t-1)*h/(r-t)**2,
        8: r*(r-1)*(r-t)*j/h**2,
        9: t*(r-1)*h*k/j**2,
    }
    for i, value in expected_x.items():
        check(f'generic_x_{i}', x[i]-value, (r, t))
    for i in range(1, 10):
        equation = y[i]**2+(1-c)*x[i]*y[i]-b*y[i]-x[i]**3+b*x[i]**2
        check(f'point_{i}_on_generic_tate_cubic', equation, (r, t))

    polys = {
        7: r-t,
        11: r*r-r*t*(t*t-3*t+4)+t,
        13: (r-t)**3-r*(t-1)**3*h,
        17: r*(r-t)*j**3-t*h**3*k,
    }
    cofactors = {
        7: 1-r,
        11: -t/(t-1)**2,
        13: t*(r-1)/((r-t)**2*(t-1)**2),
        17: (r-1)/(h**2*j**2),
    }
    certificate = json.loads((HERE.parent/'trr05/certificate.json').read_text())
    for n, poly in polys.items():
        index = (n-1)//2
        check(f'order_{n}_generic_cofactor', x[index]-x[index+1]-poly*cofactors[n], (r, t))
        stored = sum(int(z)*r**i*t**q
                     for i, row in enumerate(certificate[str(n)]['f'])
                     for q, z in enumerate(row))
        check(f'order_{n}_matches_certificate_model', poly-stored, (r, t))
        assert s.Poly(poly, r).LC() == 1
        checks.append(f'order_{n}_monic_integral_model')

    # The expansion of Phi(x(Q+z)) has coefficients q1,q2,q3 below.
    z = s.symbols('z')
    X, Y, A = s.symbols('X Y A')
    F1, F2, F3 = s.symbols('F1 F2 F3', nonzero=True)
    xlocal = X+2*Y*z+(3*X*X+A)*z*z+4*X*Y*z**3
    phi_local = s.series(F1*(xlocal-X)+F2*(xlocal-X)**2/2+F3*(xlocal-X)**3/6, z, 0, 4).removeO()
    q1, q2, q3 = [s.expand(phi_local).coeff(z, d) for d in (1, 2, 3)]
    aa = -q2/q1
    bb = (q2/q1)**2-q3/q1
    inverse_local = (1+aa*z+bb*z*z)/(q1*z)
    product = s.series(inverse_local*phi_local, z, 0, 3).removeO()
    check('reciprocal_kernel_local_coefficients', product-1, (X, Y, A, F1, F2, F3, z))
    check('local_logarithmic_coefficient', 2*aa+(3*X*X+A)/Y+2*Y*F2/F1,
          (X, Y, A, F1, F2))
    a, bcoef = s.symbols('a bcoef')
    wlocal = (1+a*z+bcoef*z*z)/z
    second_log = s.series(s.diff(s.diff(wlocal,z)/wlocal,z), z, 0, 1).removeO()
    check('second_logarithmic_derivative_constant', second_log-1/z**2-(2*bcoef-a*a), (a,bcoef,z))
    # The residue at -Q of x(Q+Z)w(Z)omega comes from b/z.
    res = s.expand(z**-2*wlocal).coeff(z, -1)
    check('higher_order_pole_residue_coefficient', res-bcoef, (a,bcoef))

    receipt = {
        'schema': 'trr07-symbolic-audit-v1', 'status': 'passed',
        'sympy_version': s.__version__, 'checks': checks, 'check_count': len(checks),
        'elapsed_seconds': round(time.monotonic()-started,6),
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'chart_order_polynomials': {str(n):str(s.expand(f)) for n,f in polys.items()},
        'chart_open_factors': ['r','t','r-1','t-1','r-t','h','j'],
        'local_series_characteristics': '0 or p>3',
        'remaining_obligations': [
            'Geometric argument that every smooth marked point lies on the stated open chart.',
            'Global residue theorem and comparison of rational functions from principal parts.',
            'Genus-one principal-divisor criterion and kernel of a nonzero derivation over a perfect field.',
            'Riemann-Roch evaluation hyperplane and decoder factorization.',
        ],
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'passed','checks':len(checks),
                      'elapsed_seconds':receipt['elapsed_seconds'],'receipt':str(args.output)}))


if __name__ == '__main__':
    main()
