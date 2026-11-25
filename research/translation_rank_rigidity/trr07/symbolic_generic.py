#!/usr/bin/env python3
"""Exact generic Tate recurrence and marked-order factors, using python-flint.

This module performs no finite-field search. Polynomial coefficients are exact
rationals; every recurrence fraction is reduced by a multivariate gcd.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
import flint

CTX = flint.fmpq_mpoly_ctx.get(["r", "t"], "lex")
R, T = CTX.gens()
NORMALIZATIONS = 0


class Fraction:
    def __init__(self, numerator=0, denominator=1):
        global NORMALIZATIONS
        if isinstance(numerator, Fraction):
            self.num, self.den = numerator.num, numerator.den
            return
        self.num = CTX.constant(numerator) if isinstance(numerator, int) else numerator
        self.den = CTX.constant(denominator) if isinstance(denominator, int) else denominator
        if not self.den:
            raise ZeroDivisionError
        assert all(co.denominator == 1 for co in self.num.coeffs())
        assert all(co.denominator == 1 for co in self.den.coeffs())
        raw_num, raw_den = self.num, self.den
        common = self.num.gcd(self.den)
        assert all(co.denominator == 1 for co in common.coeffs())
        self.num //= common
        self.den //= common
        assert self.num * common == raw_num
        assert self.den * common == raw_den
        assert all(co.denominator == 1 for co in self.num.coeffs())
        assert all(co.denominator == 1 for co in self.den.coeffs())
        lead = self.den.leading_coefficient()
        assert lead in (1, -1), "normalization introduced an exceptional integer denominator"
        self.num /= lead
        self.den /= lead
        NORMALIZATIONS += 1

    def __add__(self, other):
        other = Fraction(other)
        return Fraction(self.num * other.den + other.num * self.den, self.den * other.den)

    __radd__ = __add__

    def __neg__(self):
        return Fraction(-self.num, self.den)

    def __sub__(self, other):
        return self + -Fraction(other)

    def __rsub__(self, other):
        return Fraction(other) + -self

    def __mul__(self, other):
        other = Fraction(other)
        return Fraction(self.num * other.num, self.den * other.den)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Fraction(other)
        return Fraction(self.num * other.den, self.den * other.num)

    def __pow__(self, exponent):
        assert exponent >= 0
        return Fraction(self.num ** exponent, self.den ** exponent)


def polynomial_json(poly):
    return [[[int(e) for e in exponents], str(coefficient)] for exponents, coefficient in poly.to_dict().items()]


def coordinates(n):
    b, c = Fraction(R * T * (R - 1)), Fraction(T * (R - 1))
    xs, ys = [Fraction(0), Fraction(0), b], [Fraction(0), Fraction(0), b * c]
    for i in range(2, n):
        slope = ys[i] / xs[i]
        xs.append(slope ** 2 + (1 - c) * slope + b - xs[i])
        ys.append(b - (slope + 1 - c) * xs[-1])
    return xs, ys


def derive(order):
    global NORMALIZATIONS
    NORMALIZATIONS = 0
    start = time.monotonic()
    half = (order - 1) // 2
    xs, ys = coordinates(half + 1)
    relation = xs[half] - xs[half + 1]
    unit, factors = relation.num.factor()
    # At a smooth point of exact prime order >=7, r, r-1 and t are
    # nonzero. Remaining factors are reported without assuming coverage.
    removed, candidates = [], []
    for factor, multiplicity in factors:
        record = {"polynomial": str(factor), "coefficients": polynomial_json(factor),
                  "multiplicity": int(multiplicity), "degrees": [int(d) for d in factor.degrees()]}
        if factor in (R, R - 1, T, T - 1):
            removed.append(record)
        else:
            candidates.append(record)
    check = CTX.constant(unit)
    for factor, multiplicity in factors:
        check *= factor ** multiplicity
    assert check == relation.num
    return {"schema": "trr07-generic-order-v1", "order": order,
            "elapsed_seconds": time.monotonic() - start,
            "factorization_verified": True, "unit": str(unit),
            "integral_normalizations_verified": NORMALIZATIONS,
            "order_numerator": polynomial_json(relation.num),
            "order_denominator": polynomial_json(relation.den),
            "removed_obvious_units": removed, "candidate_factors": candidates,
            "recurrence_denominators": [polynomial_json(x.den) for x in xs[2:]],
            "status": "generic_chart_factorization_only"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--order", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = derive(args.order)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("order", "elapsed_seconds", "status")}))
    print([(f["degrees"], f["polynomial"]) for f in result["candidate_factors"]])
