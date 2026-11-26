#!/usr/bin/env python3
"""Exact finite-field circuit controls for the TRR polynomial-degree model.

The circuit is a single division-free straight-line program in x1,y1,x2,y2,u.
Its branches are polynomial zero indicators. The independent reference uses
the ordinary secant/tangent group law. Every enumerated point is synthetic.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


class Circuit:
    def __init__(self, q):
        self.q = q
        self.nodes = []
        self.degree_bounds = []
        self.depths = []
        self.power_calls = []
        self.constants = {}

    def add_node(self, node, degree, depth):
        i = len(self.nodes)
        self.nodes.append(node)
        self.degree_bounds.append(degree)
        self.depths.append(depth)
        return i

    def input(self, name, degree):
        return self.add_node(["input", name], degree, 0)

    def constant(self, value):
        value %= self.q
        if value not in self.constants:
            self.constants[value] = self.add_node(["constant", value], (0, 0), 0)
        return self.constants[value]

    def operation(self, op, a, b):
        da, db = self.degree_bounds[a], self.degree_bounds[b]
        depth = max(self.depths[a], self.depths[b])
        if op == "mul":
            degree = tuple(x + y for x, y in zip(da, db))
            depth += 1
        else:
            degree = tuple(max(x, y) for x, y in zip(da, db))
        return self.add_node([op, a, b], degree, depth)

    def add(self, a, b):
        return self.operation("add", a, b)

    def sub(self, a, b):
        return self.operation("sub", a, b)

    def mul(self, a, b):
        return self.operation("mul", a, b)

    def power(self, a, exponent):
        assert exponent >= 1
        before = len(self.nodes)
        value = a
        for bit in bin(exponent)[3:]:
            value = self.mul(value, value)
            if bit == "1":
                value = self.mul(value, a)
        count = len(self.nodes) - before
        assert count == exponent.bit_length() + exponent.bit_count() - 2
        self.power_calls.append({"exponent": str(exponent), "multiplications": count})
        return value

    def receipt(self, output):
        counts = Counter(n[0] for n in self.nodes)
        digest = hashlib.sha256(json.dumps(self.nodes, separators=(",", ":")).encode()).hexdigest()
        return {
            "nodes": len(self.nodes),
            "operations": dict(sorted(counts.items())),
            "multiplicative_depth": self.depths[output],
            "formal_block_degree_upper_bounds": list(self.degree_bounds[output]),
            "degree_bound_semantics": "Syntactic gate-level upper bounds; cancellation and reduction modulo the curve or field equations are not performed.",
            "power_calls": self.power_calls,
            "circuit_sha256": digest,
            "output_node": output,
        }


def build_circuit(q, curve_a, wrong_identity_selector=False):
    c = Circuit(q)
    x1, y1 = c.input("x1", (1, 0)), c.input("y1", (1, 0))
    x2, y2 = c.input("x2", (0, 1)), c.input("y2", (0, 1))
    u = c.input("u", (0, 0))  # A coefficient parameter for block degree.
    one, two, three = c.constant(1), c.constant(2), c.constant(3)
    A = c.constant(curve_a)
    a, b = c.sub(x2, x1), c.sub(y2, y1)
    ia = c.power(a, q - 2)
    nonzero_b = c.power(b, q - 1)
    iy = c.power(c.mul(two, y1), q - 2)
    za = c.sub(one, c.mul(a, ia))
    zb = c.sub(one, nonzero_b)
    slope = c.mul(b, ia)
    x_secant = c.sub(c.sub(c.mul(slope, slope), x1), x2)
    tangent_numerator = c.add(c.mul(three, c.mul(x1, x1)), A)
    tangent_slope = c.mul(tangent_numerator, iy)
    x_tangent = c.sub(c.mul(tangent_slope, tangent_slope), c.mul(two, x1))
    secant_term = c.mul(c.sub(one, za), x_secant)
    tangent_term = c.mul(c.mul(za, zb), x_tangent)
    inverse_selector = zb if wrong_identity_selector else c.sub(one, zb)
    inverse_term = c.mul(c.mul(za, inverse_selector), u)
    output = c.add(c.add(secant_term, tangent_term), inverse_term)
    return c, output


def replay(nodes, output, q, inputs):
    """Interpreter of the frozen gate trace; it performs no curve operations."""
    values = []
    for node in nodes:
        op = node[0]
        if op == "input":
            value = inputs[node[1]]
        elif op == "constant":
            value = node[1]
        elif op == "add":
            value = values[node[1]] + values[node[2]]
        elif op == "sub":
            value = values[node[1]] - values[node[2]]
        elif op == "mul":
            value = values[node[1]] * values[node[2]]
        else:
            raise ValueError(op)
        values.append(value % q)
    return values[output]


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n**0.5) + 1))


def group_add(P, Q, p, A):
    """Independent piecewise rational evaluator, with Python's modular inverse."""
    if P is None:
        return Q
    if Q is None:
        return P
    x, y = P
    X, Y = Q
    if x == X and (y + Y) % p == 0:
        return None
    if P == Q:
        slope = (3 * x * x + A) * pow(2 * y, -1, p) % p
    else:
        slope = (Y - y) * pow(X - x, -1, p) % p
    z = (slope * slope - x - X) % p
    return z, (slope * (x - z) - y) % p


def find_fixture(p):
    """First lexicographic smooth short model with prime order >=19, !=p."""
    for A in range(p):
        for B in range(p):
            if (4 * A**3 + 27 * B**2) % p == 0:
                continue
            points = [(x, y) for x in range(p) for y in range(p)
                      if (y*y - x*x*x - A*x - B) % p == 0]
            N = len(points) + 1
            if N < 19 or N == p or not is_prime(N):
                continue
            T = points[0]
            subgroup = [None]
            current = T
            while current is not None:
                assert current not in subgroup
                subgroup.append(current)
                current = group_add(current, T, p, A)
            assert len(subgroup) == N and set(subgroup[1:]) == set(points)
            return A, B, T, subgroup
    raise RuntimeError(f"No fixture over F_{p}")


def check_fixture(p):
    A, B, T, subgroup = find_fixture(p)
    c, output = build_circuit(p, A)
    mutant, mutant_output = build_circuit(p, A, wrong_identity_selector=True)
    N = len(subgroup)
    expected_bounds = (4*p - 2, 3*p - 3)
    assert c.degree_bounds[output] == expected_bounds
    pair_kinds = Counter()
    mutation_failures = Counter()
    evaluations = 0
    for P in subgroup[1:]:
        for Q in subgroup[1:]:
            R = group_add(P, Q, p, A)
            kind = "secant" if P[0] != Q[0] else "tangent" if P == Q else "inverse"
            pair_kinds[kind] += 1
            if kind == "inverse":
                assert R is None
            else:
                assert R is not None
            for u in range(p):
                inputs = dict(x1=P[0], y1=P[1], x2=Q[0], y2=Q[1], u=u)
                expected = u if R is None else R[0]
                assert replay(c.nodes, output, p, inputs) == expected
                evaluations += 1
            inputs["u"] = 1
            expected = 1 if R is None else R[0]
            if replay(mutant.nodes, mutant_output, p, inputs) != expected:
                mutation_failures[kind] += 1
    assert pair_kinds["inverse"] == N - 1
    assert pair_kinds["tangent"] == N - 1
    assert pair_kinds["secant"] == (N - 1) * (N - 3)
    assert mutation_failures == {"inverse": N - 1, "tangent": N - 1}
    circuit_receipt = c.receipt(output)
    expected_mults = sum(v["multiplications"] for v in c.power_calls) + 14
    assert circuit_receipt["operations"]["mul"] == expected_mults
    assert circuit_receipt["operations"]["add"] + circuit_receipt["operations"]["sub"] == 12
    return {
        "p": p, "A": A, "B": B, "T": list(T), "N": N,
        "discriminant": (-16 * (4*A**3 + 27*B**2)) % p,
        "point_enumeration": "All affine points plus O; subgroup verified equal to the full prime-order point group.",
        "minimum_decoder_degree_from_TRR11": (N + 2) // 3,
        "assigned_values_checked": list(range(p)),
        "input_pairs": (N - 1)**2,
        "pair_kinds": dict(sorted(pair_kinds.items())),
        "coefficient_evaluations": evaluations,
        "wrong_identity_selector_failures_at_u_1": dict(sorted(mutation_failures.items())),
        "circuit": circuit_receipt,
        "gate_trace": c.nodes,
    }


def secp256k1_cost_only():
    p = 2**256 - 2**32 - 977
    n = int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16)
    c, output = build_circuit(p, 0)
    d = (n + 2) // 3
    result = c.receipt(output)
    result["formal_block_degree_upper_bounds"] = [
        str(v) for v in result["formal_block_degree_upper_bounds"]
    ]
    assert result["operations"]["mul"] == 1523
    assert result["operations"]["add"] + result["operations"]["sub"] == 12
    result.update({
        "p": str(p), "n": str(n), "A": 0, "B": 7,
        "parameter_source": "https://www.secg.org/sec2-v2.pdf",
        "scope": "Cost and degree bookkeeping from public parameters only. This check does not prove parameter primality, recover a scalar, or run a key attack.",
        "minimum_degree_if_TRR11_hypotheses_hold": str(d),
        "multiplicative_depth_lower_bound_from_degree": (d - 1).bit_length(),
        "cost_model": "Binary field multiplication gates, including multiplication by constants; addition and subtraction each cost one separate field gate. Bit costs and coordinate conversion are excluded.",
    })
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("circuit_scope_receipt.json"))
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run without -O: exact controls require assertions.")
    cases = [check_fixture(p) for p in (17, 19, 23, 29, 31, 37)]
    receipt = {
        "schema": "trr12-circuit-scope-v1", "status": "passed",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "formula": "D=(1-Za)*Xsec+Za*Zb*Xdbl+Za*(1-Zb)*u; a=x2-x1; b=y2-y1; Za=1-a*a^(q-2); Zb=1-b^(q-1); Xsec=(b*a^(q-2))^2-x1-x2; Xdbl=((3*x1^2+A)*(2*y1)^(q-2))^2-2*x1",
        "theoretical_scope": "Any finite field F_q of characteristic >3, smooth short Weierstrass equation, and nonidentity inputs in an odd-order subgroup. Odd order ensures y1 != 0. Fermat zero indicators cover secants, tangents and inverse pairs.",
        "degree_tracking": "The syntactic formal block-degree upper bounds are (4q-2,3q-3); they are upper bounds before cancellation. TRR11 gives a separate minimum degree among all representatives under its hypotheses.",
        "gate_bound": "Two powers q-2 and one power q-1, plus 14 multiplications and 12 additions/subtractions. Binary powering uses bit_length(e)+popcount(e)-2 multiplication gates for e>=1, proving O(log q) total gates.",
        "fixtures": cases,
        "totals": {
            "fixtures": len(cases),
            "input_pairs": sum(c["input_pairs"] for c in cases),
            "coefficient_evaluations": sum(c["coefficient_evaluations"] for c in cases),
            "inverse_pairs": sum(c["pair_kinds"]["inverse"] for c in cases),
            "tangent_pairs": sum(c["pair_kinds"]["tangent"] for c in cases),
            "wrong_identity_selector_failures": sum(sum(c["wrong_identity_selector_failures_at_u_1"].values()) for c in cases),
        },
        "secp256k1_cost_only": secp256k1_cost_only(),
        "remaining_proof_obligations": [
            "The universal finite-field circuit identity and its arithmetic complexity are proved in the accompanying mathematics, with exact small-field controls here; the new circuit construction is not yet formalized in Lean.",
            "TRR11 certifies the minimum polynomial degree under its own field and subgroup hypotheses. The circuit controls establish no DLP or ECDSA attack lower bound.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "totals": receipt["totals"],
                      "secp256k1_multiplications": receipt["secp256k1_cost_only"]["operations"]["mul"],
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
