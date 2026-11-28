"""Exact finite orbit-lock certificate; standard library only."""
from fractions import Fraction
from itertools import permutations
from math import log


def matchings(vertices):
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    head = vertices[0]
    for i in range(1, len(vertices)):
        edge = (head, vertices[i])
        tail = vertices[1:i] + vertices[i + 1:]
        for sub in matchings(tail):
            yield tuple(sorted((edge,) + sub))


def action(permutation, matching):
    return tuple(sorted(tuple(sorted((permutation[a], permutation[b]))) for a, b in matching))


def total_variation(p, q):
    return sum((abs(p.get(k, Fraction(0)) - q.get(k, Fraction(0))) for k in p.keys() | q.keys()), Fraction(0)) / 2


def orbit_certificate(n, noise=Fraction(0)):
    """Compute the entire joint law for small even n; exponential complexity."""
    if n < 2 or n % 2 or not (0 <= noise <= 1):
        raise ValueError("even n>=2 and 0<=noise<=1 required")
    states = tuple(matchings(range(n)))
    group = tuple(permutations(range(n)))
    origin = states[0]
    m, h = len(states), len(group)
    assert h % m == 0
    joint = {}
    independent = {}
    for g in states:
        for perm in group:
            base = Fraction(1, m * h)
            locked = Fraction(1, h) if g == action(perm, origin) else Fraction(0)
            independent[g, perm] = base
            joint[g, perm] = (1 - noise) * locked + noise * base
    marginal_g = {g: sum((joint[g, perm] for perm in group), Fraction(0)) for g in states}
    marginal_p = {perm: sum((joint[g, perm] for g in states), Fraction(0)) for perm in group}
    u_g = {g: Fraction(1, m) for g in states}
    u_p = {perm: Fraction(1, h) for perm in group}
    tv = total_variation(joint, independent)
    theoretical = (1 - noise) * Fraction(m - 1, m)
    assert tv == theoretical
    assert total_variation(marginal_g, u_g) == 0
    assert total_variation(marginal_p, u_p) == 0
    event = sum((v for (g, perm), v in joint.items() if g == action(perm, origin)), Fraction(0))
    assert event == 1 - noise + noise / m
    a = float(1 - noise + noise / m)
    b = float(noise / m)
    mutual_information_nats = log(m) + (a * log(a) if a else 0.0) + (m - 1) * (b * log(b) if b else 0.0)
    return {"vertices": n, "matching_count": m, "permutations": h, "noise": str(noise),
            "tv": str(tv), "optimal_event_probability": str(event),
            "independent_event_probability": str(Fraction(1, m)),
            "mutual_information_nats": mutual_information_nats,
            "marginal_tv": "0"}


if __name__ == "__main__":
    import json
    print(json.dumps([orbit_certificate(n, e) for n in (4, 6) for e in (Fraction(0), Fraction(1, 4), Fraction(1))], indent=2))
