"""OLM-02: exact entropy/collision/whitened-spectrum certificates.

For an arbitrary finite distribution q on seeds S and deterministic map
f:S->X, form J_eps=(1-eps) Law(f(S),S)+eps(P_X x q).

The rational Gram identity verified here gives the complete CCA spectrum
without floating-point linear algebra or computing matrix square roots.
"""
from fractions import Fraction
from itertools import permutations

ONE = Fraction(1)
ZERO = Fraction(0)


def tv(p, q):
    return sum((abs(p.get(k, ZERO) - q.get(k, ZERO)) for k in p.keys() | q.keys()), ZERO) / 2


def exact_certificate(seed_probs, seed_to_observation, noise=Fraction(0)):
    """Exact joint law, TV/collision identity and weighted Gram spectral audit.

    seed_probs and mapping must have identical keys. All seed masses >0.
    The observed state support is the image of the mapping.
    Quadratic complexity in number of observations, linear in seed count.
    """
    if set(seed_probs) != set(seed_to_observation):
        raise ValueError('seed support and mapping keys must agree')
    if not seed_probs or any(x <= 0 for x in seed_probs.values()) or sum(seed_probs.values(), ZERO) != ONE:
        raise ValueError('seed masses must be positive and sum to one')
    if not (0 <= noise <= 1):
        raise ValueError('noise must be a probability')
    observations = sorted(set(seed_to_observation.values()))
    masses = {x: sum((q for s, q in seed_probs.items() if seed_to_observation[s] == x), ZERO)
              for x in observations}
    independent = {(x, s): mass * q for x, mass in masses.items() for s, q in seed_probs.items()}
    dependent = {(x, s): (1 - noise) * (q if seed_to_observation[s] == x else ZERO)
                 + noise * independent[x, s]
                 for x in observations for s, q in seed_probs.items()}
    collision = sum((x * x for x in masses.values()), ZERO)
    event = sum((mass for (x,s), mass in dependent.items() if seed_to_observation[s] == x), ZERO)
    expected_tv = (ONE - noise) * (ONE - collision)
    assert tv(dependent, independent) == expected_tv
    assert event == ONE - noise + noise * collision
    # Weighted Gram J diag(q)^-1 J^T has normalized singular values
    # 1 and (1-noise) repeated m-1 times, without computing square roots.
    r = ONE - (ONE - noise)**2
    for x in observations:
        for y in observations:
            actual = sum((dependent[x,s] * dependent[y,s] / q
                          for s, q in seed_probs.items()), ZERO)
            predicted = ((ONE-noise)**2 * masses[x] if x == y else ZERO) + r * masses[x]*masses[y]
            assert actual == predicted
    return {'n_seeds':len(seed_probs), 'n_observations':len(observations),
            'noise':str(noise), 'collision':str(collision),
            'tv':str(expected_tv), 'compatibility_event_probability':str(event),
            'null_compatibility_probability':str(collision),
            'centered_cca_singular_value':str(ONE - noise),
            'centered_cca_multiplicity':len(observations)-1,
            'weighted_gram_verified':True}


def perfect_matchings(vertices):
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for j in range(1,len(vertices)):
        b = vertices[j]
        for tail in perfect_matchings(vertices[1:j] + vertices[j+1:]):
            yield tuple(sorted(((a,b),)+tail))


def orbit_spectrum(k, noise=Fraction(0)):
    """Verify the pure relation for all permutations of 2k vertices, k=2 or 3."""
    if k not in (2,3):
        raise ValueError('enumeration limited to k=2 or 3')
    base = next(perfect_matchings(tuple(range(2*k))))
    group = tuple(permutations(range(2*k)))
    q = {p: Fraction(1,len(group)) for p in group}
    f = {p: tuple(sorted(tuple(sorted((p[a], p[b]))) for a,b in base)) for p in group}
    result = exact_certificate(q,f,noise)
    m = result['n_observations']
    assert m == {2:3,3:15}[k]
    assert Fraction(result['collision']) == Fraction(1,m)
    assert Fraction(result['tv']) == (1-noise) * Fraction(m-1,m)
    return result


if __name__ == '__main__':
    import json
    print(json.dumps([orbit_spectrum(k, eps) for k in (2,3)
                      for eps in (Fraction(0),Fraction(1,4),Fraction(1))],indent=2))
