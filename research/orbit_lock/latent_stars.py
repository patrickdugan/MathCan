"""OLM-05: exact finite rigidity, covariance and repetition probabilities.

Standard library only. Exhaustively certifies all C(15,3)=455 and
C(15,4)=1365 missing-perfect-matching cohorts on six vertices.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb


def matchings(vertices):
    vs = tuple(vertices)
    if not vs:
        yield ()
        return
    a = vs[0]
    for j in range(1, len(vs)):
        for sub in matchings(vs[1:j] + vs[j + 1:]):
            yield tuple(sorted(((a, vs[j]),) + sub))


def star_candidates(rows, feature_count=15, star_size=5):
    rows = tuple(tuple(row) for row in rows)
    seen = set()
    for row in rows:
        seen.update(combinations((i for i,x in enumerate(row) if x), 2))
    return tuple(c for c in combinations(range(feature_count), star_size)
                 if all(pair not in seen for pair in combinations(c, 2)))


def star_covers(rows, feature_count=15, star_size=5,
                n_vertices=6, max_solutions=2):
    """Backtrack every six-star cover, stopping at two for ambiguity detection."""
    candidates = tuple(frozenset(c) for c in star_candidates(rows,feature_count,star_size))
    solutions = []
    def rec(start,chosen,counts):
        if len(solutions) >= max_solutions:
            return
        if len(chosen) == n_vertices:
            if all(count == 2 for count in counts):
                solutions.append(tuple(chosen))
            return
        for j in range(start,len(candidates)):
            cand = candidates[j]
            if any(len(cand & other) != 1 for other in chosen):
                continue
            if any(counts[i] == 2 for i in cand):
                continue
            nxt = list(counts)
            for i in cand:
                nxt[i] += 1
            rec(j + 1, chosen + [cand], nxt)
    rec(0, [], [0] * feature_count)
    return candidates, tuple(solutions)


def enumerate_partial_rigidity():
    edges = tuple(combinations(range(6),2))
    states = tuple(matchings(range(6)))
    assert len(edges) == len(states) == 15
    incidence = tuple(tuple(int(e in m) for e in edges) for m in states)
    counts = Counter()
    examples = {}
    for held in combinations(range(15),3):
        rows = [incidence[j] for j in range(15) if j not in held]
        cliques = star_candidates(rows)
        signature = tuple(sorted(len(set(states[a]) & set(states[b]))
                                 for a,b in combinations(held,2)))
        key = (signature,len(cliques))
        counts[key] += 1
        examples.setdefault(key,held)
        candidates,covers = star_covers(rows)
        assert len(candidates) == len(cliques)
        assert len(covers) == 1
        assert all(sum(j in c for c in covers[0]) == 2 for j in range(15))
        assert all(len(a & b) == 1 for a,b in combinations(covers[0],2))
    expected = {((0,0,0),6):80,((0,0,1),13):180,
                ((0,1,1),24):180,((1,1,1),47):15}
    assert dict(counts) == expected
    assert sum(counts.values()) == comb(15,3)
    return {'n_features':15,'n_matching_states':15,'heldout_count':3,
            'all_holdout_subsets':comb(15,3),
            'classes':[{'pairwise_shared_edges':list(k[0]),
                        'star_candidate_cliques':k[1],
                        'count':v,'example_heldout':list(examples[k])}
                       for k,v in sorted(counts.items())],
            'direct_six_clique_cases':80,
            'extra_clique_cases_resolved_by_global_cover':375,
            'unique_global_star_covers':455}


def enumerate_four_missing_boundary():
    """Enumerate all 1365 four-holdout masks, distinguish one versus two covers."""
    edges = tuple(combinations(range(6),2))
    states = tuple(matchings(range(6)))
    masks = tuple(tuple(int(e in g) for e in edges) for g in states)
    counts = Counter()
    for held in combinations(range(15),4):
        rows = [masks[j] for j in range(15) if j not in held]
        _,covers = star_covers(rows)
        shared = [(i,j) for i,j in combinations(range(4),2)
                  if set(states[held[i]]) & set(states[held[j]])]
        shared_degrees = Counter(v for pair in shared for v in pair)
        special = len(shared) == 2 and len(shared_degrees) == 4
        count = len(covers)
        if count not in (1,2):
            raise AssertionError('unexpected cover multiplicity')
        if (count == 2) != special:
            raise AssertionError('two disjoint shared-edge pairs characterize ambiguity')
        counts[(count,'disjoint-two-shares' if special else 'other')] += 1
    assert counts[(1,'other')] == 1320
    assert counts[(2,'disjoint-two-shares')] == 45
    return {'eleven_state_subsets':comb(15,4),
            'unique_reconstructions':1320,
            'exactly_two_reconstructions':45,
            'ambiguous_iff_two_disjoint_pairs_of_omitted_matchings_share_an_edge':True}


def covariance_types(k,p=Fraction(1),q=Fraction(0)):
    if k < 2 or not (Fraction(0) <= q < p <= Fraction(1)):
        raise ValueError('requires k>=2 and 0<=q<p<=1')
    n = 2*k
    edge_p = Fraction(1,n-1)
    disjoint_joint = Fraction(1,(n-1)*(n-3))
    gain = (p-q)**2
    return {'k':k,'marginal_true_probability':edge_p,
            'covariance_incident':-gain*edge_p**2,
            'covariance_disjoint':gain*(disjoint_joint-edge_p**2),
            'smallest_covariance_magnitude':gain*min(edge_p**2,disjoint_joint-edge_p**2)}


def repeated_mask_probability(repeats,p=Fraction(9,10),q=Fraction(1,10),
                              active=36,inactive=144):
    """Binomial majority recovery for independently corrupted feature episodes."""
    if (not isinstance(repeats,int) or repeats < 1
            or not Fraction(0) <= q < Fraction(1,2) < p <= Fraction(1)):
        raise ValueError('valid R and p>1/2>q required')
    if min(active,inactive) < 0:
        raise ValueError('invalid bit counts')
    fn = sum((comb(repeats,j)*p**j*(1-p)**(repeats-j)
              for j in range(repeats//2+1)),Fraction(0))
    fp = sum((comb(repeats,j)*q**j*(1-q)**(repeats-j)
              for j in range(repeats//2+1,repeats+1)),Fraction(0))
    exact = (1-fn)**active*(1-fp)**inactive
    union_bound = min(Fraction(1),active*fn+inactive*fp)
    assert 1-exact <= union_bound
    return {'R':repeats,'p':str(p),'q':str(q),
            'fn':str(fn),'fp':str(fp),
            'exact_probability_all_bits_correct_float':float(exact),
            'union_error_upper':str(union_bound),
            'exact_success_float':float(exact),
            'union_error_float':float(union_bound)}


if __name__ == '__main__':
    import json
    print(json.dumps({'rigidity':enumerate_partial_rigidity(),
      'four_omitted':enumerate_four_missing_boundary(),
      'covariances':[{'k':k,**{name:str(v) for name,v in
             covariance_types(k,Fraction(3,4),Fraction(1,4)).items()}}
             for k in (2,3,4)],
      'repetition':[repeated_mask_probability(16),
          repeated_mask_probability(40,Fraction(3,4),Fraction(1,4)),
          repeated_mask_probability(64,Fraction(3,4),Fraction(1,4))]},indent=2))
