"""OLM-06: exhaustive one-swap alias classification on deleted K6 matchings.

Each omitted triple leaves 12 observed 3-hot matching rows. A one-swap
corruption changes one active feature to an inactive feature. The routine
finds every corruption which itself forms a valid anonymous K6 matching
codebook under another channel geometry, via the eleven-row star covers.
"""
from collections import Counter
from itertools import combinations,permutations
from latent_stars import matchings,star_covers


def relabel(p,m):
    return tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in m))


def enumerate_single_swap_aliases():
    edges=tuple(combinations(range(6),2))
    states=tuple(matchings(tuple(range(6))))
    masks=tuple(tuple(int(e in m) for e in edges) for m in states)
    relabels=tuple(permutations(range(6)))
    aliases=[]
    checked=0
    ambiguous_elevens=0
    for held in combinations(range(15),3):
        observed=[i for i in range(15) if i not in held]
        for removed in observed:
            partial=[masks[j] for j in observed if j!=removed]
            _,covers=star_covers(partial)
            checked+=1
            if len(covers)==2:ambiguous_elevens+=1
            for cov in covers:
                feature_edge={j:tuple(t for t,star in enumerate(cov) if j in star)
                              for j in range(15)}
                inv={edge:j for j,edge in feature_edge.items()}
                for matching in states:
                    active={inv[e] for e in matching}
                    candidate=tuple(int(j in active) for j in range(15))
                    if (candidate==masks[removed] or
                        sum(a!=b for a,b in zip(candidate,masks[removed]))!=2 or
                        candidate in partial):
                        continue
                    replacement=list(masks[i] for i in observed)
                    replacement[observed.index(removed)]=candidate
                    _,post_covers=star_covers(replacement)
                    if len(post_covers)!=1:
                        raise AssertionError('alias must have a unique valid new geometry')
                    new_cov=post_covers[0]
                    new_edges={j:tuple(t for t,star in enumerate(new_cov) if j in star)
                               for j in range(15)}
                    abstract=[]
                    for mask in replacement:
                        abstract.append(tuple(sorted(new_edges[j] for j,bit in enumerate(mask) if bit)))
                    # Can a common vertex relabel of the true training matching
                    # labels explain the one-swap alternate geometry?
                    gauge_compatible=any(all(relabel(p,states[i])==abstract[t]
                                        for t,i in enumerate(observed))
                                         for p in relabels)
                    aliases.append({'heldout':list(held),'corrupted_train_class':removed,
                          'swap_out':next(i for i,(a,b) in enumerate(zip(masks[removed],candidate)) if a and not b),
                          'swap_in':next(i for i,(a,b) in enumerate(zip(masks[removed],candidate)) if not a and b),
                          'eleven_cover_count':len(covers),
                          'common_vertex_gauge_possible':gauge_compatible})
    assert checked==455*12
    assert ambiguous_elevens==180
    assert len(aliases)==180
    per_hold=Counter(tuple(a['heldout']) for a in aliases)
    assert len(per_hold)==180
    assert all(v==1 for v in per_hold.values())
    assert all(a['eleven_cover_count']==2 for a in aliases)
    return {'three_state_holdouts':455,
            'remaining_eleven_subcohorts':checked,
            'ambiguous_eleven_subcohorts':ambiguous_elevens,
            'one_swap_alias_events':len(aliases),
            'distinct_three_state_holdouts_with_one_alias':len(per_hold),
            'heldouts_with_no_alias':455-len(per_hold),
            'gauge_compatible_aliases':sum(a['common_vertex_gauge_possible'] for a in aliases),
            'gauge_incompatible_aliases':sum(not a['common_vertex_gauge_possible'] for a in aliases),
            'aliases':aliases}


if __name__=='__main__':
    import json
    print(json.dumps(enumerate_single_swap_aliases(),indent=2))
