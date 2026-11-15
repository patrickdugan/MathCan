"""OLM-06: exact deterministic top-k and matching-margin certificates.

Numerical floating SAE scores can be converted to exact decimal fractions
for post-hoc margin bookkeeping. The mathematical inequalities are valid
for arbitrary real scores; this oracle checks finite rational instances.
"""
from fractions import Fraction
from itertools import combinations


def topk_stability(scores,k=3):
    if not scores or not 0<k<len(scores[0]):
        raise ValueError('nonempty score matrix and 0<k<width required')
    gaps=[]
    for row in scores:
        if len(row)!=len(scores[0]):
            raise ValueError('ragged score matrix')
        ranked=sorted((Fraction(str(v)) for v in row),reverse=True)
        gaps.append(ranked[k-1]-ranked[k])
    gap=min(gaps)
    return {'topk_global_gap':gap,'certified_linf_radius':gap/2,
            'strictly_separated':gap>0,'row_gaps':tuple(gaps)}


def matching_stability(scores,matched_sets):
    """For k-hot candidate sets, L_inf radius gap/(2*k) preserves top-1."""
    a=tuple(Fraction(str(v)) for v in scores)
    sets=tuple(tuple(sorted(s)) for s in matched_sets)
    if not sets or len(set(sets))!=len(sets):
        raise ValueError('nonempty distinct codeword supports required')
    k=len(sets[0])
    if not all(len(s)==k and len(set(s))==k and all(0<=j<len(a) for j in s) for s in sets):
        raise ValueError('invalid candidate supports')
    ranked=sorted(((sum((a[j] for j in s),Fraction(0)),s) for s in sets),reverse=True)
    if len(ranked)<2:
        raise ValueError('need two candidate states')
    gap=ranked[0][0]-ranked[1][0]
    return {'winning_support':ranked[0][1],'score_gap':gap,
            'certified_linf_radius':gap/Fraction(2*k),
            'strictly_separated':gap>0}


def silent_atom_witness(rows,atom):
    """Shows a column remains observationally free for every training row."""
    rows=tuple(tuple(Fraction(v) for v in row) for row in rows)
    if not rows or not (0<=atom<len(rows[0])):
        raise ValueError('invalid silent coordinate')
    if any(len(r)!=len(rows[0]) for r in rows):
        raise ValueError('ragged latent rows')
    if any(r[atom] for r in rows):
        raise ValueError('atom activates in training; not silent')
    d1=[Fraction(i+1,7) for i in range(len(rows[0]))]
    d2=d1[:]
    d2[atom]+=Fraction(19,11)
    y1=tuple(sum((z*w for z,w in zip(row,d1)),Fraction(0)) for row in rows)
    y2=tuple(sum((z*w for z,w in zip(row,d2)),Fraction(0)) for row in rows)
    assert y1==y2 and d1!=d2
    return {'silent_atom':atom,'distinct_parameter_vectors':True,
            'identical_training_observations':True,'n_rows':len(rows)}


def margin_from_archive(scores,k=3):
    c=topk_stability(scores[:12],k)
    return {'global_gap':str(c['topk_global_gap']),
            'strict_noise_radius':str(c['certified_linf_radius']),
            'positive':c['strictly_separated']}

if __name__=='__main__':
    import json
    from pathlib import Path
    import sys
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('sae_activation_evidence.json')
    if not path.exists():
        raise SystemExit('Pass the SMC-06 frozen score JSON path as an argument')
    doc=json.load(open(path))
    print(json.dumps({seed:margin_from_archive(score)
          for seed,score in doc['activation_scores_15_by_15'].items()},indent=2))
