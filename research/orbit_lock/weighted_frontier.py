"""OLM-03G: exact weighted two-code frontier for finite-time Markov laws."""
from fractions import Fraction

ZERO=Fraction(0)
ONE=Fraction(1)

def two_code_optimal(weights):
    """Closest-to-half exact subset sum; <=20 states to bound work."""
    weights=tuple(weights)
    if not weights or len(weights)>20 or any(p<0 for p in weights) or sum(weights,ZERO)!=ONE:
        raise ValueError('weights must be a probability law with <=20 coordinates')
    states={ZERO:0}
    for i,p in enumerate(weights):
        states.update({s+p:mask|(1<<i) for s,mask in tuple(states.items())})
    q,mask=min(states.items(),key=lambda sm:(abs(sm[0]-Fraction(1,2)),sm[0]))
    return {'tv':ONE-q*q-(ONE-q)*(ONE-q),'bin_mass':q,'bin_mask':mask,
            'n_subset_sums':len(states)}

def three_matching_onebit(t):
    """Closed-form four-vertex lazy matching-switch process with 1-bit code."""
    if not isinstance(t,int) or t<0:
        raise ValueError('t must be a nonnegative integer')
    c=Fraction(1,4)**t
    a=(ONE+2*c)/3
    b=(ONE-c)/3
    result=two_code_optimal((a,b,b))
    formula=Fraction(4,9)*(ONE+c-2*c*c)
    assert result['tv']==formula
    return {'t':t,'c':str(c),'dominant_mass':str(a),
            'full_relational_tv':str(Fraction(2,3)*(ONE-c*c)),
            'optimal_onebit_tv':str(formula),
            'optimal_onebit_balanced_accuracy':str((ONE+formula)/2),
            'balanced_bin_mass':str(result['bin_mass'])}

if __name__=='__main__':
    import json
    print(json.dumps([three_matching_onebit(t) for t in range(8)],indent=2))
