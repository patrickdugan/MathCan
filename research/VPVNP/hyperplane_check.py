"""VPVNP-02D exact finite parity kernel and coset checks."""
import json

def pair(b,a):
    return (b&a).bit_count() & 1

def run(n):
    q=1<<n
    masks=range(1,q)
    kernels={b:tuple(a for a in range(q) if not pair(b,a)) for b in masks}
    outs={b:tuple(a for a in range(q) if pair(b,a)) for b in masks}
    assert len(set(kernels.values()))==q-1
    assert all(len(outs[b])==len(kernels[b])==q//2 for b in masks)
    comparisons=0
    for b in masks:
        ann=[d for d in range(q) if all(not pair(d,a) for a in kernels[b])]
        assert ann==[0,b]
        for c in masks:
            val=sum(1-2*pair(c,a) for a in outs[b])
            assert val==(-q//2 if b==c else 0)
            if b!=c:
                assert any(pair(c,a) for a in kernels[b])
            comparisons+=1
    # Independent coordinate normals, restricted to last normal's kernel.
    independent_cases=0
    b=1<<(n-1)
    for k in range(n):
        for d in range(1<<k):
            assert all(not pair(d,a) for a in kernels[b]) == (d==0)
            independent_cases+=1
    return dict(n=n,hyperplanes=q-1,outside_size=q//2,normal_pairs=comparisons,
                annihilator_checks=(q-1)*q,restricted_combinations=independent_cases)

if __name__=='__main__':
    rows=[run(n) for n in range(1,7)]
    print(json.dumps(dict(experiment='VPVNP-02D',sizes=rows,
        normal_pairs=sum(x['normal_pairs'] for x in rows),
        status='PASS'),sort_keys=True,indent=2))
