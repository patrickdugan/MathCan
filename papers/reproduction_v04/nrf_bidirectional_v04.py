"""Post-review NRF-01--11 observer-direction audit (v0.4).

Read-only, SHA-gated, using the archived NRF09 model and NRF11 adapter bytes.
Input is the reproduction/ directory of NRF_Revised_v02_Site_Draft_and_Reproduction.zip
No neural training occurs. All diagnostics are post-hoc on NRF11 fold 13.

Per shadow sample and orthonormal U, P=UU^T, Q=I-P, D=T-I:
  B = P D Q  (dark to observed)
  C = Q D P  (observed to dark)
  A = P D P  (within observed)
Compute the Frobenius norm of each divided by sqrt(k).
Mean per-state ratios only; ratios of pooled means are separately identified.
"""
from __future__ import annotations
import argparse, csv, hashlib, json, math, sys
from pathlib import Path
import torch

SEEDS=(131,137,139,149,151,157)
DEPTHS=(16,32)
K=8


def bootstrap(root:Path):
    sys.path.insert(0,str(root/'nrf09_local'))
    import nrf09_local as n09
    return n09


def jacobians(weights, midpoints, depth:int):
    w1,b1,w2,b2=weights
    eye=torch.eye(len(b1),dtype=torch.float64)
    result=[]
    for h0 in midpoints:
        h=h0.clone(); tangent=eye.clone()
        for _ in range(depth//2):
            a=torch.tanh(w1@h+b1)
            one=eye+.25*(w2*(1-a*a)[None,:])@w1
            tangent=one@tangent
            h=h+.25*(w2@a+b2)
        result.append(tangent)
    return torch.stack(result)


def batch_metrics(basis, tangents):
    """Every scalar is per-state, with exact orthogonal block decomposition."""
    U=basis.to(torch.float64)
    eye=torch.eye(U.shape[0],dtype=torch.float64)
    assert U.shape==(128,8)
    assert float(torch.linalg.norm(U.T@U-torch.eye(K,dtype=torch.float64)))<1e-9
    P=U@U.T; Q=eye-P
    rows=[]
    for T in tangents:
        D=T-eye
        # Compute the two rectangular channels without materializing P D Q.
        a=U.T@D@U
        upper=U.T@D; right=D@U
        incoming=upper@Q
        outgoing=Q@right
        in_n=float(torch.linalg.vector_norm(incoming))/math.sqrt(K)
        out_n=float(torch.linalg.vector_norm(outgoing))/math.sqrt(K)
        within=float(torch.linalg.vector_norm(a))/math.sqrt(K)
        write=float(torch.linalg.vector_norm(upper))/math.sqrt(K)
        drive=float(torch.linalg.vector_norm(right))/math.sqrt(K)
        original=float(torch.linalg.vector_norm(U.T@T@Q))/math.sqrt(K)
        tol=1e-10
        if abs(original-in_n)>tol or abs(write*write-in_n*in_n-within*within)>tol or abs(drive*drive-out_n*out_n-within*within)>tol:
            raise AssertionError('Jacobian block identity/replay mismatch')
        rows.append(dict(incoming=in_n, outgoing=out_n, within_change=within,
                        write_change=write, origin_change=drive,
                        incoming_fraction=in_n/write if write>1e-14 else float('nan'),
                        outgoing_fraction=out_n/drive if drive>1e-14 else float('nan'),
                        incoming_outgoing_ratio=in_n/out_n if out_n>1e-14 else float('nan'),
                        reverse_asymmetry=(in_n-out_n)/(in_n+out_n) if in_n+out_n>1e-14 else float('nan')))
    return rows


def source_weights(checkpoint, n09):
    d=torch.load(checkpoint,map_location='cpu',weights_only=True)
    w=d['state_dict']
    return n09.blocks(tuple(w[k] for k in ('blocks.0.in_proj.weight',
                'blocks.0.in_proj.bias','blocks.0.out_proj.weight',
                'blocks.0.out_proj.bias')))


def run(root:Path):
    n09=bootstrap(root)
    torch.set_num_threads(1)
    per_state=[]; per_seed=[]
    for depth in DEPTHS:
        for seed in SEEDS:
            chk=root/'nrf09_local/checkpoints'/f'nrf09_tied_R{depth}_S{seed}_steps32.pt'
            adapter=root/'nrf11_work/receipts/observers'/f'nrf11_observer_R{depth}_S{seed}.pt'
            rec=json.loads((root/'nrf11_work/receipts'/f'nrf11_R{depth}_S{seed}.json').read_text())
            assert hashlib.sha256(chk.read_bytes()).hexdigest()==rec['checkpoint_sha256'],(depth,seed,'model SHA')
            assert hashlib.sha256(adapter.read_bytes()).hexdigest()==rec['observer_adapter_sha256'],(depth,seed,'adapter SHA')
            weights=source_weights(chk,n09)
            x,_=n09.gaussian_inputs(seed,13,12)
            h=n09.half_states(weights,x,depth)
            tangents=jacobians(weights,h,depth)
            frozen=torch.load(adapter,weights_only=True,map_location='cpu')
            bases={x:frozen[x+'_basis'] for x in ('supervised','task_only','joint')}
            for i in range(8):bases[f'random_{i}']=n09.random_basis(400000+31*i+17*seed).T
            for arm,U in bases.items():
                state_rows=batch_metrics(U,tangents)
                if arm in rec['arms']:
                    meanB=sum(row['incoming'] for row in state_rows)/len(state_rows)
                    expected=rec['arms'][arm]['local_fiber_leakage']
                    assert abs(meanB-expected)<1e-8,(seed,depth,arm,meanB,expected)
                for i,r in enumerate(state_rows):per_state.append({'depth':depth,'seed':seed,'arm':arm,'shadow_index':i,**r})
                means={k:sum(r[k] for r in state_rows)/len(state_rows) for k in state_rows[0]}
                per_seed.append({'depth':depth,'seed':seed,'arm':arm,**means})
            print(f'validated depth {depth} seed {seed}',flush=True)
    return per_state,per_seed


def write_csv(path,records):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=list(records[0]));writer.writeheader();writer.writerows(records)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'outputs_v04')
    args=ap.parse_args()
    records,seedrows=run(args.root)
    write_csv(args.output/'NRF_v04_bidirectional_per_state.csv',records)
    write_csv(args.output/'NRF_v04_bidirectional_per_seed.csv',seedrows)
    groups=[]
    for depth in DEPTHS:
        for arm in ('supervised','task_only','joint'):
            sub=[r for r in seedrows if r['depth']==depth and r['arm']==arm]
            means={k:sum(r[k] for r in sub)/len(sub) for k in ('incoming','outgoing','within_change','write_change','origin_change','incoming_fraction','outgoing_fraction','reverse_asymmetry')}
            groups.append({'depth':depth,'arm':arm,**means})
            print('GROUP',depth,arm,{k:round(v,6) for k,v in means.items()})
    (args.output/'NRF_v04_bidirectional_summary.json').write_text(json.dumps({'group_means':groups,'units':'Frobenius /sqrt(8); per-state ratios averaged within seed, then across six seeds','scope':'post-hoc same-model NRF11 fold13; no intervention'},indent=2)+'\n')
    print('Saved per-state:',len(records),'per-seed:',len(seedrows))
if __name__=='__main__':main()
