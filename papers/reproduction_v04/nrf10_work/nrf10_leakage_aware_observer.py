"""NRF-10: frozen-weight, rank-8 leakage-aware observation ablation.

Registered protocol: configs/nrf10_leakage_aware_observer_v1.json
Training fold 1, calibration fold 9, untouched final task fold 10 and shadow fold 11.
The task-only and joint arms receive the same optimizer budget and initial subspace.
The 128D ToyLoop state update and reference decoding match NRF-09.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
import torch

try:
    from research_gym.analysis.nrf09_matched_optimizer_steps import gaussian_inputs
    from research_gym.analysis.nrf04_semantic_fiber import (
        blocks, half_states, supervised_basis, random_basis, ridge_head,
        heldout_mse,
    )
except ModuleNotFoundError:
    # Standalone archive replay with the validated independent NRF-09 source.
    from nrf09_local import (
        gaussian_inputs, blocks, half_states, supervised_basis,
        random_basis, ridge_head, heldout_mse,
    )

SEEDS=(131,137,139,149,151,157)
DEPTHS=(16,32)
K=8
GAMMAS=(0.05,0.2,1.0)
UPDATES=80
LR=0.02


def source_sha(path:Path,seed:int,depth:int,source_receipts:Path)->str:
    actual=hashlib.sha256(path.read_bytes()).hexdigest()
    if source_receipts.is_dir():
        source=json.loads((source_receipts/f'nrf09_R{depth}_S{seed}.json').read_text())
        expected=next(x['checkpoint_sha256'] for x in source['rows'] if int(x['optimizer_steps'])==32)
    else:
        with source_receipts.open(newline='') as handle:
            rows=list(csv.DictReader(handle))
        expected=next(x['checkpoint_sha256'] for x in rows if int(x['seed'])==seed and int(x['rounds'])==depth and int(x['optimizer_steps'])==32)
    if actual!=expected:
        raise RuntimeError(f'NRF-10 source checkpoint SHA mismatch R{depth} S{seed}: {actual} != {expected}')
    return actual


def weight_tuple(checkpoint:Path):
    item=torch.load(checkpoint,map_location='cpu',weights_only=True)
    state=item['state_dict']
    return blocks(tuple(state[key] for key in (
        'blocks.0.in_proj.weight','blocks.0.in_proj.bias',
        'blocks.0.out_proj.weight','blocks.0.out_proj.bias')))


def dense_jacobians(weights,halfway_states,depth):
    """Canonical chronological product of the last depth/2 tied updates."""
    w1,b1,w2,b2=weights
    size=len(b1)
    eye=torch.eye(size,dtype=torch.float64)
    mats=[]
    with torch.no_grad():
        for h0 in halfway_states:
            h=h0.clone()
            J=eye.clone()
            for _ in range(depth//2):
                a=torch.tanh(w1@h+b1)
                step=eye+0.25*(w2*(1-a*a)[None,:])@w1
                J=step@J
                h=h+0.25*(w2@a+b2)
            mats.append(J)
    return torch.stack(mats)


def leakage_values(U,J):
    """Per-state ||U^T J (I-UU^T)||_F/sqrt(k); U orthonormal columns."""
    if U.shape!=(128,K) or J.ndim!=3 or J.shape[1:]!=(128,128):
        raise ValueError('expected rank-eight observation and batch 128x128 Jacobians')
    visible=torch.matmul(U.T.unsqueeze(0),J)   # shadow, k, 128
    self_term=torch.matmul(visible,U)           # shadow, k, k
    # Tensor arithmetic can produce tiny negative values from cancellation.
    energy=(visible.square().sum(dim=(-1,-2))-self_term.square().sum(dim=(-1,-2)))/K
    return torch.sqrt(torch.clamp(energy,min=0.))


def ridge_from_U(H,Y,U,mean_h,mean_y):
    Z=(H-mean_h)@U
    head=torch.linalg.solve(Z.T@Z+torch.eye(K,dtype=torch.float64),Z.T@(Y-mean_y))
    return head


def task_error(H,Y,U,head,mean_h,mean_y):
    return torch.mean((mean_y+(H-mean_h)@U@head-Y).square())


def evaluate(U,train_h,train_y,mean_h,mean_y,val_h,val_y,val_j):
    with torch.no_grad():
        H=ridge_from_U(train_h,train_y,U,mean_h,mean_y)
        E=float(task_error(val_h,val_y,U,H,mean_h,mean_y))
        lv=leakage_values(U,val_j)
        L=float(lv.mean())
        return {'heldout_mse':E,'local_fiber_leakage':L,'objective':E+L*L,
                'mean_leakage_squared':float((lv*lv).mean())}


def optimize(U0,train_h,train_y,mean_h,mean_y,cal_j,gamma,updates=UPDATES,lr=LR):
    raw=torch.nn.Parameter(U0.clone())
    optimizer=torch.optim.Adam([raw],lr=lr)
    for _ in range(updates):
        optimizer.zero_grad(set_to_none=True)
        U=torch.linalg.qr(raw,mode='reduced')[0]
        head=ridge_from_U(train_h,train_y,U,mean_h,mean_y)
        error=task_error(train_h,train_y,U,head,mean_h,mean_y)
        values=leakage_values(U,cal_j)
        objective=error+gamma*(values*values).mean()
        objective.backward()
        torch.nn.utils.clip_grad_norm_([raw],10.)
        optimizer.step()
    return torch.linalg.qr(raw.detach(),mode='reduced')[0]


def run_cell(seed:int,depth:int,checkpoint:Path,receipts:Path,output:Path):
    if seed not in SEEDS or depth not in DEPTHS:
        raise ValueError('out of preregistered study grid')
    checkpoint_hash=source_sha(checkpoint,seed,depth,receipts)
    weights=weight_tuple(checkpoint)
    def data(fold,n):
        x,y=gaussian_inputs(seed,fold,n)
        return half_states(weights,x,depth),y
    torch.set_num_threads(1)
    with torch.no_grad():
        train_h,train_y=data(1,160)
        cal_h,cal_y=data(9,96)
        cal_shadow,_=data(9,12)
        mean_h,mean_y=train_h.mean(0),train_y.mean(0)
        base=supervised_basis(train_h,train_y,mean_h,mean_y).T
        U0=torch.linalg.qr(base,mode='reduced')[0]
        jac_cal=dense_jacobians(weights,cal_shadow,depth)
        base_cal=evaluate(U0,train_h,train_y,mean_h,mean_y,cal_h,cal_y,jac_cal)
    task=optimize(U0,train_h,train_y,mean_h,mean_y,jac_cal,0.)
    candidates=[]
    for gamma in GAMMAS:
        U=optimize(U0,train_h,train_y,mean_h,mean_y,jac_cal,gamma)
        v=evaluate(U,train_h,train_y,mean_h,mean_y,cal_h,cal_y,jac_cal)
        v.update({'gamma':gamma,'eligible':v['heldout_mse']<=1.10*base_cal['heldout_mse']})
        candidates.append((v,U))
    eligible=[c for c in candidates if c[0]['eligible']]
    if eligible:
        choice=min(eligible,key=lambda c:(c[0]['objective'],c[0]['gamma']))
        fallback=False
    else:
        choice=min(candidates,key=lambda c:(c[0]['heldout_mse'],c[0]['gamma']))
        fallback=True
    selected,Ujoint=choice
    # Open the unseen final evaluation folds only after all candidate tuning.
    with torch.no_grad():
        test_h,test_y=data(10,96)
        shadow,_=data(11,12)
        jac_test=dense_jacobians(weights,shadow,depth)
        choices={'supervised':U0,'task_only':task,'joint':Ujoint}
        for i in range(8):
            choices[f'random_{i}']=random_basis(400000+31*i+17*seed).T
        measured={name:evaluate(U,train_h,train_y,mean_h,mean_y,test_h,test_y,jac_test)
                  for name,U in choices.items()}
        ordered=sorted(measured[f'random_{i}']['objective'] for i in range(8))
        random_med=(ordered[3]+ordered[4])/2
        sup,joint=measured['supervised'],measured['joint']
        improvement={
            'task_limit_passed':joint['heldout_mse']<=1.10*sup['heldout_mse'],
            'leakage_limit_passed':joint['local_fiber_leakage']<=0.90*sup['local_fiber_leakage'],
            'joint_dominates_supervised_and_random':joint['objective']<min(sup['objective'],random_med)}
        improvement['primary_passed']=all(improvement.values())
        projdist=float(torch.linalg.norm(Ujoint@Ujoint.T-U0@U0.T))
        gram_err=float(torch.linalg.norm(Ujoint.T@Ujoint-torch.eye(K,dtype=torch.float64)))
    outcome={
        'study_id':'NRF-10-frozen-weight-leakage-aware-observer-v1',
        'seed':seed,'depth':depth,'optimizer_steps':32,'checkpoint_sha256':checkpoint_hash,
        'calibration':{'supervised':base_cal,'candidates':[x[0] for x in candidates],
                       'selected_gamma':selected['gamma'],'fallback_no_eligible_candidate':fallback},
        'heldout':{'arms':measured,'random_median_complete_objective':random_med,
                   'gate':improvement,'projector_frobenius_distance':projdist,
                   'orthogonality_error':gram_err},
        'protocol':'Fold1 train, fold9 calibration, folds10/11 opened after selection; frozen weights',
        'torch_version':torch.__version__,
    }
    output.mkdir(parents=True,exist_ok=True)
    (output/f'nrf10_R{depth}_S{seed}.json').write_text(json.dumps(outcome,indent=2,sort_keys=True)+'\n')
    return outcome


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed',type=int,required=True,choices=SEEDS)
    parser.add_argument('--depth',type=int,required=True,choices=DEPTHS)
    parser.add_argument('--checkpoints',type=Path,required=True)
    parser.add_argument('--source-receipts',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    ck=args.checkpoints/f'nrf09_tied_R{args.depth}_S{args.seed}_steps32.pt'
    result=run_cell(args.seed,args.depth,ck,args.source_receipts,args.out)
    o=result['heldout']; print(f'R{args.depth} S{args.seed} gamma={result["calibration"]["selected_gamma"]} MSE={o["arms"]["joint"]["heldout_mse"]:.5f} L={o["arms"]["joint"]["local_fiber_leakage"]:.5f} jointJ={o["arms"]["joint"]["objective"]:.5f} supJ={o["arms"]["supervised"]["objective"]:.5f} rand_med={o["random_median_complete_objective"]:.5f} primary={o["gate"]["primary_passed"]}',flush=True)

if __name__=='__main__':
    main()
