"""ROC-02A retrospective, hash-gated NRF-09/11 frozen checkpoint pilot.

The official ROC-02 prospective delayed-rule task is an independent study.
This pilot uses six OLD seeds, two declared shadow states, nine ranks, 128
SHA256-keyed rank-matched Gaussian QR nulls per state and finite perturbations.
No sealed data or objective tuning is used. CPU-only.

Run: python roc02a_frozen_rank_causal.py --archive-root DIR --out-dir DIR
"""
from __future__ import annotations
import argparse, csv, hashlib, json, math, time
from collections import defaultdict
from statistics import median
from pathlib import Path
import torch
try:
    from research_gym.analysis.nrf10_leakage_aware_observer import gaussian_inputs, blocks, half_states
except ModuleNotFoundError:
    # Conversation archive fallback. The repo-native path uses the repaired
    # NRF-10/11 fold wrapper (required for folds 12/13).
    from nrf09_local import gaussian_inputs, blocks, half_states


def step_batch(weights,h):
    w1,b1,w2,b2=weights
    return h+.25*(torch.tanh(h@w1.T+b1)@w2.T+b2)

SEEDS=(131,137,139,149,151,157)
DEPTHS=(16,32)
RANKS=(1,2,3,4,7,8,12,16,32)
NULL_SEEDS=tuple(range(941001,941129))
SHADOW_INDICES=(0,1)
D=128
OUT=8
RADIUS=.2


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_cell(archive_root:Path,seed:int,depth:int):
    rdir=archive_root/'nrf11_work'/'receipts'
    receipt=json.loads((rdir/f'nrf11_R{depth}_S{seed}.json').read_text())
    checkpoint=archive_root/'nrf09_local'/'checkpoints'/f'nrf09_tied_R{depth}_S{seed}_steps32.pt'
    adapter=rdir/'observers'/f'nrf11_observer_R{depth}_S{seed}.pt'
    cksha,adsha=sha256(checkpoint),sha256(adapter)
    if cksha!=receipt['checkpoint_sha256'] or adsha!=receipt['observer_adapter_sha256']:
        raise RuntimeError(f'CHK_FAIL R{depth} S{seed}')
    model=torch.load(checkpoint,weights_only=True,map_location='cpu')
    state=model['state_dict']
    w=blocks(tuple(state[key] for key in ('blocks.0.in_proj.weight','blocks.0.in_proj.bias','blocks.0.out_proj.weight','blocks.0.out_proj.bias')))
    learned=torch.load(adapter,weights_only=True,map_location='cpu')
    if learned['model_checkpoint_sha256']!=cksha or learned['selected_gamma']!=receipt['selected_gamma_frozen_from_NRF10']:
        raise RuntimeError('observer provenance mismatch')
    return w,learned,cksha,adsha


def future_steps(w,h,steps):
    for _ in range(steps): h=step_batch(w,h)
    return h


def tangent(w,h,steps):
    w1,b1,w2,b2=w
    I=torch.eye(D,dtype=torch.float64)
    J=I.clone()
    state=h.clone()
    for _ in range(steps):
        act=torch.tanh(w1@state+b1)
        jac=I+.25*((w2*(1-act.square())[None,:])@w1)
        J=jac@J
        state=state+.25*(w2@act+b2)
    return J,state


def train_data(w,seed,depth):
    x,y=gaussian_inputs(seed,1,160)
    hmid=half_states(w,x,depth)
    hend=future_steps(w,hmid.clone(),depth//2)
    mean_h,mean_y=hmid.mean(0),y.mean(0)
    return hmid,y,hend,mean_h,mean_y


def train_output_head(h_end,y):
    mean_h,mean_y=h_end.mean(0),y.mean(0)
    X=h_end-mean_h
    W=torch.linalg.solve(X.T@X+torch.eye(D,dtype=torch.float64),X.T@(y-mean_y))
    return W,mean_h,mean_y


def rank_basis(htrain,ytrain,k):
    H=htrain-htrain.mean(0)
    Y=ytrain-ytrain.mean(0)
    cross=H.T@Y
    U,_,_=torch.linalg.svd(cross,full_matrices=False)
    if k<=OUT: return U[:,:k].contiguous()
    Q=torch.linalg.qr(U,mode='reduced')[0]
    residual=H-H@Q@Q.T
    _,_,vh=torch.linalg.svd(residual,full_matrices=False)
    padded=torch.cat((U,vh[:k-OUT].T),dim=1)
    result=torch.linalg.qr(padded,mode='reduced')[0]
    return result


def pca_basis(htrain,k):
    _,_,vh=torch.linalg.svd(htrain-htrain.mean(0),full_matrices=False)
    return vh[:k].T.contiguous()


def basis_ridge_mse(htrain,ytrain,htest,ytest,U):
    M=U.T@(htrain.mean(0))
    trainZ=(htrain-htrain.mean(0))@U
    testZ=(htest-htrain.mean(0))@U
    ridge=torch.linalg.solve(trainZ.T@trainZ+torch.eye(U.shape[1],dtype=torch.float64),trainZ.T@(ytrain-ytrain.mean(0)))
    pred=ytrain.mean(0)+testZ@ridge
    return float((pred-ytest).square().mean())


def seed_hash(cksha,idx,k,seed):
    s=f'{cksha}|fold13_shadow_{idx}|{k}|{seed}'
    return int.from_bytes(hashlib.sha256(s.encode()).digest()[:8],'big')%(2**63-1)


def seeded_basis(cksha,idx,k,seed):
    generator=torch.Generator(device='cpu').manual_seed(seed_hash(cksha,idx,k,seed))
    # Gaussian QR with a standardized sign convention, independent of SVD/gauge.
    g=torch.randn((D,k),generator=generator,dtype=torch.float64)
    u,r=torch.linalg.qr(g,mode='reduced')
    signs=torch.where(torch.diag(r)<0,-1.0,1.0)
    return u*signs[None,:]


def projector_slice_sha(U):
    P=(U[:16,:]@U[:16,:].T).to(dtype=torch.float32).contiguous()
    return hashlib.sha256(P.numpy().tobytes()).hexdigest()


def score_batch(U,Jout,Dmat):
    # U: Bxdxk; true rank-k basis stack. Gauge-invariant squared blocks.
    DU=torch.matmul(Dmat,U)
    DtU=torch.matmul(Dmat.T,U)
    A=torch.matmul(U.transpose(-1,-2),DU)
    an=A.square().sum((-1,-2))
    bn=torch.clamp(DtU.square().sum((-1,-2))-an,min=0.)
    cn=torch.clamp(DU.square().sum((-1,-2))-an,min=0.)
    dnorm=torch.linalg.norm(Dmat)
    ou=torch.matmul(Jout,U)
    hn=ou.square().sum((-1,-2))
    htot=Jout.square().sum()
    if float(dnorm)<=1e-12 or float(htot)<=1e-12:
        raise ValueError('zero dynamics or undefined output Gram in pilot')
    return torch.stack((an.sqrt()/dnorm,bn.sqrt()/dnorm,cn.sqrt()/dnorm,
                        hn/htot,an.sqrt(),bn.sqrt(),cn.sqrt()),dim=-1)


def pvalue(actual,scores,less):
    if len(scores)!=128: raise ValueError('registered null size changed')
    return (1+sum(x<=actual if less else x>=actual for x in scores))/129


def holm(raw):
    order=sorted(range(len(raw)),key=lambda i:(raw[i],i))
    adjusted=[1.]*len(raw)
    worst=0.
    for j,i in enumerate(order):
        worst=max(worst,min(1.,raw[i]*(len(raw)-j)))
        adjusted[i]=worst
    return adjusted


def fit_rank_readout(htrain,ytrain,U):
    Z=(htrain-htrain.mean(0))@U
    return torch.linalg.solve(Z.T@Z+torch.eye(U.shape[1],dtype=torch.float64),
                              Z.T@(ytrain-ytrain.mean(0)))


def finite_effects(w,h,head,Jout,idx,k,U,cksha,depth):
    hbase=future_steps(w,h,depth//2)
    base=hbase@head
    gen=torch.Generator(device='cpu').manual_seed(seed_hash(cksha,idx,k,940000))
    g=torch.randn(D,generator=gen,dtype=torch.float64)
    comp=g-U@(U.T@g)
    obs=U@(U.T@g)
    if float(comp.norm())<1e-10 or float(obs.norm())<1e-10:
        raise ValueError('degenerate intervention projection')
    deltas={'observed':RADIUS*obs/obs.norm(),'dark':RADIUS*comp/comp.norm(),'isotropic':RADIUS*g/g.norm()}
    vals={}
    for key,delta in deltas.items():
        actual=(future_steps(w,h+delta,depth//2)@head)-base
        linear=Jout@delta
        vals[key]=float(actual.norm())
        vals['linear_'+key]=float(linear.norm())
        vals['linear_residual_'+key]=float((actual-linear).norm())
        if abs(float(delta.norm())-RADIUS)>1e-10:
            raise AssertionError('physical intervention not norm matched')
    return vals


def run_cell(root,out,seed,depth):
    t0=time.monotonic()
    weights,learned,cksha,adsha=load_cell(root,seed,depth)
    htrain,ytrain,hen,mean_h,mean_y=train_data(weights,seed,depth)
    head,mean_last,head_mean_y=train_output_head(hen,ytrain)
    x_eval,y_eval=gaussian_inputs(seed,12,96)
    h_eval=half_states(weights,x_eval,depth)
    test_future=future_steps(weights,h_eval,depth//2)
    out_mse=float(((head_mean_y+(test_future-mean_last)@head)-y_eval).square().mean())
    x_shadow,y_shadow=gaussian_inputs(seed,13,12)
    hshadow=half_states(weights,x_shadow,depth)
    rankMSE={};bases={}
    for k in RANKS:
        for choice,base in [('supervised',rank_basis(htrain,ytrain,k)),('pca',pca_basis(htrain,k))]:
            mse=basis_ridge_mse(htrain,ytrain,h_eval,y_eval,base)
            rankMSE[(k,choice)]=mse
            bases[(k,choice)]=base
    for choice,key in [('task_only','task_only_basis'),('joint','joint_basis')]:
        u=learned[key].detach().to(torch.float64)
        if u.shape!=(D,OUT):raise ValueError('wrong adapter rank')
        if float(torch.linalg.norm(u.T@u-torch.eye(OUT,dtype=torch.float64)))>1e-8:
            raise ValueError('adapter not orthogonal')
        bases[(OUT,choice)]=u
        rankMSE[(OUT,choice)]=basis_ridge_mse(htrain,ytrain,h_eval,y_eval,u)
    all_null=[];all_obs=[]
    for idx in SHADOW_INDICES:
        T,_=tangent(weights,hshadow[idx],depth//2)
        Dmat=T-torch.eye(D,dtype=torch.float64)
        Jout=head.T@T
        dnorm=float(torch.linalg.norm(Dmat))
        htrace=float(Jout.square().sum())
        if dnorm<=1e-12 or htrace<=1e-12:
            raise AssertionError('undefined computed-change or causal output card')
        for k in RANKS:
            null_basis=[seeded_basis(cksha,idx,k,seed_null) for seed_null in NULL_SEEDS]
            ustack=torch.stack(null_basis)
            null_scores=score_batch(ustack,Jout,Dmat).tolist()
            seen=set()
            for i,base in enumerate(null_basis):
                stamp=projector_slice_sha(base)
                if stamp in seen:raise ValueError('null projector slice collision')
                seen.add(stamp)
                metrics=null_scores[i]
                all_null.append({'study':'ROC-02A-retrospective','seed':seed,'depth':depth,'checkpoint_sha256':cksha,
                                 'shadow_index':idx,'rank':k,'null_seed':NULL_SEEDS[i],
                                 'D_frob':dnorm,'H_trace':htrace,
                                 'projector_slice_sha256':stamp,
                                 **dict(zip(('a','b','c','s','A_frob','B_frob','C_frob'),metrics))})
            if len(seen)<100: raise RuntimeError('insufficient distinct nulls')
            null_columns=list(zip(*null_scores))
            null_med=[float(median(v)) for v in null_columns[:4]]
            for choice in ('supervised','pca',*(['joint','task_only'] if k==8 else [])):
                base=bases[(k,choice)]
                a,b,c,s,A,B,C=score_batch(base.unsqueeze(0),Jout,Dmat)[0].tolist()
                pvals=[pvalue(a,null_columns[0],True),pvalue(b,null_columns[1],True),
                       pvalue(c,null_columns[2],True),pvalue(b,null_columns[1],False),
                       pvalue(s,null_columns[3],False),pvalue(s,null_columns[3],True)]
                qs=holm(pvals)
                ratios=[a/null_med[0],b/null_med[1],c/null_med[2],s/null_med[3]]
                finite=finite_effects(weights,hshadow[idx],head,Jout,idx,k,base,cksha,depth)
                ridge=fit_rank_readout(htrain,ytrain,base)
                prediction=mean_y+(hshadow[idx]-mean_h)@base@ridge
                ablated=mean_y
                target=y_shadow[idx]
                state_task_mse=float((prediction-target).square().mean())
                ablation_risk_delta=float(((ablated-target).square()-(prediction-target).square()).mean())
                ablation_output_shift=float((prediction-ablated).norm())
                all_obs.append({'study':'ROC-02A-retrospective','seed':seed,'depth':depth,
                      'checkpoint_sha256':cksha,'observer_adapter_sha256':adsha if choice in ('joint','task_only') else '',
                      'shadow_index':idx,'rank':k,'observer':choice,'task_mse':rankMSE[(k,choice)],
                      'task_mse_state':state_task_mse,'D_frob':dnorm,'H_trace':htrace,
                      'source_final_head_mse':out_mse,'a':a,'b':b,'c':c,'s':s,
                      'A_frob_per_sqrtk':A/math.sqrt(k),'B_frob_per_sqrtk':B/math.sqrt(k),
                      'C_frob_per_sqrtk':C/math.sqrt(k),'rho_dark':B/math.hypot(A,B) if math.hypot(A,B)>0 else None,
                      'median_null_a':null_med[0],'median_null_b':null_med[1],
                      'median_null_c':null_med[2],'median_null_s':null_med[3],
                      'ratio_a':ratios[0],'ratio_b':ratios[1],'ratio_c':ratios[2],'ratio_s':ratios[3],
                      'p_a_down':pvals[0],'p_b_down':pvals[1],'p_c_down':pvals[2],
                      'p_b_up':pvals[3],'p_s_up':pvals[4],'p_s_down':pvals[5],
                      'holm_q_a_down':qs[0],'holm_q_b_down':qs[1],'holm_q_c_down':qs[2],
                      'holm_q_b_up':qs[3],'holm_q_s_up':qs[4],'holm_q_s_down':qs[5],
                      'finite_observed_effect':finite['observed'],
                      'finite_dark_effect':finite['dark'],
                      'finite_isotropic_effect':finite['isotropic'],
                      'linear_observed_effect':finite['linear_observed'],
                      'linear_dark_effect':finite['linear_dark'],
                      'linear_isotropic_effect':finite['linear_isotropic'],
                      'linear_observed_residual':finite['linear_residual_observed'],
                      'linear_dark_residual':finite['linear_residual_dark'],
                      'linear_isotropic_residual':finite['linear_residual_isotropic'],
                      'readout_ablation_risk_delta':ablation_risk_delta,
                      'readout_ablation_output_shift':ablation_output_shift,
                      'radius':RADIUS,'classification':'unclassified_pending_prospective',
                      'status':'retrospective_model_task_family'})
    print(f'depth={depth} seed={seed} source_head_MSE={out_mse:.6f} null={len(all_null)} obs={len(all_obs)} seconds={time.monotonic()-t0:.2f}',flush=True)
    return all_null,all_obs


def save_csv(path,rows):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]))
        w.writeheader();w.writerows(rows)


def summarize(obs):
    groups=defaultdict(list)
    for x in obs:groups[(x['depth'],x['rank'],x['observer'])].append(x)
    summary=[]
    for key,records in sorted(groups.items()):
        if len(records)!=2*len(SEEDS):raise ValueError('missing pilot states')
        means={name:sum(x[name] for x in records)/len(records) for name in ('task_mse','a','b','c','s','ratio_a','ratio_b','ratio_c','ratio_s','finite_observed_effect','finite_dark_effect','finite_isotropic_effect','linear_observed_residual','linear_dark_residual','linear_isotropic_residual','readout_ablation_risk_delta')}
        def all_q(col):return sum(x[col]<=.05 for x in records)
        n=len(records)
        summary.append({'depth':key[0],'rank':key[1],'observer':key[2],
             'n_independent_models':len(SEEDS),'states_per_model':len(SHADOW_INDICES),
             **means,'b_below_null_median_states':sum(x['ratio_b']<1 for x in records),
             's_above_null_median_states':sum(x['ratio_s']>1 for x in records),
             'holm_b_down_significant_states':all_q('holm_q_b_down'),
             'holm_s_up_significant_states':all_q('holm_q_s_up')})
    return summary


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--archive-root',type=Path,required=True)
    p.add_argument('--out-dir',type=Path,required=True)
    p.add_argument('--seed',type=int,choices=SEEDS)
    p.add_argument('--depth',type=int,choices=DEPTHS)
    args=p.parse_args()
    torch.set_num_threads(2)
    seeds=(args.seed,) if args.seed else SEEDS
    depths=(args.depth,) if args.depth else DEPTHS
    all_null=[];all_obs=[]
    for d in depths:
        for s in seeds:
            a,b=run_cell(args.archive_root,args.out_dir,s,d)
            all_null.extend(a);all_obs.extend(b)
            save_csv(args.out_dir/'roc02a_rank_nulls.csv',all_null)
            save_csv(args.out_dir/'roc02a_rank_observers.csv',all_obs)
    if len(seeds)==len(SEEDS) and len(depths)==len(DEPTHS):
        summary=summarize(all_obs)
        save_csv(args.out_dir/'roc02a_rank_summary.csv',summary)
        provenance={'study':'ROC-02A-RETRO-frozen-NRF-rank-causal-pilot-v1',
              'n_null_rows':len(all_null),'n_observer_rows':len(all_obs),
              'ranks':RANKS,'model_seeds':SEEDS,'depths':DEPTHS,
              'registered_shadows':SHADOW_INDICES,'null_seeds':(NULL_SEEDS[0],NULL_SEEDS[-1]),
              'source':'Exact NRF-09 checkpoints and NRF-11 frozen adapters, SHA gated',
              'task_head':'Separate train-fold-1 ridge final-state head, 8 signed-permutation targets',
              'label':'Retrospective NRF synthetic task only; not prospective ROC-02 delayed-rule task',
              'null_basis':'SHA256-keyed torch Gaussian QR; projector 16x16 principal submatrix float32 SHA256',
              'provenance_files':{p.name:sha256(p) for p in (args.out_dir).glob('*.csv')}}
        (args.out_dir/'roc02a_manifest.json').write_text(json.dumps(provenance,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()