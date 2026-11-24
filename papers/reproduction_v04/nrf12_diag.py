import sys,torch,math,json,csv,hashlib,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'nrf09_local')); import nrf09_local as m
torch.set_num_threads(1); S=(131,137,139,149,151,157); root=Path(__file__).resolve().parent
def jac(W,H,R):
 w1,b1,w2,b2=W; I=torch.eye(128,dtype=torch.float64); out=[]
 for h in H:
  J=I.clone(); h=h.clone()
  for _ in range(R//2):
   a=torch.tanh(w1@h+b1);J=(I+.25*(w2*(1-a*a)[None,:])@w1)@J;h=h+.25*(w2@a+b2)
  out.append(J)
 return torch.stack(out)
def metric(U,J):
 V=U.T@J; C=V@U
 total=torch.linalg.vector_norm(V,dim=(1,2))/math.sqrt(8)
 within=torch.linalg.vector_norm(C,dim=(1,2))/math.sqrt(8)
 dark=torch.sqrt(torch.clamp(total**2-within**2,min=0))
 return {'leakage':dark.mean().item(),'rho':(dark/total).mean().item(),'write_gain':total.mean().item(),'within_gain':within.mean().item()}
def weights(d):
 s=d['state_dict'];return m.blocks(tuple(s[k] for k in ('blocks.0.in_proj.weight','blocks.0.in_proj.bias','blocks.0.out_proj.weight','blocks.0.out_proj.bias')))
def snapshot(W,seed,R):
 x,y=m.gaussian_inputs(seed,1,160); H=m.half_states(W,x,R);mh=H.mean(0);my=y.mean(0)
 U=m.supervised_basis(H,y,mh,my).T
 z,t=m.gaussian_inputs(seed,12,96);h=m.half_states(W,z,R)
 mse=m.heldout_mse(h,t,U.T,mh,my,m.ridge_head(H,y,U.T,mh,my))
 z,_=m.gaussian_inputs(seed,13,12);h=m.half_states(W,z,R)
 r=metric(U,jac(W,h,R));r['mse']=mse;r['J']=mse+r['leakage']**2;return r
def main():
 rows=[];start=time.time()
 for R in (16,32):
  for seed in S:
   rootpath=root/f'nrf09_local/checkpoints/nrf09_tied_R{R}_S{seed}_steps32.pt';d=torch.load(rootpath,weights_only=True)
   receipt=json.load(open(root/f'nrf11_work/receipts/nrf11_R{R}_S{seed}.json'))
   assert hashlib.sha256(rootpath.read_bytes()).hexdigest()==receipt['checkpoint_sha256']
   W=weights(d); z,_=m.gaussian_inputs(seed,13,12);h=m.half_states(W,z,R);J=jac(W,h,R)
   adapter=root/f'nrf11_work/receipts/observers/nrf11_observer_R{R}_S{seed}.pt';a=torch.load(adapter,weights_only=True)
   assert hashlib.sha256(adapter.read_bytes()).hexdigest()==receipt['observer_adapter_sha256']
   for arm in ('supervised','task_only','joint'):
    t=metric(a[arm+'_basis'],J)
    assert abs(t['leakage']-receipt['arms'][arm]['local_fiber_leakage'])<1e-8
    rows.append(dict(depth=R,seed=seed,arm=arm,**t))
   torch.manual_seed(seed);initial=m.ToyLoop(128,R,tied=True,alpha=1.,beta=.25);b=initial.blocks[0]
   w=m.blocks((b.in_proj.weight,b.in_proj.bias,b.out_proj.weight,b.out_proj.bias))
   rows.append(dict(depth=R,seed=seed,arm='step0',**snapshot(w,seed,R)))
   print('completed',R,seed,'seconds',round(time.time()-start,1),flush=True)
 with open(root/'NRF_postreview_metrics.csv','w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=['depth','seed','arm','leakage','rho','write_gain','within_gain','mse','J']);w.writeheader();w.writerows(rows)
 for R in (16,32):
  for arm in ('step0','supervised','task_only','joint'):
   q=[r for r in rows if r['depth']==R and r['arm']==arm]
   print('AVERAGE',R,arm,{k:round(sum(r[k] for r in q)/len(q),5) for k in ('leakage','rho','write_gain','within_gain')},flush=True)
 print('saved',len(rows),'rows; elapsed',round(time.time()-start,1))
if __name__=='__main__': main()
