"""Post-review, exploratory heldout gamma-frontier and task-free leakage controls.
All previous NRF-11 folds and model seeds are already exposed. This is descriptive.
"""
import sys,time,torch,json,csv,hashlib,math
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'nrf09_local'))
sys.path.insert(0,str(Path(__file__).resolve().parent/'nrf10_work'))
import nrf09_local as source
import nrf10_leakage_aware_observer as n10
from nrf12_diag import jac,metric
root=Path(__file__).resolve().parent;torch.set_num_threads(1)
SEEDS=(131,137,139,149,151,157);out=[]
def leakage_only(U0,J,updates=80,lr=.02):
 raw=torch.nn.Parameter(U0.clone());op=torch.optim.Adam([raw],lr=lr)
 for _ in range(updates):
  op.zero_grad(set_to_none=True)
  U=torch.linalg.qr(raw,mode='reduced')[0]
  loss=n10.leakage_values(U,J).square().mean()
  loss.backward();torch.nn.utils.clip_grad_norm_([raw],10.);op.step()
 return torch.linalg.qr(raw.detach(),mode='reduced')[0]
def run(seed):
 R=32;chk=root/f'nrf09_local/checkpoints/nrf09_tied_R{R}_S{seed}_steps32.pt'
 source_receipt=json.load(open(root/f'nrf11_work/receipts/nrf11_R{R}_S{seed}.json'))
 assert hashlib.sha256(chk.read_bytes()).hexdigest()==source_receipt['checkpoint_sha256']
 W=n10.weight_tuple(chk)
 def data(fold,n):
  X,Y=source.gaussian_inputs(seed,fold,n)
  return source.half_states(W,X,R),Y
 train_h,train_y=data(1,160);mean_h=train_h.mean(0);mean_y=train_y.mean(0)
 U0=torch.linalg.qr(source.supervised_basis(train_h,train_y,mean_h,mean_y).T,mode='reduced')[0]
 H9,Y9=data(9,96);shadow9,_=data(9,12);J9=n10.dense_jacobians(W,shadow9,R)
 H12,Y12=data(12,96);shadow13,_=data(13,12);J13=n10.dense_jacobians(W,shadow13,R)
 ref=source_receipt['arms']['joint']['objective']
 for gamma in (0.,.05,.2,1.):
  U=n10.optimize(U0,train_h,train_y,mean_h,mean_y,J9,gamma)
  score=n10.evaluate(U,train_h,train_y,mean_h,mean_y,H12,Y12,J13)
  scale=metric(U,J13)
  if gamma==source_receipt['selected_gamma_frozen_from_NRF10']:
   assert abs(score['objective']-ref)<1e-8,(seed,gamma,score['objective'],ref)
  out.append(dict(seed=seed,arm=f'gamma={gamma:g}',gamma=gamma,mse=score['heldout_mse'],objective=score['objective'],**scale))
 for label,U in [('leak_only_supervised_start',U0),('leak_only_random_start',source.random_basis(8371+seed).T)]:
  U2=leakage_only(U,J9)
  score=n10.evaluate(U2,train_h,train_y,mean_h,mean_y,H12,Y12,J13)
  out.append(dict(seed=seed,arm=label,gamma=None,mse=score['heldout_mse'],objective=score['objective'],**metric(U2,J13)))
if __name__=='__main__':
 start=time.time()
 for seed in SEEDS:
  run(seed); print('seed',seed,'done',round(time.time()-start,1),'seconds',flush=True)
 outp=root/'NRF_postreview_gamma_frontier.csv'
 with outp.open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=['seed','arm','gamma','mse','objective','leakage','rho','write_gain','within_gain']);w.writeheader();w.writerows(out)
 print('written',outp,round(time.time()-start,1))
 for arm in sorted({r['arm'] for r in out}):
  v=[r for r in out if r['arm']==arm];print(arm,{k:round(sum(r[k] for r in v)/len(v),6) for k in ('mse','leakage','rho','objective','write_gain','within_gain')})
