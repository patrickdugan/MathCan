"""Reconstruct exact NRF-09 matched-optimizer-step CPU six-seed protocol.

This standalone scratch reproduction mirrors the linked repository's source. A
repository version imports the canonical source modules rather than duplicating.
"""
import copy,hashlib,json,math,sys,time
from pathlib import Path
import torch
from torch import nn
N=128;K=8
SEEDS=(131,137,139,149,151,157)
class ToyResidualBlock(nn.Module):
    def __init__(self,hidden_size,*,alpha=1.,beta=1.):
        super().__init__();self.hidden_size=hidden_size;self.alpha=alpha;self.beta=beta
        self.in_proj=nn.Linear(hidden_size,hidden_size)
        self.out_proj=nn.Linear(hidden_size,hidden_size)
    def forward(self,state):
        branch=self.out_proj(torch.tanh(self.in_proj(state)))
        return self.alpha*state+self.beta*branch
class ToyLoop(nn.Module):
    def __init__(self,hidden_size,rounds,*,tied,alpha=1.,beta=1.):
        super().__init__();self.rounds=rounds;self.tied=tied
        self.blocks=nn.ModuleList(ToyResidualBlock(hidden_size,alpha=alpha,beta=beta) for _ in range(1 if tied else rounds))
    def forward(self,state):
        for visit in range(self.rounds):
            state=self.blocks[0 if self.tied else visit](state)
        return state

def signed_permutation_batch(seed,batch_size,hidden_size,stream):
    generator=torch.Generator(device="cpu").manual_seed(seed*1009+stream)
    inputs=torch.randn(batch_size,hidden_size,generator=generator)
    permutation=torch.randperm(hidden_size,generator=torch.Generator().manual_seed(seed+17))
    signs=torch.where(torch.rand(hidden_size,generator=torch.Generator().manual_seed(seed+29))>0.5,1.0,-1.0)
    targets=torch.tanh(inputs[:,permutation]*signs)
    return inputs,targets

def gaussian_stream(seed):
    state=seed & 0xffffffff
    while True:
        state=(1664525*state+1013904223)&0xffffffff
        u=(state+.5)/4294967296
        state=(1664525*state+1013904223)&0xffffffff
        v=(state+.5)/4294967296
        yield math.sqrt(-2*math.log(u))*math.cos(2*math.pi*v)

def gaussian_inputs(task_seed,fold,count):
    stream=gaussian_stream(20261115+7919*task_seed+104729*fold)
    x=torch.tensor([[next(stream) for _ in range(N)] for _ in range(count)],dtype=torch.float64)
    permutation=torch.randperm(N,generator=torch.Generator().manual_seed(task_seed+17))[:K]
    signs=torch.where(torch.rand(N,generator=torch.Generator().manual_seed(task_seed+29))>.5,1.,-1.)[:K].to(torch.float64)
    return x,torch.tanh(x[:,permutation]*signs)

def blocks(parameters):
    return tuple(x.detach().cpu().to(torch.float64) for x in parameters)

def step_batch(parameters,h):
    w1,b1,w2,b2=parameters
    return h+.25*(torch.tanh(h@w1.T+b1)@w2.T+b2)

def half_states(parameters,x,rounds):
    h=x.clone()
    for _ in range(rounds//2):h=step_batch(parameters,h)
    return h

def orthonormal_columns(columns):
    out=[]
    for column in columns:
        v=column.clone()
        for _ in range(2):
            for q in out:v-=q*torch.dot(q,v)
        length=float(v.norm())
        if length<1e-10:raise ValueError('degenerate')
        out.append(v/length)
    return torch.stack(out)

def supervised_basis(h,y,mean_h,mean_y,shifted=False):
    train_labels=torch.roll(y,shifts=-1,dims=0) if shifted else y
    cov=(h-mean_h).T@(train_labels-mean_y)
    return orthonormal_columns([cov[:,j] for j in range(K)])

def random_basis(seed):
    stream=gaussian_stream(seed)
    cols=torch.tensor([[next(stream) for _ in range(N)] for _ in range(K)],dtype=torch.float64)
    return orthonormal_columns(cols)

def coordinate_basis():return torch.eye(N,dtype=torch.float64)[:K]

def ridge_head(train_h,train_y,basis,mean_h,mean_y):
    z=(train_h-mean_h)@basis.T
    gram=z.T@z+torch.eye(K,dtype=torch.float64)
    return torch.linalg.solve(gram,z.T@(train_y-mean_y))

def heldout_mse(test_h,test_y,basis,mean_h,mean_y,head):
    prediction=mean_y+(test_h-mean_h)@basis.T@head
    return float(torch.mean((prediction-test_y)**2))

def suffix_derivatives(parameters,h,count):
    w1,b1,w2,b2=parameters
    derivatives=[]
    for _ in range(count):
        a=torch.tanh(w1@h+b1)
        derivatives.append(1-a*a)
        h=h+.25*(w2@a+b2)
    return derivatives

def leakage_at(parameters,h,suffix_length,basis):
    w1,b1,w2,b2=parameters
    derivatives=suffix_derivatives(parameters,h,suffix_length)
    squared=0.
    for u in basis:
        v=u.clone()
        for derivative in reversed(derivatives):
            v=v+.25*w1.T@(derivative*(w2.T@v))
        dark=v-basis.T@(basis@v)
        squared+=float(torch.dot(dark,dark))
    return math.sqrt(max(0.,squared/K))

def train_one(seed,rounds,outdir):
    torch.manual_seed(seed)
    model=ToyLoop(N,rounds,tied=True,alpha=1.,beta=.25).to('cpu')
    optimizer=torch.optim.AdamW(model.parameters(),lr=.001,weight_decay=0.)
    outdir.mkdir(parents=True,exist_ok=True)
    snapshots=[]
    for step in range(1,33):
        x,y=signed_permutation_batch(seed,8,N,step-1)
        optimizer.zero_grad(set_to_none=True)
        loss=torch.nn.functional.mse_loss(model(x),y)
        loss.backward();optimizer.step()
        exposure=step*8*rounds
        if step not in (16,32):continue
        snap=copy.deepcopy(model.state_dict())
        path=outdir/f'nrf09_tied_R{rounds}_S{seed}_steps{step}.pt'
        torch.save({'cell_id':f'nrf09_tied_R{rounds}_S{seed}','step':step,'exposure':exposure,'state_dict':snap,'optimizer':copy.deepcopy(optimizer.state_dict())},path)
        snapshots.append({'rounds':rounds,'seed':seed,'exposure':exposure,'step':step,'checkpoint_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'train_loss_latest':float(loss),'state_dict':snap})
    return snapshots

def fixed_state_suffix_replay(snapshot,suffix_lengths=(8,16)):
    rounds,seed=snapshot['rounds'],snapshot['seed'];state=snapshot['state_dict']
    weights=blocks(tuple(state[key] for key in ('blocks.0.in_proj.weight','blocks.0.in_proj.bias','blocks.0.out_proj.weight','blocks.0.out_proj.bias')))
    def dataset(fold,size):
        x,y=gaussian_inputs(seed,fold,size)
        return half_states(weights,x,rounds),y
    with torch.no_grad():
        h_train,y_train=dataset(1,160)
        h_test,y_test=dataset(7,96)
        h_shadow,_=dataset(8,12)
        mean_h,mean_y=h_train.mean(0),y_train.mean(0)
        bases={'supervised':supervised_basis(h_train,y_train,mean_h,mean_y),'label_shifted_train_null':supervised_basis(h_train,y_train,mean_h,mean_y,shifted=True),'first_eight_coordinates':coordinate_basis()}
        for i in range(8):bases[f'random_{i}']=random_basis(400000+31*i+17*seed)
        errors={}
        for name,basis in bases.items():
            head=ridge_head(h_train,y_train,basis,mean_h,mean_y)
            errors[name]=heldout_mse(h_test,y_test,basis,mean_h,mean_y,head)
        rows=[]
        for s in suffix_lengths:
            arms={}
            for name,basis in bases.items():
                leak=sum(leakage_at(weights,h,s,basis) for h in h_shadow)/len(h_shadow)
                mse=errors[name]
                arms[name]={'heldout_mse':mse,'local_fiber_leakage':leak,'lambda_one_objective':mse+leak**2}
            ref=sorted(arms[f'random_{i}']['lambda_one_objective'] for i in range(8))
            med=(ref[3]+ref[4])/2
            rows.append({'suffix_visits':s,'arms':arms,'supervised_objective':arms['supervised']['lambda_one_objective'],'random_median_objective':med,'supervised_wins':arms['supervised']['lambda_one_objective']<med})
    return {'id':f'R{rounds}_S{seed}_E{snapshot["exposure"]}','trained_rounds':rounds,'seed':seed,'exposure':snapshot['exposure'],'checkpoint_sha256':snapshot['checkpoint_sha256'],'suffix_rows':rows}

if __name__=='__main__':
    torch.set_num_threads(1)
    seed=int(sys.argv[1]); rounds=int(sys.argv[2]); start=time.monotonic()
    outdir=Path('/mnt/data/nrf09_local/checkpoints')
    snapshots=train_one(seed,rounds,outdir)
    output=[]
    for snapshot in snapshots:
        row=fixed_state_suffix_replay(snapshot,(rounds//2,))['suffix_rows'][0]
        row.update({
            'seed':seed,'rounds':rounds,'optimizer_steps':snapshot['step'],
            'exposure':snapshot['exposure'],
            'checkpoint_sha256':snapshot['checkpoint_sha256'],
            'train_loss_latest':snapshot['train_loss_latest'],
            'supervised_wins_lambda_zero': row['arms']['supervised']['heldout_mse'] <
                sum(sorted([row['arms'][f'random_{i}']['heldout_mse'] for i in range(8)])[3:5])/2,
        })
        output.append(row)
        print(f'R{rounds} S{seed} step {snapshot["step"]} E{snapshot["exposure"]} J_sup={row["supervised_objective"]:.6f} J_rand={row["random_median_objective"]:.6f} win={row["supervised_wins"]} elapsed={time.monotonic()-start:.1f}s',flush=True)
    (Path('/mnt/data/nrf09_local')/f'nrf09_R{rounds}_S{seed}.json').write_text(json.dumps({
      'study_id':'NRF-09-matched-optimizer-updates-v1','rows':output,
      'protocol':'six fresh paired seeds R16/R32 at 16/32 optimizer updates; eval folds 7/8',
      'torch_version':torch.__version__,'python_version':sys.version
    },sort_keys=True,indent=2)+'\n')
