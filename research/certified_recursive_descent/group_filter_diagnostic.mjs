// CRD-07 post-hoc, frozen-checkpoint diagnostic. Node >=18.
// Run from any directory: node group_filter_diagnostic.mjs
import {readFileSync} from "node:fs";
import {rng} from "./search.mjs";
import {ok} from "./learned_frontier.mjs";
import {K0,K1,sum,ft,mix,kernels,prep07,predict07,root07,terminal07} from "./group_filter.mjs";

function opnorm2(x){
 const f=sum(x.map(v=>v*v)),det=x[0]*x[3]-x[1]*x[2];
 return Math.sqrt((f+Math.sqrt(Math.max(0,f*f-4*det*det)))/2);
}
function blockErrorBound(obs,learned){
 const pairs=obs.map(([y,c])=>[ft(mix([K0,K1],c)),ft(mix(learned,c))]);
 const stats=pairs.map(([a,b])=>({rs:Math.max(Math.abs(a[0]),Math.abs(b[0])),ds:Math.abs(a[0]-b[0]),rm:Math.max(opnorm2(a.slice(1)),opnorm2(b.slice(1))),dm:opnorm2(a.slice(1).map((v,i)=>v-b[i+1]))}));
 let Bs=0,Bm=0;
 for(let i=0;i<stats.length;i++){let ps=stats[i].ds,pm=stats[i].dm;for(let j=0;j<stats.length;j++)if(j!==i){ps*=stats[j].rs;pm*=stats[j].rm}Bs+=ps;Bm+=pm}
 return (Bs+4*Bm)/6;
}
function diag07(receipt){
 const choices=receipt.training.choices,learned=kernels(choices.learned.weights),kinds=["fourier","learned","hard","rnn","window","full","uniform","last"],out={};
 for(const regime of ["in","shift"]){
  const used=new Set(),roots=Array.from({length:192},(_,i)=>root07(1370001+i,regime,used)),tables=Object.fromEntries(kinds.map(k=>[k,prep07(k,choices[k]?.weights??null)]));
  let errorSum=0,maxError=0,boundSum=0,maxBound=0,branchChecks=0,rootEpsSum=0;
  const rows={},boundChecks={1:0,4:0},maxRegret={1:0,4:0};
  for(const root of roots){
   const exact=root.branches.map(b=>predict07("fourier",null,b.obs,tables.fourier));
   const approx=root.branches.map(b=>predict07("learned",choices.learned.weights,b.obs,tables.learned));
   const p=exact.map(x=>x[root.target]),q=approx.map(x=>x[root.target]),epsilon=Math.max(...p.map((v,i)=>Math.abs(v-q[i])));
   rootEpsSum+=epsilon;
   for(let i=0;i<16;i++){
    const err=Math.max(...exact[i].map((v,j)=>Math.abs(v-approx[i][j]))),b=blockErrorBound(root.branches[i].obs,learned);
    ok(err<=b+1e-12,"operator telescoping bound");
    errorSum+=err;boundSum+=b;maxError=Math.max(maxError,err);maxBound=Math.max(maxBound,b);branchChecks++;
   }
   const order=scores=>scores.map((v,index)=>({v,index})).sort((a,b)=>b.v-a.v||b.index-a.index).map(x=>x.index);
   const val=ids=>1-ids.reduce((v,i)=>v*(1-p[i]),1);
   const exactRank=order(p.map(v=>Math.round(v*1e12)/1e12));
   for(const view of ["true","scrambled"])for(const kind of kinds){
    const score=root.branches.map((b,i)=>{
     if(kind==="uniform")return rng((root.seed^Math.imul(i+1,0x9E3779B9))>>>0)();
     const obs=view==="true"?b.obs:b.scrambled,w=choices[kind]?.weights??null;
     const v=view==="true"&&kind==="fourier"?p[i]:view==="true"&&kind==="learned"?q[i]:predict07(kind,w,obs,tables[kind])[root.target];
     return Math.round(v*1e12)/1e12;
    });
    const rank=order(score);
    for(const k of [1,4]){
     const ids=rank.slice(0,k),v=val(ids),optimal=val(exactRank.slice(0,k)),regret=optimal-v,hit=ids.some(i=>terminal07(root.branches[i],root.target));
     const key=view+":"+kind+":"+k,o=rows[key]??={view,kind,probes:k,expectedSuccessSum:0,regretSum:0,observed:0};
     ok(regret>=-1e-10,"exact top-k optimality");
     o.expectedSuccessSum+=v;o.regretSum+=regret;o.observed+=Number(hit);
     if(kind==="learned"&&view==="true"){
      ok(regret<=2*k*epsilon+1e-10,"top-k regret bound");boundChecks[k]++;maxRegret[k]=Math.max(maxRegret[k],regret);
     }
    }
   }
  }
  const values=Object.values(rows).map(r=>{
   const original=receipt.search[regime].rows.find(x=>x.view===r.view&&x.kind===r.kind&&x.probes===r.probes);
   ok(original.solved===r.observed,"post-hoc observed replay");
   return {view:r.view,kind:r.kind,probes:r.probes,observed:r.observed,expectedSuccess:r.expectedSuccessSum/roots.length,meanRegret:r.regretSum/roots.length};
  });
  out[regime]={roots:roots.length,branchChecks,meanBranchMaxError:errorSum/branchChecks,maxError,meanBound:boundSum/branchChecks,maxBound,meanRootEpsilon:rootEpsSum/roots.length,boundChecks,maxRegret,values};
 }
 return out;
}
const receipt=JSON.parse(readFileSync(new URL("./group_filter_receipt.json",import.meta.url),"utf8"));
console.log(JSON.stringify({scope:"post-hoc frozen test diagnostic; conditional expectation under known synthetic law, no tuning",...diag07(receipt)},null,2));
