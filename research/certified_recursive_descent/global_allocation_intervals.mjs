// CRD-14B: BigInt static allocation intervals using frozen CRD-13 engines.
import {ok,sum,compile,rawBits,bounded} from "./grouped_likelihoods.mjs";
import {fixtureC,solveOverlap} from "./likelihood_overlap_stress.mjs";
const budgets=[0,32,128,512],caps=[46,78];
const ratio=(n,d)=>Number(n)/Number(d);
function localOptions(root){
 const C=compile(root.sensors),w=root.prior.slice(0,3),den=sum(root.prior)*C.den[0];
 const options={original:[],combined:[]};let exactChecks=0;
 for(const k of [1,2]){
  let truth=null;
  if(root.m===12){
   const raw=rawBits(root.sensors,root.prior,k);
   ok((raw.numerator*den)%raw.denominator===0n,"reference denominator");
   truth=raw.numerator*den/raw.denominator;exactChecks++;
  }
  const a=bounded(C,w,k,den,truth),b=solveOverlap(C,w,k,den,truth);
  for(const [name,rows] of [["original",a],["combined",b]]){
   let lastL=0n,lastU=den;
   const entries=rows.map((r,i)=>{
    const L=BigInt(r.lower),U=BigInt(r.upper);
    ok(r.budget===budgets[i]&&BigInt(r.denominator)===den,"local interval domain");
    ok(lastL<=L&&L<=U&&U<=lastU,"nested local interval");lastL=L;lastU=U;
    if(truth!==null)ok(L<=truth&&truth<=U,"depth12 exact containment");
    return {L,U,visited:r.visited,expanded:r.expanded,peakHeap:r.peakHeap};
   });
   options[name].push({k,cost:root.m+k,entries});
  }
 }
 const mass=sum(w)*C.den[0];
 for(const name of ["original","combined"]){
  const exact=(k,cost,v)=>({k,cost,entries:budgets.map(()=>({L:v,U:v,visited:0,expanded:0,peakHeap:0}))});
  options[name]=[exact(0,0,0n),...options[name],exact(3,root.m+3,mass)];
 }
 return {depth:root.m,seed:root.seed,den,options,exactChecks};
}
// Since every choice for branch i shares denominator D_i, static objective
// maximization is integer minimization of failure numerator products.
function allocDP(branches,engine,index,B,side){
 const n=branches.length,dp=Array.from({length:n+1},()=>Array(B+1).fill(null));let combos=0,cells=0;
 for(let r=0;r<=B;r++)dp[n][r]={failure:1n,plan:[]};
 for(let i=n-1;i>=0;i--)for(let r=0;r<=B;r++){
  cells++;let best=null;
  for(const o of branches[i].options[engine]){
   if(o.cost>r)continue;
   const tail=dp[i+1][r-o.cost],v=o.entries[index][side],failure=(branches[i].den-v)*tail.failure;
   combos++;
   if(!best||failure<best.failure)best={failure,plan:[o.k,...tail.plan]};
  }
  dp[i][r]=best;
 }
 return {...dp[0][B],combos,cells};
}
function enumerate(branches,engine,index,B){
 const all=[];
 function rec(i,spent,Lfailure,Ufailure,plan){
  if(i===branches.length){all.push({spent,Lfailure,Ufailure,plan});return}
  const d=branches[i].den;
  for(const o of branches[i].options[engine]){
   if(spent+o.cost>B)continue;
   const {L,U}=o.entries[index];
   rec(i+1,spent+o.cost,Lfailure*(d-L),Ufailure*(d-U),[...plan,o.k]);
  }
 }
 rec(0,0,1n,1n,[]);return all;
}
function evaluateAllocation(branches,engine,index,B){
 const den=branches.reduce((x,b)=>x*b.den,1n),l=allocDP(branches,engine,index,B,"L"),u=allocDP(branches,engine,index,B,"U"),all=enumerate(branches,engine,index,B);
 const lower=den-l.failure,upper=den-u.failure,selected=all.find(x=>x.plan.join(",")===l.plan.join(","));
 ok(selected&&lower===den-selected.Lfailure,"selected lower");
 ok(all.every(x=>x.Lfailure>=l.failure&&x.Ufailure>=u.failure),"exhaustive allocation comparison");
 const alternative=all.filter(x=>x.plan.join(",")!==l.plan.join(","));
 const altUpper=alternative.reduce((m,x)=>den-x.Ufailure>m?den-x.Ufailure:m,0n);
 const selectedUpper=den-selected.Ufailure;
 const regret=upper-lower,alternativeRegret=altUpper>lower?altUpper-lower:0n;
 ok(0n<=lower&&lower<=selectedUpper&&selectedUpper<=upper&&upper<=den,"static objective interval");
 const sameAttainsBoth=selectedUpper===upper,unique=lower>altUpper;
 if(unique)ok(sameAttainsBoth,"uniqueness implies common maximizer");
 const record={budget:B,expansions:budgets[index],engine,lower:lower.toString(),upper:upper.toString(),denominator:den.toString(),selectedUpper:selectedUpper.toString(),alternativeUpper:altUpper.toString(),regretBound:regret.toString(),alternativeRegretBound:alternativeRegret.toString(),guaranteedSuccess:ratio(lower,den),optimisticSuccess:ratio(upper,den),width:ratio(regret,den),alternativeWidth:ratio(alternativeRegret,den),lowerPlan:l.plan,upperPlan:u.plan,sameAttainsBoth,unique,certifiedOptimal:lower>=altUpper,combinations:l.combos+u.combos,cells:l.cells+u.cells,feasibleAllocations:all.length,unavailableDepths:branches.filter(b=>b.depth+1>B).map(b=>b.depth)};
 ok(record.guaranteedSuccess>=0&&record.optimisticSuccess<=1+1e-12,"decimal display");
 return record;
}
function deep14(){
 const start=Date.now(),rows=[],seeds=new Set();let exactChecks=0,dpChecks=0;
 for(const [ri,regime] of ["weak","moderate","high"].entries())for(let i=0;i<12;i++){
  const seed=2050001+12*ri+i,depths=[12,32,64].map((_,j)=>[12,32,64][(i+j)%3]);
  const branches=depths.map((m,j)=>{
   const localSeed=seed*4+j;ok(!seeds.has(localSeed),"branch seed collision");seeds.add(localSeed);
   const z=localOptions(fixtureC(regime,localSeed,m));exactChecks+=z.exactChecks;return z;
  });
  const localWork={};
  for(const engine of ["original","combined"])localWork[engine]=budgets.map((budget,k)=>{
   const entries=branches.flatMap(b=>b.options[engine].filter(o=>o.k===1||o.k===2).map(o=>o.entries[k]));
   return {budget,visited:entries.reduce((a,x)=>a+x.visited,0),expanded:entries.reduce((a,x)=>a+x.expanded,0),peakHeap:Math.max(...entries.map(x=>x.peakHeap))};
  });
  const results=[];
  for(const B of caps)for(const engine of ["original","combined"]){
   let lastL=0n,lastU=branches.reduce((a,b)=>a*b.den,1n);
   for(let index=0;index<budgets.length;index++){
    const r=evaluateAllocation(branches,engine,index,B),L=BigInt(r.lower),U=BigInt(r.upper);
    ok(lastL<=L&&L<=U&&U<=lastU,"nested static optimum");lastL=L;lastU=U;results.push(r);dpChecks++;
   }
  }
  rows.push({regime,seed,depths,localSeeds:branches.map(b=>b.seed),localWork,results});
 }
 const summary=[];
 for(const regime of ["weak","moderate","high"])for(const B of caps)for(const e of budgets){
  const rs=rows.filter(r=>r.regime===regime),mean=a=>a.reduce((s,x)=>s+x,0)/a.length;
  const engines={};
  for(const engine of ["original","combined"]){
   const a=rs.map(r=>r.results.find(x=>x.engine===engine&&x.budget===B&&x.expansions===e));
   engines[engine]={meanLower:mean(a.map(x=>x.guaranteedSuccess)),meanUpper:mean(a.map(x=>x.optimisticSuccess)),meanWidth:mean(a.map(x=>x.width)),meanAlternativeWidth:mean(a.map(x=>x.alternativeWidth)),maxWidth:Math.max(...a.map(x=>x.width)),unique:a.filter(x=>x.unique).length,certifiedOptimal:a.filter(x=>x.certifiedOptimal).length,sameAttainsBoth:a.filter(x=>x.sameAttainsBoth).length,meanCombinations:mean(a.map(x=>x.combinations)),meanFeasibleAllocations:mean(a.map(x=>x.feasibleAllocations))};
  }
  summary.push({regime,budget:B,expansions:e,roots:rs.length,...engines});
 }
 return {status:"PASS",scope:"independent static allocation only; bounds are not adaptive upper bounds",roots:rows.length,branchFixtures:seeds.size,exactDepth12Checks:exactChecks,allocationDPChecks:dpChecks,summary,rows,elapsedMs:Date.now()-start};
}
console.log(JSON.stringify(deep14(),null,2));
