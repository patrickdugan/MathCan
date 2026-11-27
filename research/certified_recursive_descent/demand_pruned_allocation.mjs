// CRD-28: exact boundary and demand-pruned scalar allocation.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {canon16,align16} from "./persistent_symmetry.mjs";
import {EPS,clip,key,STOP,charges,setup,addWork} from "./metered_refinement.mjs";
import {Inc19,Two19,copyInc19,policy19} from "./incremental_refinement.mjs";
import {queries25} from "./packed_pareto_factors.mjs";
import {single26} from "./joint_scalar_allocation.mjs";
import {meter27,Scalar27,make27,last27} from "./linear_scalar_kernels.mjs";
const ev28=["boundaryCells","boundaryAdvances","demandShifts","demandCells","demandSkipped","demandMaskSlots","orderComparisons","kernelCalls28"];
function meter28(limit){const m=meter27(limit);Object.assign(m.c,Object.fromEntries(ev28.map(k=>[k,0])));return m}
const blank28=()=>meter28(0).c;
function boundary28(opts,b,M,mode){
 M.event("kernelCalls28");if(!opts.length)return 0;if(opts.length===1)return single26(opts,M);
 ok(b<=30,"bitset horizon");
 if(mode==="ordered"||mode==="demandOrdered"){
  opts=opts.map((os,i)=>({os,i})).sort((a,c)=>{M.take("lookup");M.event("orderComparisons");return a.os.length-c.os.length||a.i-c.i}).map(x=>x.os)
 }
 const n=opts.length,demand=mode.startsWith("demand");
 let masks=null;
 if(demand){
  M.take("nodeInit",n);M.event("demandMaskSlots",n);masks=new Uint32Array(n);masks[n-1]=(1<<b)>>>0;
  for(let i=n-1;i>=1;i--){
   let m=masks[i];
   for(let j=1;j<opts[i].length;j++){M.take("option");M.event("demandShifts");m|=masks[i]>>>opts[i][j].t}
   masks[i-1]=m>>>0;
  }
 }
 let dp=Array(b+1).fill(NaN),j=0;
 for(let r=0;r<=b;r++){
  M.take("rangeOutcome");M.event("boundaryCells");
  while(j+1<opts[0].length&&opts[0][j+1].t<=r){M.take("option");M.event("boundaryAdvances");j++}
  if(demand&&!(masks[0]&(1<<r))){M.event("demandSkipped");continue}
  dp[r]=1-opts[0][j].v;
 }
 for(let i=1;i<n;i++){
  const last=i===n-1,next=Array(b+1).fill(NaN);
  for(let r=last?b:0;r<=b;r++){
   if(demand){M.take("rangeOutcome");M.event("demandCells");if(!(masks[i]&(1<<r))){M.event("demandSkipped");continue}}
   let best=1;
   for(const o of opts[i]){if(o.t>r)break;M.take("allocation");ok(Number.isFinite(dp[r-o.t]),"demand closure");best=Math.min(best,(1-o.v)*dp[r-o.t])}
   if(last)return clip(1-best);
   next[r]=best
  }dp=next;
 }
 throw Error("missing target")
}
class Scalar28 extends Scalar27{
 constructor(P,M,mode,B){super(P,M,"last",B);this.mode28=mode}
 alloc(s,b){
  const M=this.M;M.event("factorQueries");M.take("lookup");const c=canon16(this.P,s,b);
  if(this.av.has(c.key))return this.av.get(c.key);
  const opts=[];
  for(const {i} of c.entries){
   const id=s[i],os=[{t:0,v:0}];M.take("option");
   if(id>=0){const l=this.P.local[i],v=l.at(id),m=l.L-v.stage,k=Math.min(3,b-m);
    if(k>0&&v.mass>0){const pair=k>=2&&m>0?this.pair26(i,id):null;let last=0;
     for(let j=1;j<=k;j++){M.take("option");const value=pair&&j<=2?pair[j]:this.val(i,id,m+j);if(value>last+1e-15){os.push({t:m+j,v:value});last=value}}
    }
   }
   if(os.length===1){M.event("identitySkips26");continue}opts.push(os)
  }
  const v=boundary28(opts,b,M,this.mode28);this.av.set(c.key,v);return v
 }
}
function make28(P,M,mode,B){return ["direct","scalar","last"].includes(mode)?make27(P,M,mode,B):new Scalar28(P,M,mode,B)}
class Inc28 extends Inc19{
 constructor(P,M,mode,B,retained){super(P,M,"incCheap",retained,false);this.factor28=make28(P,M,mode,B)}
 val(i,id,b){return this.factor28.val(i,id,b)}
 alloc(s,b){return this.factor28.alloc(s,b)}
 dl(s,b){return this.factor28.dl(s,b)}
}
class Two28 extends Two19{
 constructor(P,M,B){super(P,M,"prophet",null);this.factor28=make28(P,M,"boundary",B)}
 val(i,id,b){return this.factor28.val(i,id,b)}
 alloc(s,b){return this.factor28.alloc(s,b)}
 dl(s,b){return this.factor28.dl(s,b)}
}
function unit28(){
 const r=rng(3450001);let checks=0,maxError=0,skips=0;
 function test(raw,b){
  const den=10n**BigInt(raw.length);let best=den;
  function rec(i,c,f){if(i===raw.length){if(f<best)best=f;return}for(const a of raw[i])if(c+a.t<=b)rec(i+1,c+a.t,f*BigInt(10-a.num))}
  rec(0,0,1n);const truth=Number(den-best)/Number(den),os=raw.map(x=>x.filter(a=>a.t<=b).map(a=>({t:a.t,v:a.num/10}))).filter(x=>x.length>1);
  for(const k of ["boundary","demand","ordered","demandOrdered"]){
   const M=meter28(Infinity),v=boundary28(os,b,M,k),e=Math.abs(v-truth),d=last27(os,b,meter28(Infinity));
   ok(e<1e-12&&Math.abs(v-d)<1e-12,"integer/dense boundary reference");checks+=2;maxError=Math.max(maxError,e);skips+=M.c.demandSkipped
  }
 }
 for(let j=0;j<256;j++){
  const n=1+Math.floor(r()*7),b=1+Math.floor(r()*8),os=[];
  for(let i=0;i<n;i++){const m=Math.floor(r()*5),a=[{t:0,num:0}];let last=0;
   for(let k=1;k<=3&&m+k<=b;k++){const z=last+Math.floor(r()*(11-last));if(z>last){a.push({t:m+k,num:z});last=z}}
   os.push(a)
  }test(os,b)
 }
 test([],4);test([[{t:0,num:0},{t:2,num:5}]],3);test(Array.from({length:3},()=>[{t:0,num:0},{t:2,num:5}]),4);
 return {checks,maxError,skips}
}
function trace28(root,cap,B,auditAll){
 const P=new Problem(root,cap);setup(P);const qs=queries25(P,B).flatMap(g=>g.qs),R=new AllocationProblem(root,cap);setup(R);
 const truth=qs.map(q=>R.alloc(align16(P,q.s,R),q.b).v),modes=["direct","scalar","last","boundary","demand","ordered","demandOrdered"],rows=[];
 let allBudgetChecks=0,maxError=0;
 for(const mode of modes){
  const M=meter28(Infinity),G=make28(P,M,mode,B);let emax=0;
  for(let i=0;i<qs.length;i++){
   const q=qs[i],v=G.alloc(q.s,q.b),e=Math.abs(v-truth[i]);ok(e<1e-10,"trace disagreement "+JSON.stringify({mode,q,v,truth:truth[i],e}));emax=Math.max(emax,e)
  }
  if(G.store)ok(G.store.index.size<=G.store.slots,"trace cap");
  ok(M.used===sum(charges.map(k=>M.c[k])),"trace ledger");
  rows.push({kind:mode,queries:qs.length,work:M.used,typedBytes:G.bytes??null,stats:M.c,maxError:emax});maxError=Math.max(maxError,emax);
  if(auditAll){
   const A=make28(P,meter28(Infinity),mode,B);
   for(const q of qs){const s=align16(P,q.s,R);for(let b=0;b<=q.b;b++){const e=Math.abs(A.alloc(q.s,b)-R.alloc(s,b).v);ok(e<1e-10,"all budget");allBudgetChecks++;maxError=Math.max(maxError,e)}}
  }
 }
 const changed=[0,0,0];for(const q of qs)changed[q.changed]++;
 return {queries:qs.length,distinct:new Set(qs.map(q=>key(q.s,q.b))).size,changed,valueChecks:qs.length*modes.length,allBudgetChecks,maxError,rows}
}
function policy28(root,cap,B,total,mode,oracle){
 const P=new Problem(root,cap),pre=setup(P),inc=mode!=="boundary2",audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakSlots:0,peakNodes:0,peakEdges:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank28(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0],M=meter28(Math.min(left,Math.ceil(2*left/b))),G=inc?new Inc28(P,M,mode,B,retained):new Two28(P,M,B),r=G.solve(s,b,fallback);
  if(!r.ranges&&inc&&M.c.fallback===0)M.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakSlots=Math.max(audit.peakSlots,M.c.storePeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,G.peakEdges);
  ok(G.factor28.store.index.size<=G.factor28.store.slots,"store cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){if(o.hit){v+=o.p;continue}
   const C=meter28(left-M.used);let keep=null;
   if(inc&&r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyInc19(o.n,C);
   addWork(work,C.c,o.p);const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep);
   v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p)
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work}
 }
 const r=rec(P.initial(),B,total,null),regret=oracle.rec(oracle.P.initial(),B).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre}
}
function cohort28(name){
 if(name==="standard")return {n:20,seed:3420001,pop:3,stages:3,b:6};
 if(name==="population")return {n:16,seed:3430001,pop:5,stages:2,b:6};
 return {n:12,seed:3440001,pop:7,stages:2,b:5}
}
function experiment28(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort28(name),cap=2,traceModes=["direct","scalar","last","boundary","demand","ordered","demandOrdered"],modes=["incCheap","metered2","scalar","last","boundary","demand","ordered","demandOrdered","boundary2"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),refs={optimal:[],receding2:[]},traces=[];
 const audit={unit:unit28(),queries:0,distinct:0,changed:[0,0,0],valueChecks:0,allBudgetChecks:0,maxError:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),t=trace28(root,cap,b,i<2);traces.push(t);
  for(const k of ["queries","distinct","valueChecks","allBudgetChecks"])audit[k]+=t[k];for(let j=0;j<3;j++)audit.changed[j]+=t.changed[j];audit.maxError=Math.max(audit.maxError,t.maxError);
  const P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);refs.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);refs.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  for(const t of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,t,mode,oracle,false):policy28(root,cap,b,t,mode,oracle);
   r.work={...blank28(),...r.work};all[mode+t].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,traceRows=[],tracePairs=[],rows=[],paired=[];
 for(const mode of traceModes){
  const a=traces.map(t=>t.rows.find(r=>r.kind===mode)),stats=Object.fromEntries(Object.keys(blank28()).map(k=>[k,k==="storePeak"?Math.max(...a.map(x=>x.stats[k])):sum(a.map(x=>x.stats[k]))]));
  traceRows.push({kind:mode,roots:n,queries:audit.queries,totalWork:sum(a.map(x=>x.work)),typedBytes:a[0].typedBytes,stats,maxError:Math.max(...a.map(x=>x.maxError))})
 }
 for(const [k,r] of [["boundary","last"],["demand","boundary"],["ordered","boundary"],["demandOrdered","demand"],["boundary","scalar"],["boundary","direct"]]){
  const d=traces.map(t=>t.rows.find(x=>x.kind===k).work-t.rows.find(x=>x.kind===r).work);tracePairs.push({kind:k,ref:r,...bootstrap(d,(0xC0281000+seed+traceModes.indexOf(k)*20+traceModes.indexOf(r))>>>0)})
 }
 for(const total of limits)for(const mode of modes){
  const k=mode+total,a=all[k],work=Object.fromEntries(Object.keys(blank28()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:64*(b+1)*8,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakSlots:max("peakSlots"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}})
 }
 for(const t of limits)for(const [k,r] of [["boundary","last"],["demand","boundary"],["ordered","boundary"],["demandOrdered","demand"],["boundary","scalar"],["boundary","incCheap"],["boundary2","metered2"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0280000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)})
 }
 return {status:"PASS",scope:"finite synthetic independent model, exact scalar kernels and declared work proxy",name,roots:n,population:pop,budget:b,cap,audit,baselines:{optimal:mean(refs.optimal),receding2:mean(refs.receding2)},traceRows,tracePairs,rows,paired,elapsedMs:Date.now()-start}
}

const name28=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
console.log(JSON.stringify(experiment28(name28),null,2));
