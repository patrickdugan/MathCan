import {pathToFileURL} from "node:url";
// CRD-26: exact scalar joint likelihoods and affordability-aware allocation.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {desc16,canon16,align16} from "./persistent_symmetry.mjs";
import {EPS,clip,key,STOP,charges,setup,Planner,addWork} from "./metered_refinement.mjs";
import {Inc19,Two19,copyInc19,policy19} from "./incremental_refinement.mjs";
import {meter24,Factor24} from "./shared_allocation_factors.mjs";
import {queries25} from "./packed_pareto_factors.mjs";

const ev26=["jointSweeps26","jointWords26","jointOutputs26","jointValues26","singleSweeps26","eagerRequests26","identitySkips26","singleCases26","twoEligible26","pairCases26","pairRejected26","pairChecks26","pairProducts26","singleChecks26","foldCases26","zeroCases26","estimateWork26"];
function meter26(limit){const m=meter24(limit);Object.assign(m.c,Object.fromEntries(ev26.map(k=>[k,0])));return m}
const blank26=()=>meter26(0).c;
function fold26(opts,b,M){
 M.event("foldCases26");let dp=Array(b+1).fill(1);
 for(const os of opts){
  const next=[];
  for(let r=0;r<=b;r++){
   let best=1;
   for(const o of os){if(o.t>r)break;M.take("allocation");best=Math.min(best,(1-o.v)*dp[r-o.t])}
   next.push(best)
  }dp=next;
 }
 return clip(1-dp[b]);
}
function single26(opts,M){
 let best=0;for(const os of opts){M.take("allocation");M.event("singleChecks26");best=Math.max(best,os.at(-1).v)}
 return best;
}
function allocation26(opts,b,M,kind){
 // Inputs have zero and strictly improving positive options, costs ascending.
 if(!opts.length){M.event("zeroCases26");return 0}
 if(opts.length===1){M.event("singleCases26");return single26(opts,M)}
 if(kind==="short"||kind==="both"){
  const before=M.used,mins=[];
  for(const os of opts){M.take("option");mins.push(os[1].t)}
  mins.sort((a,c)=>{M.take("lookup");return a-c});
  M.event("estimateWork26",M.used-before);
  if(mins[0]+mins[1]>b){M.event("singleCases26");return single26(opts,M)}
  if(mins.length<3||mins[0]+mins[1]+mins[2]>b){
   M.event("twoEligible26");const begin=M.used;
   let foldCost=0,pairCost=opts.length;
   for(let i=0;i<opts.length;i++){
    for(const o of opts[i]){M.take("option");foldCost+=b-o.t+1}
    for(let j=0;j<i;j++){M.take("option");pairCost+=1+2*(opts[i].length-1)*(opts[j].length-1)}
   }
   M.event("estimateWork26",M.used-begin);
   if(pairCost<=foldCost){
    M.event("pairCases26");
    let fail=1-single26(opts,M);
    for(let i=0;i<opts.length;i++)for(let j=0;j<i;j++){
     M.take("option");
     for(let u=1;u<opts[i].length;u++)for(let v=1;v<opts[j].length;v++){
      M.take("rangeOutcome");M.event("pairChecks26");const a=opts[i][u],c=opts[j][v];
      if(a.t+c.t>b)continue;
      M.take("allocation");M.event("pairProducts26");fail=Math.min(fail,(1-a.v)*(1-c.v));
     }
    }return clip(1-fail)
   }
   M.event("pairRejected26");
  }
 }
 return fold26(opts,b,M);
}
const pred26=(j,x)=>j===0?x%2:j===1?Number(x<3):Number(x%3===0);
class Scalar26 extends Factor24{
 constructor(P,M,kind,B){super(P,M,"scalar",B);this.kind26=kind;this.joint26=["joint","eagerJoint","both"].includes(kind);this.skip26=["skip","short","both"].includes(kind)}
 // Only called for k=1 and k=2, with positive remaining sensor count.
 pair26(i,id){
  const M=this.M,l=this.P.local[i],s=l.at(id),m=l.L-s.stage,d=desc16(this.P,i,id),vals=[0,0,0],missing=[];
  ok(m>0&&m+2<=this.B,"joint local domain");
  for(let k=1;k<=2;k++){
   const key=d+":"+(m+k);M.take("lookup");
   if(this.lv.has(key))vals[k]=this.lv.get(key);else missing.push(k);
  }
  if(!missing.length)return vals;
  M.take("localMiss",missing.length);
  if(missing.length===2){M.event("jointSweeps26");M.event("jointValues26",2)}else M.event("singleSweeps26");
  for(let u=0;u<2**m;u++){
   M.take("likelihood",3*m);if(missing.length===2)M.event("jointWords26");
   const w=s.p.slice(0,3);
   for(let t=0;t<m;t++){
    const j=s.stage+t,a=l.spec.sensors[j]/100,bit=(u>>t)&1;
    for(let x=0;x<3;x++)w[x]*=pred26(j,x)===bit?a:1-a
   }
   w.sort((a,b)=>b-a);
   for(const k of missing){
    if(missing.length===2){M.take("rangeOutcome");M.event("jointOutputs26")}
    vals[k]+=k===1?w[0]:w[0]+w[1];
   }
  }
  // Each individual scalar value is complete; an abort between writes
  // can leave one valid cached value without the other.
  for(const k of missing)this.lv.set(d+":"+(m+k),vals[k]);
  return vals;
 }
 val(i,id,b){
  if(this.kind26==="eagerJoint"&&id>=0&&b>0){
   const l=this.P.local[i],m=l.L-l.at(id).stage,k=b-m;
   if(m>0&&m+2<=this.B&&(k===1||k===2)){
    this.M.event("eagerRequests26");return this.pair26(i,id)[k];
   }
  }
  return super.val(i,id,b);
 }
 alloc(s,b){
  const M=this.M;M.event("factorQueries");M.take("lookup");const c=canon16(this.P,s,b);
  if(this.av.has(c.key))return this.av.get(c.key);
  const opts=[];
  for(const {i} of c.entries){
   const id=s[i],os=[{t:0,v:0}];M.take("option");
   if(id>=0){
    const l=this.P.local[i],v=l.at(id),m=l.L-v.stage,k=Math.min(3,b-m);
    let pair=null,last=0;
    if(k>0&&(!this.skip26||v.mass>0)){
     // Joint only when both values are requested by this allocation.
     // Eager additionally precomputes the pair for one-value requests.
     if(this.joint26&&k>=2&&m>0)pair=this.pair26(i,id);
     for(let j=1;j<=k;j++){
      M.take("option");const value=pair&&j<=2?pair[j]:this.val(i,id,m+j);
      if(value>last+1e-15){os.push({t:m+j,v:value});last=value}
     }
    }
   }
   if(this.skip26&&os.length===1){M.event("identitySkips26");continue}
   opts.push(os);
  }
  const v=this.skip26?allocation26(opts,b,M,this.kind26):fold26(opts,b,M);
  this.av.set(c.key,v);return v;
 }
}
function make26(P,M,mode,B){
 return mode==="direct"?new Planner(P,M,"prophet",null):mode==="scalar"?new Factor24(P,M,"scalar",B):new Scalar26(P,M,mode,B);
}
class Inc26 extends Inc19{
 constructor(P,M,mode,B,retained){super(P,M,"incCheap",retained,false);this.factor26=make26(P,M,mode,B)}
 val(i,id,b){return this.factor26.val(i,id,b)}
 alloc(s,b){return this.factor26.alloc(s,b)}
 dl(s,b){return this.factor26.dl(s,b)}
}
class Two26 extends Two19{
 constructor(P,M,B){super(P,M,"prophet",null);this.factor26=make26(P,M,"both",B)}
 val(i,id,b){return this.factor26.val(i,id,b)}
 alloc(s,b){return this.factor26.alloc(s,b)}
 dl(s,b){return this.factor26.dl(s,b)}
}
function unit26(){
 const r=rng(3250001),M=meter26(Infinity);let checks=0,maxError=0;
 function test(os,b){
  const n=os.length,den=10n**BigInt(n);let best=den;
  function rec(i,c,f){
   if(i===n){if(f<best)best=f;return}
   for(const a of os[i])if(c+a.t<=b)rec(i+1,c+a.t,f*BigInt(10-a.num));
  }rec(0,0,1n);
  const ref=Number(den-best)/Number(den),o=os.map(x=>x.filter(a=>a.t<=b).map(a=>({t:a.t,v:a.num/10}))).filter(x=>x.length>1);
  for(const mode of ["skip","short","both"]){
   const v=allocation26(o,b,M,mode),e=Math.abs(v-ref);ok(e<1e-12,"integer shortcut");
   checks++;maxError=Math.max(maxError,e)
  }
 }
 for(let j=0;j<256;j++){
  const n=1+Math.floor(r()*7),b=1+Math.floor(r()*8),os=[];
  for(let i=0;i<n;i++){
   const m=Math.floor(r()*5),a=[{t:0,num:0}];let last=0;
   for(let k=1;k<=3&&m+k<=b;k++){const z=last+Math.floor(r()*(11-last));if(z>last){a.push({t:m+k,num:z});last=z}}
   os.push(a)
  }test(os,b)
 }
 // Exact threshold: three cost-two branches; at b=5 at most two,
 // at b=6 all three can be used. Empty/identity and single cases.
 const three=Array.from({length:3},()=>[{t:0,num:0},{t:2,num:5}]);
 for(const b of [1,2,3,4,5,6])test(three,b);
 test([],4);test([[{t:0,num:0}]],4);test([[{t:0,num:0},{t:2,num:7}]],3);
 return {checks,maxError,zero:M.c.zeroCases26,single:M.c.singleCases26,twoEligible:M.c.twoEligible26,pair:M.c.pairCases26,rejected:M.c.pairRejected26,fold:M.c.foldCases26}
}
function trace26(root,cap,B,auditAll){
 const P=new Problem(root,cap);setup(P);const qs=queries25(P,B).flatMap(g=>g.qs),R=new AllocationProblem(root,cap);setup(R);
 const truth=qs.map(q=>R.alloc(align16(P,q.s,R),q.b).v);
 const modes=["direct","scalar","joint","eagerJoint","skip","short","both"],rows=[];
 let allBudgetChecks=0,localChecks=0,maxError=0;
 for(const mode of modes){
  const M=meter26(Infinity),G=make26(P,M,mode,B);let emax=0;
  for(let i=0;i<qs.length;i++){
   const q=qs[i],v=G.alloc(q.s,q.b),e=Math.abs(v-truth[i]);ok(e<1e-10,"trace scalar disagreement "+JSON.stringify({mode,q,v,truth:truth[i],e}));emax=Math.max(emax,e)
  }
  if(G.store)ok(G.store.index.size<=G.store.slots,"trace cache cap");
  ok(M.used===sum(charges.map(k=>M.c[k])),"trace ledger");
  rows.push({kind:mode,queries:qs.length,work:M.used,typedBytes:G.bytes??null,stats:M.c,maxError:emax});maxError=Math.max(maxError,emax);
  if(auditAll){
   // Separate cache and meter: do not warm or charge the measured trace.
   const A=make26(P,meter26(Infinity),mode,B);
   for(const q of qs){
    const s=align16(P,q.s,R);
    for(let b=0;b<=q.b;b++){
     const e=Math.abs(A.alloc(q.s,b)-R.alloc(s,b).v);ok(e<1e-10,"all-budget audit");allBudgetChecks++;maxError=Math.max(maxError,e)
    }
   }
   for(let i=0;i<P.local.length;i++){
    const l=P.local[i];
    for(let id=0;id<l.states.length;id++)for(let b=0;b<=B;b++){
     const e=Math.abs(A.val(i,id,b)-l.value(id,b));ok(e<1e-10,"local native DP audit");localChecks++;maxError=Math.max(maxError,e)
    }
   }
  }
 }
 const changed=[0,0,0];for(const q of qs)changed[q.changed]++;
 return {queries:qs.length,distinct:new Set(qs.map(q=>key(q.s,q.b))).size,changed,valueChecks:qs.length*modes.length,allBudgetChecks,localChecks,maxError,rows};
}
function policy26(root,cap,B,total,mode,oracle){
 const P=new Problem(root,cap),pre=setup(P),inc=mode!=="both2",audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakSlots:0,peakNodes:0,peakEdges:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank26(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0],M=meter26(Math.min(left,Math.ceil(2*left/b))),G=inc?new Inc26(P,M,mode,B,retained):new Two26(P,M,B),r=G.solve(s,b,fallback);
  if(!r.ranges&&inc&&M.c.fallback===0)M.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakSlots=Math.max(audit.peakSlots,M.c.storePeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,G.peakEdges);
  ok(G.factor26.store.index.size<=G.factor26.store.slots,"scalar cache cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){if(o.hit){v+=o.p;continue}
   const C=meter26(left-M.used);let keep=null;
   if(inc&&r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyInc19(o.n,C);
   addWork(work,C.c,o.p);
   const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p)
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),B,total,null),regret=oracle.rec(oracle.P.initial(),B).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre}
}
function cohort26(name){
 if(name==="standard")return {n:24,seed:3220001,pop:3,stages:3,b:6};
 if(name==="population")return {n:20,seed:3230001,pop:5,stages:2,b:6};
 return {n:12,seed:3240001,pop:7,stages:2,b:5};
}
function experiment26(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort26(name),cap=2,traceModes=["direct","scalar","joint","eagerJoint","skip","short","both"],modes=["incCheap","metered2",...traceModes.slice(1),"both2"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),refs={optimal:[],receding2:[]},traces=[];
 const audit={unit:unit26(),queries:0,distinct:0,changed:[0,0,0],valueChecks:0,allBudgetChecks:0,localChecks:0,maxError:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),t=trace26(root,cap,b,i<2);traces.push(t);
  for(const k of ["queries","distinct","valueChecks","allBudgetChecks","localChecks"])audit[k]+=t[k];for(let j=0;j<3;j++)audit.changed[j]+=t.changed[j];audit.maxError=Math.max(audit.maxError,t.maxError);
  const P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);refs.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);refs.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  for(const t of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,t,mode,oracle,false):policy26(root,cap,b,t,mode,oracle);
   r.work={...blank26(),...r.work};all[mode+t].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,traceRows=[],tracePairs=[],rows=[],paired=[];
 for(const mode of traceModes){
  const a=traces.map(t=>t.rows.find(r=>r.kind===mode)),stats=Object.fromEntries(Object.keys(blank26()).map(k=>[k,k==="storePeak"?Math.max(...a.map(x=>x.stats[k])):sum(a.map(x=>x.stats[k]))]));
  traceRows.push({kind:mode,roots:n,queries:audit.queries,totalWork:sum(a.map(x=>x.work)),typedBytes:a[0].typedBytes,stats,maxError:Math.max(...a.map(x=>x.maxError))})
 }
 const traceComparisons=[["both","scalar"],["joint","scalar"],["eagerJoint","joint"],["skip","scalar"],["short","skip"],["both","joint"],["both","short"],["both","direct"]];
 for(const [k,r] of traceComparisons){
  const d=traces.map(t=>t.rows.find(x=>x.kind===k).work-t.rows.find(x=>x.kind===r).work);tracePairs.push({kind:k,ref:r,...bootstrap(d,(0xC0261000+seed+traceModes.indexOf(k)*20+traceModes.indexOf(r))>>>0)})
 }
 for(const total of limits)for(const mode of modes){
  const k=mode+total,a=all[k],work=Object.fromEntries(Object.keys(blank26()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:64*(b+1)*8,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakSlots:max("peakSlots"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}})
 }
 for(const t of limits)for(const [k,r] of [["both","scalar"],["both","incCheap"],["both","joint"],["joint","scalar"],["eagerJoint","joint"],["skip","scalar"],["short","skip"],["both","short"],["both2","metered2"],["scalar","incCheap"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0260000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)})
 }
 return {status:"PASS",scope:"finite synthetic independent-branch model; exact static arithmetic and metered policy proxy",name,roots:n,population:pop,budget:b,cap,audit,baselines:{optimal:mean(refs.optimal),receding2:mean(refs.receding2)},traceRows,tracePairs,rows,paired,elapsedMs:Date.now()-start}
}
export {meter26,blank26,Scalar26,fold26,single26,make26,policy26,experiment26};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const name26=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
 console.log(JSON.stringify(experiment26(name26),null,2));
}
