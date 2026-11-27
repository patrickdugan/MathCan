// CRD-27: scalar fusion, terminal fold, linear gate, distinct-branch table.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {canon16,align16} from "./persistent_symmetry.mjs";
import {EPS,clip,key,STOP,charges,setup,addWork} from "./metered_refinement.mjs";
import {Inc19,Two19,copyInc19,policy19} from "./incremental_refinement.mjs";
import {queries25} from "./packed_pareto_factors.mjs";
import {meter26,Scalar26,fold26,single26,make26,policy26} from "./joint_scalar_allocation.mjs";

const ev27=["terminalFolds","terminalCandidates","gateCalls27","gateUnits27","gatePairBound","gateTableBound","gateFoldBound","gateRejected27","gateSingle27","gateTwo27","pairRuns27","tableRuns27","tableCells27","tableAdvances27","tableProducts27","tableExclusions27","kernelActual27","kernelBound27"];
function meter27(limit){const m=meter26(limit);Object.assign(m.c,Object.fromEntries(ev27.map(k=>[k,0])));return m}
const blank27=()=>meter27(0).c;
function last27(opts,b,M){
 M.event("terminalFolds");let dp=Array(b+1).fill(1);
 for(let i=0;i<opts.length;i++){
  const os=opts[i],last=i===opts.length-1;
  const next=[];
  for(let r=last?b:0;r<=b;r++){
   let best=1;
   for(const o of os){if(o.t>r)break;M.take("allocation");if(last)M.event("terminalCandidates");best=Math.min(best,(1-o.v)*dp[r-o.t])}
   if(last)return clip(1-best);
   next.push(best)
  }dp=next;
 }
 return 0;
}
function pair27(opts,b,M){
 M.event("pairRuns27");let f=1-single26(opts,M);
 for(let i=0;i<opts.length;i++)for(let j=0;j<i;j++){
  M.take("option");
  for(let u=1;u<opts[i].length;u++)for(let v=1;v<opts[j].length;v++){
   M.take("rangeOutcome");M.event("pairChecks26");const a=opts[i][u],c=opts[j][v];
   if(a.t+c.t>b)continue;
   M.take("allocation");M.event("pairProducts26");f=Math.min(f,(1-a.v)*(1-c.v));
  }
 }return clip(1-f);
}
function table27(opts,b,M){
 M.event("tableRuns27");M.take("nodeInit",4*(b+1));
 const table=new Float64Array(4*(b+1));
 for(let r=0;r<=b;r++){table[4*r]=1;table[4*r+1]=-1;table[4*r+2]=1;table[4*r+3]=-1}
 const better=(v,i,w,j)=>v<w||(v===w&&(j<0||i<j));
 for(let i=0;i<opts.length;i++){
  const os=opts[i];let j=0;
  for(let r=0;r<=b;r++){
   M.take("rangeOutcome");M.event("tableCells27");
   while(j+1<os.length&&os[j+1].t<=r){M.take("option");M.event("tableAdvances27");j++}
   if(j===0)continue;
   const v=1-os[j].v,p=4*r;
   if(better(v,i,table[p],table[p+1])){
    table[p+2]=table[p];table[p+3]=table[p+1];table[p]=v;table[p+1]=i
   }else if(better(v,i,table[p+2],table[p+3])){
    table[p+2]=v;table[p+3]=i
   }
  }
 }
 let fail=1;
 for(let i=0;i<opts.length;i++)for(let j=1;j<opts[i].length;j++){
  const o=opts[i][j],p=4*(b-o.t),ex=table[p+1]===i;
  M.take("allocation");M.event("tableProducts27");if(ex)M.event("tableExclusions27");
  fail=Math.min(fail,(1-o.v)*table[p+(ex?2:0)])
 }
 return clip(1-fail)
}
function estimates27(opts,b,M){
 const before=M.used,n=opts.length;let c1=Infinity,c2=Infinity,c3=Infinity,K=0,J=0,D=0;
 for(let i=0;i<n;i++){
  const os=opts[i],c=os[1].t,k=os.length-1;
  M.take("option");K+=k;J+=k*k;
  if(c<c1){c3=c2;c2=c1;c1=c}else if(c<c2){c3=c2;c2=c}else if(c<c3)c3=c;
  for(const o of os){M.take("option");D+=i===n-1?1:b-o.t+1}
 }
 return {c1,c2,c3,n,K,pair:n+n*(n-1)/2+K*K-J,table:4*(b+1)+n*(b+1)+2*K,fold:D,gate:M.used-before};
}
function alloc27(opts,b,M,mode){
 if(!opts.length){M.event("zeroCases26");return 0}
 if(opts.length===1){M.event("singleCases26");return single26(opts,M)}
 if(mode==="fused")return fold26(opts,b,M);
 if(mode==="last")return last27(opts,b,M);
 M.event("gateCalls27");
 const e=estimates27(opts,b,M);M.event("gateUnits27",e.gate);
 M.event("gatePairBound",e.pair);M.event("gateTableBound",e.table);M.event("gateFoldBound",e.fold);
 if(e.c1+e.c2>b){M.event("gateSingle27");return single26(opts,M)}
 if(e.c1+e.c2+e.c3>b){
  M.event("gateTwo27");
  const useTable=mode==="table"&&e.table<e.pair&&e.table+e.gate<=e.fold;
  const usePair=e.pair+e.gate<=e.fold;
  if(useTable||usePair){
   const before=M.used,v=useTable?table27(opts,b,M):pair27(opts,b,M),bound=useTable?e.table:e.pair;
   M.event("kernelActual27",M.used-before);M.event("kernelBound27",bound);
   ok(M.used-before<=bound,"gate bound");return v
  }
  M.event("gateRejected27")
 }
 return last27(opts,b,M)
}
class Scalar27 extends Scalar26{
 constructor(P,M,mode,B){super(P,M,"joint",B);this.mode27=mode}
 alloc(s,b){
  const M=this.M;M.event("factorQueries");M.take("lookup");const c=canon16(this.P,s,b);
  if(this.av.has(c.key))return this.av.get(c.key);
  const opts=[];
  for(const {i} of c.entries){
   const id=s[i],os=[{t:0,v:0}];M.take("option");
   if(id>=0){
    const l=this.P.local[i],v=l.at(id),m=l.L-v.stage,k=Math.min(3,b-m);
    if(k>0&&v.mass>0){
     const pair=k>=2&&m>0?this.pair26(i,id):null;let last=0;
     for(let j=1;j<=k;j++){
      M.take("option");const value=pair&&j<=2?pair[j]:this.val(i,id,m+j);
      if(value>last+1e-15){os.push({t:m+j,v:value});last=value}
     }
    }
   }
   if(os.length===1){M.event("identitySkips26");continue}
   opts.push(os)
  }
  const v=alloc27(opts,b,M,this.mode27);this.av.set(c.key,v);return v
 }
}
function make27(P,M,mode,B){return ["direct","scalar","joint","skip","both"].includes(mode)?make26(P,M,mode,B):new Scalar27(P,M,mode,B)}
class Inc27 extends Inc19{
 constructor(P,M,mode,B,retained){super(P,M,"incCheap",retained,false);this.factor27=make27(P,M,mode,B)}
 val(i,id,b){return this.factor27.val(i,id,b)}
 alloc(s,b){return this.factor27.alloc(s,b)}
 dl(s,b){return this.factor27.dl(s,b)}
}
class Two27 extends Two19{
 constructor(P,M,B){super(P,M,"prophet",null);this.factor27=make27(P,M,"last",B)}
 val(i,id,b){return this.factor27.val(i,id,b)}
 alloc(s,b){return this.factor27.alloc(s,b)}
 dl(s,b){return this.factor27.dl(s,b)}
}
function unit27(){
 const r=rng(3350001);let checks=0,forced=0,maxError=0,tableExclusions=0,tableRuns=0,pairRuns=0,gateBoundChecks=0;
 function test(raw,b){
  const n=raw.length,den=10n**BigInt(n);let best=den;
  function rec(i,c,f){if(i===n){if(f<best)best=f;return}for(const a of raw[i])if(c+a.t<=b)rec(i+1,c+a.t,f*BigInt(10-a.num))}
  rec(0,0,1n);const truth=Number(den-best)/Number(den),os=raw.map(x=>x.filter(a=>a.t<=b).map(a=>({t:a.t,v:a.num/10}))).filter(x=>x.length>1);
  const check=v=>{const e=Math.abs(v-truth);ok(e<1e-12,"exact integer reference");maxError=Math.max(maxError,e);checks++};
  for(const k of ["fused","last","linear","table"])check(alloc27(os,b,meter27(Infinity),k));
  if(os.length){
   const e=estimates27(os,b,meter27(Infinity));
   const F=meter27(Infinity);check(last27(os,b,F));ok(F.used===e.fold,"fold estimate");gateBoundChecks++;
   if(e.c1+e.c2+e.c3>b){
    for(const [fn,bound] of [[pair27,e.pair],[table27,e.table]]){
     const M=meter27(Infinity);check(fn(os,b,M));forced++;ok(M.used<=bound,"forced kernel bound");gateBoundChecks++;tableExclusions+=M.c.tableExclusions27;tableRuns+=M.c.tableRuns27;pairRuns+=M.c.pairRuns27
    }
   }
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
 const three=Array.from({length:3},()=>[{t:0,num:0},{t:2,num:5}]);
 for(const b of [1,2,3,4,5,6])test(three,b);
 test([],4);test([[{t:0,num:0}]],4);test([[{t:0,num:0},{t:2,num:7}]],3);
 // Best branch exclusion with tied best alternatives, one strong branch.
 test([[{t:0,num:0},{t:2,num:9}],[{t:0,num:0},{t:2,num:5}],[{t:0,num:0},{t:2,num:5}]],4);
 return {checks,forced,maxError,tableExclusions,tableRuns,pairRuns,gateBoundChecks}
}
function trace27(root,cap,B,auditAll){
 const P=new Problem(root,cap);setup(P);const qs=queries25(P,B).flatMap(g=>g.qs),R=new AllocationProblem(root,cap);setup(R);
 const truth=qs.map(q=>R.alloc(align16(P,q.s,R),q.b).v),modes=["direct","scalar","joint","skip","both","fused","last","linear","table"],rows=[];
 let allBudgetChecks=0,maxError=0;
 for(const mode of modes){
  const M=meter27(Infinity),G=make27(P,M,mode,B);let emax=0;
  for(let i=0;i<qs.length;i++){
   const q=qs[i],v=G.alloc(q.s,q.b),e=Math.abs(v-truth[i]);ok(e<1e-10,"trace disagreement "+JSON.stringify({mode,q,v,truth:truth[i],e}));emax=Math.max(emax,e)
  }
  if(G.store)ok(G.store.index.size<=G.store.slots,"trace cap");
  ok(M.used===sum(charges.map(k=>M.c[k])),"trace ledger");
  rows.push({kind:mode,queries:qs.length,work:M.used,typedBytes:G.bytes??null,stats:M.c,maxError:emax});maxError=Math.max(maxError,emax);
  if(auditAll){
   const A=make27(P,meter27(Infinity),mode,B);
   for(const q of qs){const s=align16(P,q.s,R);for(let b=0;b<=q.b;b++){const e=Math.abs(A.alloc(q.s,b)-R.alloc(s,b).v);ok(e<1e-10,"all budget");allBudgetChecks++;maxError=Math.max(maxError,e)}}
  }
 }
 const changed=[0,0,0];for(const q of qs)changed[q.changed]++;
 return {queries:qs.length,distinct:new Set(qs.map(q=>key(q.s,q.b))).size,changed,valueChecks:qs.length*modes.length,allBudgetChecks,maxError,rows}
}
function policy27(root,cap,B,total,mode,oracle){
 const P=new Problem(root,cap),pre=setup(P),inc=mode!=="last2",audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakSlots:0,peakNodes:0,peakEdges:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank27(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0],M=meter27(Math.min(left,Math.ceil(2*left/b))),G=inc?new Inc27(P,M,mode,B,retained):new Two27(P,M,B),r=G.solve(s,b,fallback);
  if(!r.ranges&&inc&&M.c.fallback===0)M.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakSlots=Math.max(audit.peakSlots,M.c.storePeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,G.peakEdges);
  ok(G.factor27.store.index.size<=G.factor27.store.slots,"store cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){if(o.hit){v+=o.p;continue}
   const C=meter27(left-M.used);let keep=null;
   if(inc&&r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyInc19(o.n,C);
   addWork(work,C.c,o.p);const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep);
   v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p)
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work}
 }
 const r=rec(P.initial(),B,total,null),regret=oracle.rec(oracle.P.initial(),B).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre}
}
function cohort27(name){
 if(name==="standard")return {n:24,seed:3320001,pop:3,stages:3,b:6};
 if(name==="population")return {n:20,seed:3330001,pop:5,stages:2,b:6};
 return {n:12,seed:3340001,pop:7,stages:2,b:5}
}
function experiment27(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort27(name),cap=2,traceModes=["direct","scalar","joint","skip","both","fused","last","linear","table"],modes=["incCheap","metered2","scalar","joint","fused","last","linear","table","last2"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),refs={optimal:[],receding2:[]},traces=[];
 const audit={unit:unit27(),queries:0,distinct:0,changed:[0,0,0],valueChecks:0,allBudgetChecks:0,maxError:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),t=trace27(root,cap,b,i<2);traces.push(t);
  for(const k of ["queries","distinct","valueChecks","allBudgetChecks"])audit[k]+=t[k];for(let j=0;j<3;j++)audit.changed[j]+=t.changed[j];audit.maxError=Math.max(audit.maxError,t.maxError);
  const P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);refs.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);refs.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  for(const t of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,t,mode,oracle,false):["scalar","joint"].includes(mode)?policy26(root,cap,b,t,mode,oracle):policy27(root,cap,b,t,mode,oracle);
   r.work={...blank27(),...r.work};all[mode+t].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,traceRows=[],tracePairs=[],rows=[],paired=[];
 for(const mode of traceModes){
  const a=traces.map(t=>t.rows.find(r=>r.kind===mode)),stats=Object.fromEntries(Object.keys(blank27()).map(k=>[k,k==="storePeak"?Math.max(...a.map(x=>x.stats[k])):sum(a.map(x=>x.stats[k]))]));
  traceRows.push({kind:mode,roots:n,queries:audit.queries,totalWork:sum(a.map(x=>x.work)),typedBytes:a[0].typedBytes,stats,maxError:Math.max(...a.map(x=>x.maxError))})
 }
 for(const [k,r] of [["fused","scalar"],["last","fused"],["linear","last"],["table","last"],["table","linear"],["linear","both"],["table","both"],["last","direct"]]){
  const d=traces.map(t=>t.rows.find(x=>x.kind===k).work-t.rows.find(x=>x.kind===r).work);tracePairs.push({kind:k,ref:r,...bootstrap(d,(0xC0271000+seed+traceModes.indexOf(k)*20+traceModes.indexOf(r))>>>0)})
 }
 for(const total of limits)for(const mode of modes){
  const k=mode+total,a=all[k],work=Object.fromEntries(Object.keys(blank27()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:64*(b+1)*8,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakSlots:max("peakSlots"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}})
 }
 for(const t of limits)for(const [k,r] of [["last","scalar"],["last","incCheap"],["fused","scalar"],["last","fused"],["linear","last"],["table","last"],["table","linear"],["last2","metered2"],["joint","scalar"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0270000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)})
 }
 return {status:"PASS",scope:"finite synthetic independent model, exact scalar kernels and declared work proxy",name,roots:n,population:pop,budget:b,cap,audit,baselines:{optimal:mean(refs.optimal),receding2:mean(refs.receding2)},traceRows,tracePairs,rows,paired,elapsedMs:Date.now()-start}
}
const name27=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
console.log(JSON.stringify(experiment27(name27),null,2));
