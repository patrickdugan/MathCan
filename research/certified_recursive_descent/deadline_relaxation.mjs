// CRD-17: deadline-screening information relaxation and persistent planning.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {EPS15,key15} from "./selective_bellman.mjs";
import {canon16,align16,Sparse16,copyReach16,PersistentPlanner16,emptyEffort16} from "./persistent_symmetry.mjs";

function localSetup17(P){
 let states=0,edges=0;
 for(const l of P.local){
  for(let id=0;id<l.states.length;id++){
   for(const a of l.actions(id,12))edges+=l.outcomes(id,a).length;
  }
  states+=l.states.length;
 }
 return {states,edges};
}
function descriptors17(P,s,b){
 return s.flatMap((id,i)=>{
  if(id<0||b<=0)return [];
  const l=P.local[i],x=l.at(id),m=l.L-x.stage;
  if(m+1>b||x.mass<=0)return [];
  return [{i,m,p:x.p.slice(0,3),w:x.w.slice(0,3).map(BigInt),den:x.w.reduce((a,v)=>a+BigInt(v),0n),mass:x.mass}];
 });
}
function deadline17(P,s,b,work=null){
 const d=descriptors17(P,s,b),screens=d.filter(x=>x.m>0).sort((a,c)=>c.m-a.m||a.i-c.i),ready=d.filter(x=>x.m===0);
 let dp=Array(b+1).fill(Infinity);dp[0]=1;
 if(work){work.boundCalls++;work.sortItems+=screens.length}
 for(const x of screens){
  const next=dp.slice();
  for(let t=0;t<b;t++)if(Number.isFinite(dp[t])&&t+1<=b-x.m){
   if(work)work.boundCombinations++;
   next[t+1]=Math.min(next[t+1],dp[t]*(1-x.mass));
  }
  dp=next;
 }
 for(const x of ready){
  const next=Array(b+1).fill(Infinity),p=x.p.slice().sort((a,c)=>c-a);
  for(let t=0;t<=b;t++)if(Number.isFinite(dp[t])){
   let mass=0;
   for(let k=0;k<=3&&t+k<=b;k++){
    if(k)mass+=p[k-1];
    if(work)work.boundCombinations++;
    next[t+k]=Math.min(next[t+k],dp[t]*Math.max(0,1-mass));
   }
  }
  dp=next;
 }
 return Math.max(0,Math.min(1,1-Math.min(...dp)));
}
function prophet17(P,s,b){
 return 1-descriptors17(P,s,b).reduce((v,x)=>v*(1-x.mass),1);
}
// Independent exhaustive BigInt subset/count enumeration; do not use the DP order.
function integerReference17(P,s,b){
 const d=descriptors17(P,s,b),den=d.reduce((a,x)=>a*x.den,1n);
 let best=den,plans=0;
 function rec(i,deadlines,probes,f){
  if(i===d.length){
   const ds=deadlines.slice().sort((a,c)=>a-c);
   if(ds.length+probes>b||ds.some((x,j)=>j+1>x))return;
   plans++;if(f<best)best=f;return;
  }
  const x=d[i];rec(i+1,deadlines,probes,f*x.den);
  if(x.m>0)rec(i+1,[...deadlines,b-x.m],probes,f*(x.den-x.w.reduce((a,v)=>a+v,0n)));
  else{
   const w=x.w.slice().sort((a,c)=>a>c?-1:a<c?1:0);let mass=0n;
   for(let k=1;k<=3;k++){mass+=w[k-1];rec(i+1,deadlines,probes+k,f*(x.den-mass))}
  }
 }
 rec(0,[],0,1n);return {v:Number(den-best)/Number(den),plans};
}
// Independent recursive relaxed Bellman: feasible screening completes for certain;
// all-failure continuation consumes one call. Ready probes update the failure mask.
function relaxedReference17(P,s,b){
 const d=descriptors17(P,s,b),memo=new Map();let states=0,actions=0;
 function rec(left,flags,masks){
  if(left<=0)return 0;
  const key=JSON.stringify([left,flags,masks]);
  if(memo.has(key))return memo.get(key);
  states++;let v=0;
  for(let i=0;i<d.length;i++){
   const x=d[i];
   if(x.m>0){
    if(!flags[i]||x.m+1>left)continue;
    const next=flags.slice();next[i]=false;actions++;
    v=Math.max(v,x.mass+(1-x.mass)*rec(left-1,next,masks));
   }else{
    const mask=masks[i];let z=1;
    for(let j=0;j<3;j++)if(!(mask&(1<<j)))z-=x.p[j];
    if(z<=1e-15)continue;
    for(let j=0;j<3;j++)if((mask&(1<<j))&&x.p[j]>0){
     const p=x.p[j]/z,next=masks.slice();next[i]=mask&~(1<<j);actions++;
     v=Math.max(v,p+(1-p)*rec(left-1,flags,next));
    }
   }
  }
  memo.set(key,v);return v;
 }
 const v=rec(b,d.map(x=>x.m>0),d.map(x=>x.m===0?7:0));
 return {v,states,actions};
}
function verifyBound17(P,s,b,v){
 const u=deadline17(P,s,b),r=relaxedReference17(P,s,b),q=integerReference17(P,s,b),old=prophet17(P,s,b);
 const err=Math.max(Math.abs(u-r.v),Math.abs(u-q.v));
 ok(err<1e-10&&v<=u+1e-10&&u<=old+1e-10,"deadline reference or envelope");
 return {u,old,err,refStates:r.states,refActions:r.actions,plans:q.plans};
}
function boundsWork17(){return {boundCalls:0,boundHits:0,boundCombinations:0,sortItems:0,warmCalls:0,warmActions:0,warmOutcomes:0,strictTighten:0,eligibleNodes:0,sumTightening:0}}
class BoundPlanner17 extends PersistentPlanner16{
 constructor(P,limit,retained,mode){
  super(P,limit,retained);this.mode=mode;this.upperMemo=new Map();this.warmMemo=new Map();this.bw=boundsWork17();
 }
 dl(s,b){
  const k=canon16(this.P,s,b).key;
  if(this.upperMemo.has(k)){this.bw.boundHits++;return this.upperMemo.get(k)}
  const v=deadline17(this.P,s,b,this.bw);this.upperMemo.set(k,v);return v;
 }
 warm(s,b){
  const k=canon16(this.P,s,b).key;if(this.warmMemo.has(k))return this.warmMemo.get(k);
  let v=0;this.bw.warmCalls++;
  for(const a of this.P.legal(s,b)){
   this.bw.warmActions++;
   const q=sum(this.P.outcomes(s,a).map(o=>{this.bw.warmOutcomes++;return o.p*(o.hit?1:this.dl(o.s,b-1))}));
   v=Math.max(v,q);
  }
  this.warmMemo.set(k,v);return v;
 }
 node(s,b){
  const k=key15(s,b);if(this.cache.has(k))return this.cache.get(k);
  const n=super.node(s,b);
  if(n.U-n.L>EPS15){
   this.bw.eligibleNodes++;const old=n.U;
   if(this.mode!=="prophet"){
    n.U=Math.min(n.U,this.dl(s,b));
    if(this.mode==="backed")n.U=Math.min(n.U,this.warm(s,b));
    ok(n.U>=n.L-1e-10,"tightened upper below static lower");
    n.U=Math.max(n.L,n.U);
   }
   this.bw.strictTighten+=Number(old-n.U>EPS15);this.bw.sumTightening+=old-n.U;
  }
  return n;
 }
}
const extra17=Object.keys(boundsWork17());
function blank17(){return {...emptyEffort16(),...boundsWork17()}}
function policy17(root,cap,budget,total,mode,oracle){
 const P=new Sparse16(root,cap,false),setup=localSetup17(P),audit={visits:0,actionChecks:0,certified:0,maxViolation:0,maxRegret:0,maxGapViolation:0,maxBoundViolation:0,peakNodes:0,peakEdges:0,strictAtReached:0,sumProphetGap:0,sumDeadlineGap:0,sumBackedGap:0};
 function rec(s,b,left,retained){
  if(b<=0||!P.legal(s,b).length)return {v:0,calls:0,evictions:0,work:blank17(),maxUsed:0};
  ok(left>=b,"reserved expansion budget");const quota=Math.min(16,left-(b-1));
  P.reset16();const planner=new BoundPlanner17(P,quota,retained,mode),r=planner.solve16(s,b),w=planner.work,aw=P.work;
  ok(w.nodeExpanded<=quota,"per-decision quota");
  const o=oracle.rec(align16(P,s,oracle.P),b),qmap=new Map(o.qs.map(x=>[x.a.id,x.q]));
  ok(qmap.size===r.ranges.length,"legal action count");
  for(const a of r.ranges){
   const q=qmap.get(a.id),violation=Math.max(0,a.L-q,q-a.U);
   ok(Number.isFinite(q)&&violation<1e-9,"Q interval");audit.actionChecks++;audit.maxViolation=Math.max(audit.maxViolation,violation);
  }
  const violation=Math.max(0,r.L-o.v,o.v-r.U),regret=Math.max(0,o.v-qmap.get(r.action.id));
  ok(violation<1e-9&&regret<=r.gap+1e-9,"state/regret interval");if(r.certified)ok(regret<=EPS15+1e-9,"certified regret");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxRegret=Math.max(audit.maxRegret,regret);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakNodes=Math.max(audit.peakNodes,r.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,r.peakEdges);
  const work=blank17();
  Object.assign(work,{decisions:1,certified:Number(r.certified),expansions:w.nodeExpanded,created:w.nodeCreated,outcomes:w.outcomes,backups:w.backups,propagations:w.propagations,reverseLinks:w.reverseLinks,allocCombinations:aw.allocCombinations,allocCalls:aw.allocCalls,allocHits:aw.allocHits,localCalls:aw.localCalls,localHits:aw.localHits,patterns:aw.patterns,likelihoodProducts:aw.likelihoodProducts,optionCandidates:aw.optionCandidates||0,optionsKept:aw.optionsKept||0,canonicalHits:aw.canonicalHits||0,localCanonicalHits:aw.localCanonicalHits||0,reusedExpandedRoots:Number(r.reused),gapSum:r.gap,actualGapSum:regret},planner.bw);
  // Separate oracle-side audit; no bounds-work counter or policy cache modified.
  const os=align16(P,s,oracle.P),old=prophet17(oracle.P,os,b),dl=deadline17(oracle.P,os,b);
  let warm=0;
  for(const a of oracle.P.legal(os,b))warm=Math.max(warm,sum(oracle.P.outcomes(os,a).map(x=>x.p*(x.hit?1:deadline17(oracle.P,x.s,b-1)))));
  warm=Math.min(dl,warm);
  const bv=Math.max(0,o.v-warm,o.v-dl,dl-old,warm-dl);
  ok(bv<1e-9,"reached information bound");audit.maxBoundViolation=Math.max(audit.maxBoundViolation,bv);
  audit.strictAtReached+=Number(old-dl>EPS15);audit.sumProphetGap+=old-o.v;audit.sumDeadlineGap+=dl-o.v;audit.sumBackedGap+=warm-o.v;
  let v=0,calls=1,evictions=Number(r.action.evict>=0),maxUsed=w.nodeExpanded;
  for(const out of r.selected.os){
   if(out.hit){v+=out.p;continue}
   let keep=null;
   if(out.n.b>0&&P.legal(out.n.s,out.n.b).length){keep=copyReach16(out.n);work.copyNodes+=out.p*keep.nodes;work.copyEdges+=out.p*keep.edges}
   const z=rec(out.n.s,out.n.b,left-w.nodeExpanded,keep);
   v+=out.p*z.v;calls+=out.p*z.calls;evictions+=out.p*z.evictions;
   for(const k of Object.keys(work))work[k]+=out.p*z.work[k];
   maxUsed=Math.max(maxUsed,w.nodeExpanded+z.maxUsed);
  }
  ok(maxUsed<=left&&calls<=b+1e-10,"trajectory accounting");return {v,calls,evictions,work,maxUsed};
 }
 const z=rec(P.initial(),budget,total,null),opt=oracle.rec(oracle.P.initial(),budget).v,regret=opt-z.v;
 ok(regret>=-1e-9&&Math.abs(regret-z.work.actualGapSum)<1e-9&&regret<=z.work.gapSum+1e-9,"trajectory regret");
 return {...z,regret,audit,setup};
}
function cohort17(name){
 if(name==="standard")return {n:64,seed:2320001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:32,seed:2330001,cap:2,b:8,stages:4};
 return {n:48,seed:2340001,cap:1,b:5,stages:4};
}
function root17(name,seed,stages){
 if(name!=="tight")return fixture(seed,3,stages);
 const r=rng(seed),branches=[];
 for(let i=0;i<3;i++){
  const prior=Array.from({length:6},()=>1+Math.floor(r()*12)),L=3+Math.floor(r()*2),sensors=Array.from({length:L},()=>[60,80,100][Math.floor(r()*3)]);
  branches.push({prior,sensors});
 }
 return {seed,branches};
}
function hand17(){
 const cases=[
  {b:6,sensors:[[60],[60],[60]],ready:false,expected:1-.5**3},
  {b:4,sensors:[[60,60,60],[60,60,60],[60,60,60]],ready:false,expected:.5},
  {b:2,sensors:[[100],[100],[100]],ready:true,expected:1-(2/3)**2},
  {b:3,sensors:[[100,100],[100],[100]],mixed:true,expected:1-.5*(2/3)**2}
 ];
 for(const c of cases){
  const root={seed:0,branches:c.sensors.map(sensors=>({prior:[1,1,1,1,1,1],sensors}))},P=new Problem(root,3);localSetup17(P);
  const s=P.initial();
  // Ready state deliberately uses a uniform posterior continuation descriptor.
  if(c.ready)for(let i=0;i<3;i++)s[i]=P.local[i].intern(P.local[i].L,[1,1,1,1,1,1]);
  if(c.mixed)for(let i=1;i<3;i++)s[i]=P.local[i].intern(P.local[i].L,[1,1,1,1,1,1]);
  // Ready-only b=2: two probes on one branch dominate one probe on each.
  const expect=c.ready?1/3:c.mixed?1-.5*(5/6)**2:c.expected;
  const v=deadline17(P,s,c.b),r=relaxedReference17(P,s,c.b),q=integerReference17(P,s,c.b);
  // Mixed: screen then two probes on the same ready branch (1/3 success).
  const target=c.mixed?1-.5*(2/3):expect;
  ok(Math.abs(v-target)<1e-10&&Math.abs(v-r.v)<1e-10&&Math.abs(v-q.v)<1e-10,"hand deadline case "+JSON.stringify({v,target,c}));
 }
 return cases.length;
}
function experiment17(name){
 const start=Date.now(),{n,seed,cap,b,stages}=cohort17(name),keys=[16,48].flatMap(t=>["prophet","deadline","backed"].map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]]));
 const ref={optimal:[],receding2:[]},baseWork={states:0,actions:0,transitions:0,allocCombinations:0,h1Outcomes:0,h2Outcomes:0};
 const check={hand:hand17(),rootChecks:0,stateChecks:0,relaxStates:0,relaxActions:0,integerPlans:0,maxError:0,strictRoots:0,rootProphetGap:0,rootDeadlineGap:0,setupStates:0,setupEdges:0};
 for(let i=0;i<n;i++){
  const root=root17(name,seed+i,stages),OP=new Problem(root,cap),setup=localSetup17(OP),oracle=new Engine(OP,"optimal",null),opt=oracle.rec(OP.initial(),b);
  check.setupStates+=setup.states;check.setupEdges+=setup.edges;
  baseWork.states+=oracle.stats.states;baseWork.actions+=oracle.stats.actions;baseWork.transitions+=oracle.stats.transitions;
  for(let t=0;t<=b;t++){
   const exact=oracle.rec(OP.initial(),t).v,q=verifyBound17(OP,OP.initial(),t,exact);
   check.rootChecks++;check.relaxStates+=q.refStates;check.relaxActions+=q.refActions;check.integerPlans+=q.plans;check.maxError=Math.max(check.maxError,q.err);
   if(t===b){check.strictRoots+=Number(q.old-q.u>EPS15);check.rootProphetGap+=q.old-exact;check.rootDeadlineGap+=q.u-exact}
  }
  if(i<2)for(const x of [...oracle.memo.values()].filter(x=>x.s&&x.action).slice(0,128)){
   const q=verifyBound17(OP,x.s,x.b,x.v);
   check.stateChecks++;check.relaxStates+=q.refStates;check.relaxActions+=q.refActions;check.integerPlans+=q.plans;check.maxError=Math.max(check.maxError,q.err);
  }
  const RP=new AllocationProblem(root,cap);localSetup17(RP);
  const R=new Engine(RP,"receding2",null),rr=R.rec(RP.initial(),b);
  ref.optimal.push(opt.v);ref.receding2.push(rr.v);
  for(const k of ["allocCombinations","h1Outcomes","h2Outcomes"])baseWork[k]+=RP.work[k];
  for(const total of [16,48])for(const mode of ["prophet","deadline","backed"])all[mode+total].push(policy17(root,cap,b,total,mode,oracle));
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const kind of keys){
  const a=all[kind],work=Object.fromEntries(Object.keys(blank17()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]));
  const visits=sum(a.map(x=>x.audit.visits));
  rows.push({kind,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedEvictions:mean(a.map(x=>x.evictions)),work,expectedCertificateRate:work.certified/work.decisions,maxUsed:Math.max(...a.map(x=>x.maxUsed)),peakNodes:max("peakNodes"),peakEdges:max("peakEdges"),setupStates:sum(a.map(x=>x.setup.states)),setupEdges:sum(a.map(x=>x.setup.edges)),audit:{visits,actions:sum(a.map(x=>x.audit.actionChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxBoundViolation:max("maxBoundViolation"),maxGapViolation:max("maxGapViolation"),maxRegret:max("maxRegret"),strictDeadlineRate:sum(a.map(x=>x.audit.strictAtReached))/visits,meanProphetGap:sum(a.map(x=>x.audit.sumProphetGap))/visits,meanDeadlineGap:sum(a.map(x=>x.audit.sumDeadlineGap))/visits,meanBackedGap:sum(a.map(x=>x.audit.sumBackedGap))/visits}});
 }
 for(const total of [16,48])for(const mode of ["deadline","backed"])for(const refName of ["prophet"+total,"deadline"+total,"receding2","optimal"].filter(x=>x!==mode+total)){
  const a=all[mode+total],other=ref[refName]??all[refName].map(x=>x.v),d=a.map((x,i)=>x.v-other[i]);
  paired.push({kind:mode+total,ref:refName,...bootstrap(d,(0xC0170000+seed+total*100+keys.indexOf(mode+total)*10+["prophet"+total,"deadline"+total,"receding2","optimal"].indexOf(refName))>>>0)});
 }
 check.rootProphetGap/=n;check.rootDeadlineGap/=n;
 return {status:"PASS",scope:"independent finite synthetic decision model; numerical enclosures and trajectory-weighted work",name,roots:n,cap,budget:b,check,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2),work:baseWork},rows,paired,elapsedMs:Date.now()-start};
}
const cohort=process.argv.includes("--deep")?"deep":process.argv.includes("--tight")?"tight":"standard";
console.log(JSON.stringify(experiment17(cohort),null,2));
