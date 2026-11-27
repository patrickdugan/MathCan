// CRD-20: progressive bounded two-step lower-envelope refinement.
import {ok,sum,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {align16} from "./persistent_symmetry.mjs";
import {EPS,quant,clip,key,STOP,charges,setup,Planner,addWork,rootFor} from "./metered_refinement.mjs";
import {blank19,meter19,snapshot19,cheapValue19,policy19} from "./incremental_refinement.mjs";

const ev20=["commits","staticTerms","secondTerms","deadlineTerms","childRosters","blockedRosters","arenaPeak","partialUseful","taskScans","auditUpdates","fullTwoStepRoots"];
const blank20=()=>({...blank19(),...Object.fromEntries(ev20.map(k=>[k,0]))});
function meter20(limit){const m=meter19(limit);m.c=blank20();return m}
function range20(os,child,M=null){
 if(M)M.take("rangeEval");let L=0,U=0;
 for(const o of os){if(M)M.take("rangeOutcome");const z=o.hit?{L:1,U:1}:child(o);L+=o.p*z.L;U+=o.p*z.U}
 return {L:clip(L),U:clip(U)};
}
function intersect20(a,b){
 const L=Math.max(a.L,b.L),U=Math.min(a.U,b.U);
 ok(L<=U+EPS,"empty progressive interval");return {L:clip(L),U:clip(Math.max(L,U))};
}
class Progressive20 extends Planner{
 constructor(P,M,mode,cap,audit=false,finish=false){
  super(P,M,"prophet",null);
  this.mode20=mode;this.cap20=cap;this.audit20=audit;this.finish20=finish;
  this.children=new Map();this.rows=[];this.records=0;this.peak=0;this.snap=null;this.cheap=null;this.parentB=0;this.initialized=false;
 }
 admit(n){
  if(this.records+n>this.cap20)return false;
  this.records+=n;this.peak=Math.max(this.peak,this.records);this.M.c.arenaPeak=this.peak;return true;
 }
 root20(s,b){
  const M=this.M,children=new Map(),rows=[];let records=0;
  this.parentB=b;
  for(const a of this.P.legal(s,b)){
   M.take("actionEnum");const count=this.P.local[a.i].outcomes(s[a.i],a.t).length;M.take("outcomeGen",count);
   const os=[];M.take("nodeInit");records++;
   for(const o of this.P.outcomes(s,a)){
    M.take("nodeInit");records++;
    if(o.hit){os.push({p:o.p,hit:true,c:null});continue}
    M.take("lookup");const k=key(o.s,b-1);let c=children.get(k);
    if(!c){
     M.take("nodeInit");records++;const r=cheapValue19(this.P,o.s,b-1,M);
     c={k,s:o.s.slice(),b:b-1,L:r.L,U:r.U,staticDone:false,roster:null,blocked:false,reach:0,refs:new Set(),id:children.size};
     children.set(k,c);
    }
    c.reach+=o.p;c.refs.add(rows.length);os.push({p:o.p,hit:false,c});
   }
   rows.push({a,os,...range20(os,o=>o.c,M)});
  }
  this.M.event("cheapSnapshots");
  this.cheap=snapshot19(rows.map(({a,L,U})=>({a,L,U})));this.snap=this.cheap;
  if(!this.admit(records)){M.event("blockedRosters");return}
  this.rows=rows;this.children=children;this.initialized=true;
 }
 // All affected root sums and a complete ranking are paid before committing.
 // Cached child roster updates are immutable until that transaction succeeds.
 commit(c,z,patch={}){
  const M=this.M,next=intersect20(c,z),changed=next.L!==c.L||next.U!==c.U,rows=this.rows.slice();
  if(changed){
   for(const i of c.refs){
    M.take("traverseEdge");
    const a=rows[i],r=range20(a.os,o=>o.c===c?next:o.c,M);
    rows[i]={...a,...intersect20(a,r)};
   }
  }
  // Ranking scan is charged even when cached intervals have not changed.
  for(const a of rows)M.take("rangeEval");
  const snap=snapshot19(rows.map(({a,L,U})=>({a,L,U})));
  ok(snap.bestL+EPS>=this.snap.bestL,"nonmonotone root lower");
  ok(snap.U<=this.snap.U+EPS,"nonmonotone root upper");
  Object.assign(c,next,patch);this.rows=rows;this.snap=snap;M.event("commits");
  if(this.audit20)this.auditCurrent();
 }
 auditCurrent(){
  for(const a of this.rows){
   const r=range20(a.os,o=>o.c);
   ok(Math.abs(a.L-r.L)<1e-10&&Math.abs(a.U-r.U)<1e-10,"root direct reconstruction");this.M.event("auditUpdates");
  }
  for(const c of this.children.values())if(c.roster){
   for(const a of c.roster){
    const r=range20(a.os,o=>o);
    ok(Math.abs(a.L-r.L)<1e-10&&Math.abs(a.U-r.U)<1e-10,"child direct reconstruction");this.M.event("auditUpdates");
   }
   const L=Math.max(0,...c.roster.map(a=>a.L)),U=Math.max(0,...c.roster.map(a=>a.U));
   ok(c.L>=L-EPS&&c.U<=U+EPS,"child backup intersection");
  }
 }
 static20(c){
  const v=this.alloc(c.s,c.b);
  this.commit(c,{L:v,U:c.U},{staticDone:true});this.M.event("staticTerms");
 }
 roster20(c){
  const M=this.M,as=this.P.legal(c.s,c.b),raw=[];let records=0;
  // Count and charge the proposed roster. A blocked roster consumes the
  // enumeration charge but generates no conditional outcomes or records.
  for(const a of as){M.take("actionEnum");const n=this.P.local[a.i].outcomes(c.s[a.i],a.t).length;raw.push({a,n});records+=1+n}
  if(this.records+records>this.cap20){c.blocked=true;M.event("blockedRosters");return}
  const rows=[];
  for(const {a,n} of raw){
   M.take("nodeInit");M.take("outcomeGen",n);const os=[];
   for(const o of this.P.outcomes(c.s,a)){
    M.take("nodeInit");const r=o.hit?{L:1,U:1}:cheapValue19(this.P,o.s,c.b-1,M);
    os.push({p:o.p,hit:o.hit,s:o.s?.slice()??null,...r,doneF:o.hit,doneD:o.hit});
   }
   rows.push({a,os,...range20(os,o=>o,M)});
  }
  M.take("backup");for(const a of rows)M.take("rangeEval");
  const L=Math.max(0,...rows.map(a=>a.L)),U=Math.max(0,...rows.map(a=>a.U));
  this.commit(c,{L,U},{roster:rows});
  ok(this.admit(records),"atomic roster capacity");M.event("childRosters");
 }
 term20(c,i,j,tier){
  const M=this.M,rows=c.roster.slice(),a=rows[i],os=a.os.slice(),o=os[j];
  let z;
  if(tier==="F"){const v=this.alloc(o.s,c.b-1);z={...o,...intersect20(o,{L:v,U:o.U}),doneF:true}}
  else{const u=this.dl(o.s,c.b-1);z={...o,...intersect20(o,{L:o.L,U:u}),doneD:true}}
  os[j]=z;
  rows[i]={...a,os,...intersect20(a,range20(os,x=>x,M))};
  M.take("backup");for(const a of rows)M.take("rangeEval");
  const L=Math.max(0,...rows.map(a=>a.L)),U=Math.max(0,...rows.map(a=>a.U));
  this.commit(c,{L,U},{roster:rows});
  M.event(tier==="F"?"secondTerms":"deadlineTerms");
 }
 chooseTask(){
  const M=this.M,seq=this.mode20==="sequential",tasks=[],best=this.snap.bestL;
  const reach=c=>{
   let p=0;
   for(const i of c.refs){
    M.take("rangeEval");const a=this.rows[i];
    if(seq||a.U+EPS>=best)for(const o of a.os){M.take("rangeOutcome");if(o.c===c)p+=o.p}
   }return p;
  };
  // Phase one: F on every relevant first successor before second-level tasks.
  for(const c of this.children.values()){
   M.take("leafVisit");M.event("taskScans");
   if(c.staticDone||c.U-c.L<=EPS/10)continue;
   const p=reach(c);if(p>0)tasks.push({type:"static",c,score:p*(c.U-c.L),i:-1,j:-1});
  }
  if(!tasks.length){
   for(const c of this.children.values()){
    M.take("leafVisit");M.event("taskScans");
    if(c.blocked||c.U-c.L<=EPS/10)continue;
    const p=reach(c);if(!p)continue;
    if(!c.roster){tasks.push({type:"roster",c,score:p*(c.U-c.L),i:-1,j:-1});continue}
    const childBest=Math.max(0,...c.roster.map(a=>a.L));
    for(let i=0;i<c.roster.length;i++){
     M.take("rangeEval");const a=c.roster[i];
     if(!seq&&a.U+EPS<childBest)continue;
     for(let j=0;j<a.os.length;j++){
      M.take("rangeOutcome");M.event("taskScans");const o=a.os[j];
      if(o.hit||o.U-o.L<=EPS/10)continue;
      const type=!o.doneF?"F":this.mode20==="weightedDeadline"&&!o.doneD?"D":null;
      if(type)tasks.push({type,c,i,j,score:p*o.p*(o.U-o.L)});
     }
    }
   }
  }
  if(!tasks.length)return null;
  // For sequential preserve insertion order. Weighted priority uses current
  // bound width and summed reach across competing root actions, not oracle Q.
  if(!seq)tasks.sort((a,b)=>b.score-a.score||a.c.id-b.c.id||a.i-b.i||a.j-b.j);
  return tasks[0];
 }
 solve(s,b,fallback){
  const M=this.M;M.event("decisions");
  try{
   this.root20(s,b);
   while(this.initialized&&(!this.snap.certified||this.finish20)){
    const t=this.chooseTask();if(!t)break;
    if(t.type==="static")this.static20(t.c);
    else if(t.type==="roster")this.roster20(t.c);
    else this.term20(t.c,t.i,t.j,t.type);
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  if(!this.snap){M.event("fallback");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(this.snap.bestL>this.cheap.bestL+EPS)M.event("partialUseful");
  if(this.snap.certified)M.event("certified");
  if(this.snap===this.cheap)M.event("cheapSelected");
  return this.snap;
 }
}
function reference20(P,s,b){
 const memo=new Map();
 function h1(s,b){
  if(b<=0)return 0;const k=key(s,b);if(memo.has(k))return memo.get(k);
  const v=Math.max(0,...P.legal(s,b).map(a=>sum(P.outcomes(s,a).map(o=>o.p*(o.hit?1:P.alloc(o.s,b-1).v)))));
  memo.set(k,v);return v;
 }
 return P.legal(s,b).map(a=>({id:a.id,L:sum(P.outcomes(s,a).map(o=>o.p*(o.hit?1:h1(o.s,b-1))))}));
}
function unlimited20(root,cap,b){
 const P=new Problem(root,cap),Q=new AllocationProblem(root,cap);setup(P);setup(Q);
 const M=meter20(Infinity),g=new Progressive20(P,M,"sequential",Infinity,true,true);
 const r=g.solve(P.initial(),b,P.legal(P.initial(),b)[0]),ref=reference20(Q,Q.initial(),b),cheap=new Map(g.cheap.ranges.map(a=>[a.id,a.L]));
 let max=0;for(const a of r.ranges){
  const x=ref.find(v=>v.id===a.id),err=Math.abs(a.L-Math.max(cheap.get(a.id),x.L));
  ok(err<1e-10,"unlimited progressive T^2F "+JSON.stringify({a,x,cheap:cheap.get(a.id),err}));max=Math.max(max,err);
 }
 return {checks:r.ranges.length,max,updates:M.c.auditUpdates};
}
function policy20(root,cap,budget,total,mode,arena,oracle,doAudit){
 const P=new Problem(root,cap),pre=setup(P),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakRecords:0,updates:0};
 function rec(s,b,left){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank20(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,b)=>b.id-a.id)[0];
  const M=meter20(Math.min(left,Math.ceil(2*left/b))),g=new Progressive20(P,M,mode,arena,doAudit),r=g.solve(s,b,fallback);
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));
  let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);
  ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"progressive oracle interval");
  if(r.certified)ok(regret<=EPS+1e-9,"certified");
  ok(g.records<=arena&&g.peak<=arena,"record arena");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakRecords=Math.max(audit.peakRecords,g.peak);audit.updates+=M.c.auditUpdates;
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  for(const o of P.outcomes(s,r.a)){
   if(o.hit){v+=o.p;continue}
   const q=rec(o.s,b-1,left-M.used);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*q.used;maxUsed=Math.max(maxUsed,M.used+q.maxUsed);addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"work/call ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"work identity");
  return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),budget,total),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");
 return {...r,regret,audit,pre};
}
function cohort20(name){
 if(name==="standard")return {n:48,seed:2620001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:24,seed:2630001,cap:2,b:8,stages:4};
 return {n:32,seed:2640001,cap:1,b:5,stages:4};
}
function experiment20(name){
 const start=Date.now(),{n,seed,cap,b,stages}=cohort20(name),modes=["incCheap","metered2","sequential","weighted","weightedDeadline","weighted32"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]};
 const check={unlimitedRoots:0,unlimitedActions:0,maxValueError:0,unlimitedUpdates:0,updates:0};
 for(let i=0;i<n;i++){
  const root=rootFor(name,seed+i,stages),P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);
  ref.optimal.push(opt.v);const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(i<4){const u=unlimited20(root,cap,b);check.unlimitedRoots++;check.unlimitedActions+=u.checks;check.maxValueError=Math.max(check.maxValueError,u.max);check.unlimitedUpdates+=u.updates}
  for(const total of limits)for(const mode of modes){
   let r;
   if(mode==="incCheap"||mode==="metered2"){
    r=policy19(root,cap,b,total,mode,oracle,false);r.work={...blank20(),...r.work};r.audit.peakRecords=null;r.audit.updates=0;
   }else r=policy20(root,cap,b,total,mode==="weighted32"?"weighted":mode,mode==="weighted32"?32:96,oracle,i<2);
   all[mode+total].push(r);check.updates+=r.audit.updates;
  }
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const k of keys){
  const a=all[k],work=Object.fromEntries(Object.keys(blank20()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakRecords:k.startsWith("incCheap")||k.startsWith("metered2")?null:max("peakRecords")}});
 }
 for(const t of limits)for(const [k,r] of [["weighted","metered2"],["weighted","sequential"],["weighted","incCheap"],["weightedDeadline","weighted"],["weighted32","weighted"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);
  paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0200000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite synthetic decision model, weighted work and logical records",name,roots:n,cap,budget:b,check,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-start};
}
const cohortName20=process.argv.includes("--deep")?"deep":process.argv.includes("--tight")?"tight":"standard";
console.log(JSON.stringify(experiment20(cohortName20),null,2));
