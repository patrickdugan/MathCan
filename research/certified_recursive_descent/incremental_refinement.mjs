import {pathToFileURL} from "node:url";
// CRD-19: metered incremental Bellman transactions and feasible early ranking.
import {ok,sum,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {align16} from "./persistent_symmetry.mjs";
import {EPS,quant,clip,key,STOP,charges,blank,Meter,top,setup,affordable,prophet,Planner,copyGraph,addWork,rootFor} from "./metered_refinement.mjs";

const extra19=["transactions","changedParents","cachedReads","rangeAuditChecks","cheapSnapshots","cheapSelected","twoStepSnapshots","twoStepSelected","adaptiveWarm","partialAborts"];
const blank19=()=>({...blank(),...Object.fromEntries(extra19.map(k=>[k,0]))});
function meter19(limit){const m=new Meter(limit);m.c=blank19();return m}
const ordered19=xs=>xs.slice().sort((a,b)=>quant(b.L)-quant(a.L)||b.a.id-a.a.id);
function snapshot19(rows,root=null){
 const as=ordered19(rows),a=as[0];ok(a,"snapshot");
 const gap=Math.max(0,...as.map(x=>x.U-a.L));
 const L=Math.max(root?.L??0,...as.map(x=>x.L)),U=Math.min(root?.U??1,Math.max(...as.map(x=>x.U)));
 ok(L<=U+EPS,"snapshot state interval");
 return {a:a.a,os:a.os??null,L:clip(L),U:clip(Math.max(L,U)),gap,certified:gap<=EPS,ranges:as.map(x=>({id:x.a.id,L:x.L,U:x.U})),bestL:a.L};
}
function better19(a,b){
 if(!a)return b;if(!b)return a;
 const q=quant(a.bestL)-quant(b.bestL);
 return q>0?a:q<0?b:a.a.id>b.a.id?a:b;
}
function cheapValue19(P,s,b,M){
 let L=0,U=0,failure=1;
 for(const x of affordable(P,s,b)){
  M.take("option");M.take("localMiss");
  L=Math.max(L,top(x.p,Math.min(3,b-x.m)));failure*=1-x.mass;
 }
 U=1-failure;return {L:clip(L),U:clip(Math.max(L,U))};
}
function cheapRoot19(P,s,b,M){
 const raw=[],rows=[];
 for(const a of P.legal(s,b)){
  M.take("actionEnum");const count=P.local[a.i].outcomes(s[a.i],a.t).length;M.take("outcomeGen",count);
  const os=P.outcomes(s,a);raw.push({a,os});M.take("rangeEval");let L=0,U=0;
  for(const o of os){M.take("rangeOutcome");const r=o.hit?{L:1,U:1}:cheapValue19(P,o.s,b-1,M);L+=o.p*r.L;U+=o.p*r.U}
  rows.push({a,L:clip(L),U:clip(U)});
 }
 M.event("cheapSnapshots");return {snap:snapshot19(rows),raw,rows};
}
function ensureParents19(n){if(!n.parents)n.parents=new Map();return n}
function direct19(a,shadow,M=null){
 if(M)M.take("rangeEval");let L=0,U=0;
 for(const o of a.os){if(M)M.take("rangeOutcome");const v=o.hit?{L:1,U:1}:shadow.get(o.n)??o.n;L+=o.p*v.L;U+=o.p*v.U}
 return {L:clip(L),U:clip(U)};
}
class Inc19 extends Planner{
 constructor(P,M,mode,retained,audit=false){
  super(P,M,mode==="incLazy"?"lazy":"deadline",retained);
  this.variant=mode;this.auditTransactions=audit;
 }
 node(s,b){return ensureParents19(super.node(s,b))}
 range(a){
  this.M.take("rangeEval");this.M.event("cachedReads");ok(a.r,"missing cached range");return {a:a.a,os:a.os,L:a.r.L,U:a.r.U}
 }
 refresh(root){this.M.take("traverseNode")}
 // Prepare a complete atomic transaction. Its shadow map contains staged
 // node values and action lists. Charge dependencies before committing.
 transaction(n,L,U,actions=null,links=[]){
  const M=this.M,shadow=new Map(),pending=new Map(),original=n;
  function enqueue(child){
   for(const [p,idxs] of child.parents??[]){
    for(const idx of idxs){M.take("traverseEdge");if(!pending.has(p))pending.set(p,new Set());pending.get(p).add(idx)}
   }
  }
  const bounded=(node,l,u,list)=>{
   if(list){M.take("backup");let ml=0,mu=0;for(const a of list){M.take("rangeEval");M.event("cachedReads");ml=Math.max(ml,a.r.L);mu=Math.max(mu,a.r.U)}l=Math.max(l,ml);u=Math.min(u,mu)}
   ok(l<=u+EPS,"incremental enclosure");return {L:clip(l),U:clip(Math.max(l,u)),actions:list};
  };
  M.take("traverseNode");
  const first=bounded(n,L,U,actions??n.actions);shadow.set(n,first);
  if(first.L!==n.L||first.U!==n.U)enqueue(n);
  // All dependencies decrease b along forward edges; lowest remaining budget
  // first ensures every changed child is staged before its parent.
  while(pending.size){
   let p=null;for(const x of pending.keys())if(!p||x.b<p.b||(x.b===p.b&&x.key<p.key))p=x;
   M.take("traverseNode");const idxs=pending.get(p);pending.delete(p);
   const as=p.actions.slice();
   for(const i of idxs){const a=as[i];as[i]={...a,r:direct19(a,shadow,M)}}
   const z=bounded(p,p.L,p.U,as);shadow.set(p,z);M.event("changedParents");
   if(z.L!==p.L||z.U!==p.U)enqueue(p);
  }
  // New reverse links are charged before attachment; no partial update survives.
  for(const link of links)M.take("traverseEdge");
  for(const [p,z] of shadow){p.L=z.L;p.U=z.U;p.actions=z.actions}
  for(const {child,parent,idx} of links){
   ensureParents19(child);if(!child.parents.has(parent))child.parents.set(parent,new Set());child.parents.get(parent).add(idx)
  }
  M.event("transactions");
  if(this.auditTransactions){
   for(const [p] of shadow){
    if(!p.actions)continue;
    let lo=0,hi=0;
    for(const a of p.actions){
     const z=direct19(a,new Map());ok(Math.abs(z.L-a.r.L)<1e-10&&Math.abs(z.U-a.r.U)<1e-10,"cached action sum");M.event("rangeAuditChecks");lo=Math.max(lo,z.L);hi=Math.max(hi,z.U)
    }
    ok(p.L>=lo-1e-10&&p.U<=hi+1e-10&&p.L<=p.U+EPS,"backed node intersection");
   }
  }
 }
 tighten(n,U){
  const u=Math.max(n.L,Math.min(n.U,U));
  ok(U>=n.L-EPS,"tightened below lower");
  const strict=n.U-u>EPS;
  if(n.parents?.size||n.actions)this.transaction(n,n.L,u);
  else n.U=u;
  if(strict)this.M.event("strictTightens");
 }
 expand(n){
  ok(n.actions===null,"expand once");
  const was=n.prepared,raw=was??this.raw(n,false),as=[],links=[];
  for(const a of raw){
   if(was)this.M.take("traverseNode");
   const os=[];
   for(const o of a.os){
    if(was){this.M.take("traverseEdge");this.M.event("reusedOutcomes")}
    os.push(o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:this.node(o.s,n.b-1)});
   }
   const aa={a:a.a,os};aa.r=direct19(aa,new Map(),this.M);
   const idx=as.length;as.push(aa);
   for(const o of os)if(!o.hit)links.push({child:o.n,parent:n,idx});
  }
  this.transaction(n,n.L,n.U,as,links);
  n.prepared=null;if(!was)this.edges+=as.reduce((s,a)=>s+a.os.length,0);
  this.peakEdges=Math.max(this.peakEdges,this.edges);this.M.event("expansions");
 }
 graphSolve(s,b,initial=null){
  let snap=initial;
  try{
   const root=this.node(s,b);if(!root.actions)this.expand(root);
   for(;;){
    this.refresh(root);const as=this.choices(root),g=snapshot19(as,root);
    snap=initial?better19(snap,g):g;if(g.certified){snap=g;break}
    const n=this.leaf(root,true);if(!n)break;
    if(this.variant==="incLazy"&&n.tier===0)this.tightenDL(n);
    else if(this.variant==="incLazy"&&n.tier===1)this.warm(n,true);
    else if(this.variant==="incAdaptive"&&n.tier<2&&n.U-n.L>=.10&&affordable(this.P,n.s,n.b).length>=2){
     this.M.event("adaptiveWarm");this.warm(n,true)
    }else this.expand(n);
   }
  }catch(e){if(e!==STOP)throw e;this.M.event("aborted")}
  return snap;
 }
 solve(s,b,fallback){
  this.M.event("decisions");let cheap=null;
  if(["incCheap","incAdaptive"].includes(this.variant)){
   try{cheap=cheapRoot19(this.P,s,b,this.M).snap}
   catch(e){if(e!==STOP)throw e;this.M.event("aborted");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  }
  const r=cheap?.certified?cheap:this.graphSolve(s,b,cheap);
  if(!r){this.M.event("fallback");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(r===cheap)this.M.event("cheapSelected");if(r.certified)this.M.event("certified");return r;
 }
}
function copyInc19(root,meter){
 const cache=new Map();
 function rec(n){
  if(cache.has(n.key))return cache.get(n.key);
  meter.take("copyNode");const c={s:n.s.slice(),b:n.b,key:n.key,L:n.L,U:n.U,tier:n.tier,actions:null,prepared:null,parents:new Map()};cache.set(c.key,c);
  if(n.actions)c.actions=n.actions.map((a,i)=>({a:{...a.a},r:{...a.r},os:a.os.map(o=>{
   meter.take("copyEdge");if(o.hit)return {p:o.p,hit:true,n:null};
   const child=rec(o.n);meter.take("traverseEdge");
   if(!child.parents.has(c))child.parents.set(c,new Set());child.parents.get(c).add(i);
   return {p:o.p,hit:false,n:child};
  })}));
  else if(n.prepared)c.prepared=n.prepared.map(a=>({a:{...a.a},os:a.os.map(o=>{meter.take("copyEdge");return {p:o.p,hit:o.hit,s:o.s?.slice()??null}})}));
  return c;
 }
 try{rec(root);cache.edgeCount=meter.c.copyEdge;return cache}catch(e){if(e!==STOP)throw e;meter.event("copyAborts");return null}
}
class Two19 extends Planner{
 solve(s,b,fallback){
  this.M.event("decisions");let cheap=null,snap=null;
  try{
   const c=cheapRoot19(this.P,s,b,this.M);cheap=c.snap;snap=cheap;
   if(cheap.certified){this.M.event("cheapSelected");this.M.event("certified");return cheap}
   const memo=new Map();
   const h1=(s,b)=>{
    if(b<=0)return 0;
    this.M.take("lookup");const k=key(s,b);if(memo.has(k))return memo.get(k);
    const raw=this.raw({s,b},false);let v=0;
    for(const a of raw){this.M.take("rangeEval");let q=0;for(const o of a.os){this.M.take("rangeOutcome");q+=o.p*(o.hit?1:this.alloc(o.s,b-1))}v=Math.max(v,q)}
    memo.set(k,v);return v;
   };
   const rows=[];
   for(const a of c.raw){
    this.M.take("rangeEval");let L=0;for(const o of a.os){this.M.take("rangeOutcome");L+=o.p*(o.hit?1:h1(o.s,b-1))}
    const old=c.rows.find(x=>x.a.id===a.a.id);
    rows.push({a:a.a,L:clip(Math.max(old.L,L)),U:old.U});
   }
   const z=snapshot19(rows);this.M.event("twoStepSnapshots");snap=better19(cheap,z);if(snap===z)this.M.event("twoStepSelected");
  }catch(e){if(e!==STOP)throw e;this.M.event("aborted")}
  if(!snap){this.M.event("fallback");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap===cheap)this.M.event("cheapSelected");if(snap.certified)this.M.event("certified");return snap;
 }
}
function policy19(root,cap,budget,total,mode,oracle,doAudit){
 const P=new Problem(root,cap),pre=setup(P),inc=mode.startsWith("inc"),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakNodes:0,peakEdges:0,maxUsed:0};
 let transactionChecks=0;
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank19(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,b)=>b.id-a.id)[0];
  const meter=meter19(Math.min(left,Math.ceil(2*left/b)));
  const planner=inc?new Inc19(P,meter,mode,retained,doAudit):mode==="metered2"?new Two19(P,meter,"prophet",null):new Planner(P,meter,mode==="fullLazy"?"lazy":"deadline",retained);
  const r=planner.solve(s,b,fallback);
  // If the cheap ranking itself was interrupted, preserve the common fallback.
  if(!r.ranges&&inc&&["incCheap","incAdaptive"].includes(mode)&&meter.c.fallback===0)meter.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));
  let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"oracle regret interval");
  if(r.certified)ok(regret<=EPS+1e-9,"certified regret");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakNodes=Math.max(audit.peakNodes,planner.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,planner.peakEdges);
  transactionChecks+=meter.c.rangeAuditChecks;
  const work={...meter.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let value=0,calls=1,used=meter.used,maxUsed=meter.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){
   if(o.hit){value+=o.p;continue}
   const cm=meter19(left-meter.used);let keep=null;
   if(r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=inc?copyInc19(o.n,cm):copyGraph(o.n,cm);
   addWork(work,cm.c,o.p);
   const q=rec(o.n.s,o.n.b,left-meter.used-cm.used,keep);
   value+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(cm.used+q.used);maxUsed=Math.max(maxUsed,meter.used+cm.used+q.maxUsed);addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"trajectory work/call ceiling");
  ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"weighted ledger identity");
  return {v:value,calls,work,maxUsed,used};
 }
 const r=rec(P.initial(),budget,total,null),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");
 audit.maxUsed=r.maxUsed;return {...r,regret,audit,pre,transactionChecks};
}
function unlimited19(root,cap,b,oracle){
 let checks=0,maxRegret=0,maxValueError=0;
 for(const mode of ["deadline","lazy"]){
  const P=new Problem(root,cap);setup(P);const Q=new Problem(root,cap);setup(Q);
  const a=new Planner(P,meter19(Infinity),mode,null),c=new Inc19(Q,meter19(Infinity),mode==="lazy"?"incLazy":"incDeadline",null,true);
  const f=P.legal(P.initial(),b)[0],g=Q.legal(Q.initial(),b)[0];
  const r=a.solve(P.initial(),b,f),z=c.solve(Q.initial(),b,g),o=oracle.rec(oracle.P.initial(),b);
  const q=new Map(o.qs.map(x=>[x.a.id,x.q])),regret=Math.max(o.v-q.get(r.a.id),o.v-q.get(z.a.id)),err=Math.max(Math.abs(r.L-o.v),Math.abs(z.L-o.v));
  ok(r.certified&&z.certified&&regret<1e-9&&err<1e-9,"unlimited full/incremental equivalence");
  checks++;maxRegret=Math.max(maxRegret,regret);maxValueError=Math.max(maxValueError,err);
 }
 return {checks,maxRegret,maxValueError};
}
function cohort19(name){
 if(name==="standard")return {n:48,seed:2520001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:24,seed:2530001,cap:2,b:8,stages:4};
 return {n:32,seed:2540001,cap:1,b:5,stages:4};
}
function experiment19(name){
 const start=Date.now(),{n,seed,cap,b,stages}=cohort19(name),modes=["fullDeadline","fullLazy","incDeadline","incLazy","incCheap","incAdaptive","metered2"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]};
 const check={unlimitedChecks:0,maxRegret:0,maxValueError:0,transactionChecks:0};
 for(let i=0;i<n;i++){
  const root=rootFor(name,seed+i,stages),P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);
  ref.optimal.push(opt.v);const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(i<4){const a=unlimited19(root,cap,b,oracle);check.unlimitedChecks+=a.checks;check.maxRegret=Math.max(check.maxRegret,a.maxRegret);check.maxValueError=Math.max(check.maxValueError,a.maxValueError)}
  for(const total of limits)for(const mode of modes){
   const r=policy19(root,cap,b,total,mode,oracle,i<2);all[mode+total].push(r);check.transactionChecks+=r.transactionChecks;
  }
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const k of keys){
  const a=all[k],work=Object.fromEntries(Object.keys(blank19()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}});
 }
 for(const t of limits)for(const [k,r] of [["incDeadline","fullDeadline"],["incLazy","fullLazy"],["incCheap","incDeadline"],["incAdaptive","incCheap"],["metered2","fullDeadline"],["metered2","incCheap"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);
  paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0190000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite synthetic model, weighted planning proxy",name,roots:n,cap,budget:b,check,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-start};
}
export {blank19,meter19,snapshot19,cheapValue19,cheapRoot19,Inc19,Two19,policy19,experiment19};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const cohortName19=process.argv.includes("--deep")?"deep":process.argv.includes("--tight")?"tight":"standard";
 console.log(JSON.stringify(experiment19(cohortName19),null,2));
}
