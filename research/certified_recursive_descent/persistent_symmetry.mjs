import {pathToFileURL} from "node:url";
// CRD-16: exact symmetry quotient, sparse static allocation and trajectory DAG reuse.
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem,local14} from "./global_allocation.mjs";
import {Planner15,EPS15,key15,quant15} from "./selective_bellman.mjs";

function desc16(P,i,id){
 if(id<0)return "dead";
 const l=P.local[i],s=l.at(id);
 return JSON.stringify([id===0?"unopened":"active",s.w,l.spec.sensors.slice(s.stage).map((a,j)=>[Math.min(2,s.stage+j),a])]);
}
function canon16(P,s,b){
 const entries=s.map((id,i)=>({i,d:desc16(P,i,id)})).sort((a,b)=>a.d<b.d?-1:a.d>b.d?1:a.i-b.i);
 const pos=[];entries.forEach((e,j)=>pos[e.i]=j);
 return {key:JSON.stringify([b,entries.map(e=>e.d)]),pos,entries};
}
function action16(a,pos){return [pos[a.i],a.t,a.evict<0?-1:pos[a.evict]].join(":")}
function align16(P,s,Q){return s.map((id,i)=>id<0?id:Q.local[i].intern(P.local[i].at(id).stage,P.local[i].at(id).w))}
class Quotient16{
 constructor(P){this.P=P;this.memo=new Map();this.stats={states:0,actions:0,outcomes:0,hits:0,nonidenticalHits:0,canonicalizations:0}}
 solve(s,b){
  if(b<=0)return {v:0,table:new Map()};
  const c=canon16(this.P,s,b),label=key15(s,b);this.stats.canonicalizations++;
  if(this.memo.has(c.key)){
   this.stats.hits++;const z=this.memo.get(c.key);if(z.label!==label)this.stats.nonidenticalHits++;
   return z;
  }
  const table=new Map();let v=0;
  for(const a of this.P.legal(s,b)){
   const os=this.P.outcomes(s,a);this.stats.actions++;this.stats.outcomes+=os.length;
   const q=sum(os.map(o=>o.p*(o.hit?1:this.solve(o.s,b-1).v)));
   const k=action16(a,c.pos);ok(!table.has(k),"canonical action collision");table.set(k,q);v=Math.max(v,q);
  }
  const z={v,table,label};this.memo.set(c.key,z);this.stats.states++;return z;
 }
 qs(s,b){const c=canon16(this.P,s,b),z=this.solve(s,b);
  return {v:z.v,qs:this.P.legal(s,b).map(a=>({id:a.id,q:z.table.get(action16(a,c.pos))}))};
 }
}
function checkQuotient16(oracle,Q,all){
 const P=oracle.P,states=all?[...oracle.memo.values()]:[oracle.rec(P.initial(),Q.budget)];
 let count=0,actions=0,maxError=0;
 for(const r of states){
  if(!r.s)continue;
  const s=align16(P,r.s,Q.P),z=Q.qs(s,r.b);
  const d=Math.abs(z.v-r.v);ok(d<1e-10,"quotient value mismatch");maxError=Math.max(maxError,d);count++;
  const m=new Map(z.qs.map(a=>[a.id,a.q]));ok(m.size===r.qs.length,"quotient legal action count");
  for(const a of r.qs){
   const e=Math.abs(a.q-m.get(a.a.id));ok(Number.isFinite(e)&&e<1e-10,"quotient Q mismatch");maxError=Math.max(maxError,e);actions++;
  }
 }
 return {count,actions,maxError};
}

class Sparse16 extends AllocationProblem{
 constructor(root,cap,audit=false){
  super(root,cap);this.sparse=true;this.auditRef=audit?new AllocationProblem(root,cap):null;
  this.audit={checks:0,maxError:0};this.reset16();
 }
 reset16(){
  this.values=this.local.map(()=>new Map());this.allocCache=new Map();this.h1Cache=new Map();this.sharedValues=new Map();
  for(const k of Object.keys(this.work))this.work[k]=k==="minSlack"?Infinity:0;
  Object.assign(this.work,{optionCandidates:0,optionsKept:0,canonicalHits:0,localCanonicalHits:0});
 }
 val(i,id,b){
  const d=desc16(this,i,id),key=d+":"+b,label=i+":"+id+":"+b;
  if(this.sharedValues.has(key)){
   this.work.localHits++;const v=this.sharedValues.get(key);if(v.label!==label)this.work.localCanonicalHits++;return v.v;
  }
  this.work.localCalls++;const v=local14(this.local[i],id,b,this.work);
  this.sharedValues.set(key,{v,label});return v;
 }
 alloc(s,b){
  const c=canon16(this,s,b),label=key15(s,b);let out;
  if(this.allocCache.has(c.key)){
   this.work.allocHits++;out=this.allocCache.get(c.key);if(out.label!==label)this.work.canonicalHits++;
  }else{
   this.work.allocCalls++;
   let dp=Array(b+1).fill(1);
   for(const {i} of c.entries){
    const id=s[i],options=[{t:0,v:0}];this.work.optionCandidates++;
    if(id>=0){
     const l=this.local[i],v=l.at(id),m=l.L-v.stage;let last=0;
     for(let k=1;k<=3&&m+k<=b;k++){
      const t=m+k,value=this.val(i,id,t);this.work.optionCandidates++;
      if(value>last+1e-15){options.push({t,v:value});last=value}
     }
    }
    this.work.optionsKept+=options.length;
    const next=[];
    for(let r=0;r<=b;r++){
     this.work.allocCells++;let best=1;
     for(const o of options){if(o.t>r)break;this.work.allocCombinations++;best=Math.min(best,(1-o.v)*dp[r-o.t])}
     next.push(best);
    }
    dp=next;
   }
   out={v:1-dp[b],label};this.allocCache.set(c.key,out);
  }
  if(this.auditRef){
   const exact=this.auditRef.alloc(align16(this,s,this.auditRef),b).v,e=Math.abs(exact-out.v);
   ok(e<1e-10,"sparse allocation mismatch");this.audit.checks++;this.audit.maxError=Math.max(this.audit.maxError,e);
  }
  return out;
 }
}
class Dense16 extends AllocationProblem{
 reset16(){
  this.values=this.local.map(()=>new Map());this.allocCache=new Map();this.h1Cache=new Map();
  for(const k of Object.keys(this.work))this.work[k]=k==="minSlack"?Infinity:0;
 }
}

function copyReach16(root){
 const cache=new Map();let edges=0;
 function rec(n){
  if(cache.has(n.key))return cache.get(n.key);
  const c={s:n.s.slice(),b:n.b,key:n.key,L:n.L,U:n.U,parents:new Set(),actions:null};
  cache.set(c.key,c);
  if(n.actions!==null)c.actions=n.actions.map(a=>({a:{...a.a},os:a.os.map(o=>{
   edges++;if(o.hit)return {p:o.p,hit:true,n:null};
   const ch=rec(o.n);ch.parents.add(c);return {p:o.p,hit:false,n:ch};
  })}));
  return c;
 }
 const node=rec(root);return {cache,root:node,nodes:cache.size,edges};
}
class PersistentPlanner16 extends Planner15{
 constructor(P,limit,retained){super(P,limit);if(retained){this.cache=retained.cache;this.work.peakDAG=this.cache.size}}
 solve16(s,b){
  const root=this.node(s,b),reused=root.actions!==null;
  if(!reused)this.expand(root);
  ok(root.actions.length>0,"nonterminal root");
  let selected,gap,ranges;
  for(;;){
   const as=this.choices(root);
   selected=as[0];gap=Math.max(0,...as.map(a=>a.U-selected.L));
   ranges=as.map(a=>({id:a.a.id,L:a.L,U:a.U}));
   if(gap<=EPS15||this.work.nodeExpanded>=this.limit)break;
   const next=this.leaf(root,true);ok(next,"unresolved persistent leaf");this.work.leafSelections++;this.expand(next);
  }
  let edges=0;for(const n of this.cache.values())if(n.actions!==null)for(const a of n.actions)edges+=a.os.length;
  return {root,selected,action:selected.a,L:root.L,U:root.U,gap,ranges,reused,certified:gap<=EPS15,peakNodes:this.cache.size,peakEdges:edges};
 }
}
const effortKeys16=["decisions","certified","expansions","created","outcomes","backups","propagations","reverseLinks","allocCombinations","allocCalls","allocHits","localCalls","localHits","patterns","likelihoodProducts","optionCandidates","optionsKept","canonicalHits","localCanonicalHits","copyNodes","copyEdges","reusedExpandedRoots","gapSum","actualGapSum"];
const emptyEffort16=()=>Object.fromEntries(effortKeys16.map(k=>[k,0]));
function policy16(root,cap,budget,total,kind,oracle,auditSparse){
 const persistent=kind==="persistent",P=kind==="dense"?new Dense16(root,cap):new Sparse16(root,cap,auditSparse);
 const audit={visits:0,actionChecks:0,certified:0,maxViolation:0,maxRegret:0,maxGapViolation:0,maxBudgetUsed:0,peakNodes:0,peakEdges:0,sparseChecks:0,sparseMaxError:0};
 function rec(s,b,left,retained){
  if(b<=0||!P.legal(s,b).length)return {v:0,calls:0,evictions:0,work:emptyEffort16(),maxUsed:0,digest:"."};
  ok(left>=b,"reserved expansions");
  const quota=Math.min(16,left-(b-1));ok(quota>=1,"quota");
  P.reset16();const planner=new PersistentPlanner16(P,quota,retained),r=planner.solve16(s,b),w=planner.work,aw=P.work;
  ok(w.nodeExpanded<=quota,"quota exceeded");
  const o=oracle.rec(align16(P,s,oracle.P),b),qmap=new Map(o.qs.map(x=>[x.a.id,x.q]));
  ok(qmap.size===r.ranges.length,"legal actions");
  for(const a of r.ranges){
   const q=qmap.get(a.id),violation=Math.max(0,a.L-q,q-a.U);ok(Number.isFinite(q)&&violation<1e-9,"Q enclosure");
   audit.actionChecks++;audit.maxViolation=Math.max(audit.maxViolation,violation);
  }
  const violation=Math.max(0,r.L-o.v,o.v-r.U),regret=Math.max(0,o.v-qmap.get(r.action.id));
  ok(violation<1e-9&&regret<=r.gap+1e-9,"state/regret enclosure");
  if(r.certified)ok(regret<=EPS15+1e-9,"certified action");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxRegret=Math.max(audit.maxRegret,regret);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakNodes=Math.max(audit.peakNodes,r.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,r.peakEdges);
  const work=emptyEffort16();
  Object.assign(work,{decisions:1,certified:Number(r.certified),expansions:w.nodeExpanded,created:w.nodeCreated,outcomes:w.outcomes,backups:w.backups,propagations:w.propagations,reverseLinks:w.reverseLinks,allocCombinations:aw.allocCombinations,allocCalls:aw.allocCalls,allocHits:aw.allocHits,localCalls:aw.localCalls,localHits:aw.localHits,patterns:aw.patterns,likelihoodProducts:aw.likelihoodProducts,optionCandidates:aw.optionCandidates||0,optionsKept:aw.optionsKept||0,canonicalHits:aw.canonicalHits||0,localCanonicalHits:aw.localCanonicalHits||0,reusedExpandedRoots:Number(r.reused),gapSum:r.gap,actualGapSum:regret});
  let v=0,calls=1,evictions=Number(r.action.evict>=0),maxUsed=w.nodeExpanded,digest="("+r.action.id+":";
  for(const out of r.selected.os){
   if(out.hit){v+=out.p;digest+="H";continue}
   let keep=null;
   if(persistent&&out.n.b>0&&P.legal(out.n.s,out.n.b).length){
    keep=copyReach16(out.n);work.copyNodes+=out.p*keep.nodes;work.copyEdges+=out.p*keep.edges;
   }
   const z=rec(out.n.s,out.n.b,left-w.nodeExpanded,keep);
   v+=out.p*z.v;calls+=out.p*z.calls;evictions+=out.p*z.evictions;
   for(const k of effortKeys16)work[k]+=out.p*z.work[k];
   maxUsed=Math.max(maxUsed,w.nodeExpanded+z.maxUsed);digest+=z.digest;
  }
  ok(maxUsed<=left,"total planning cap");ok(calls<=b+1e-10,"environment cap");
  return {v,calls,evictions,work,maxUsed,digest:digest+")"};
 }
 const z=rec(P.initial(),budget,total,null),opt=oracle.rec(oracle.P.initial(),budget).v;
 ok(z.v<=opt+1e-9,"oracle dominance");const regret=opt-z.v;
 ok(Math.abs(regret-z.work.actualGapSum)<1e-9,"performance difference identity");
 ok(regret<=z.work.gapSum+1e-9,"expected regret bound");
 audit.maxBudgetUsed=z.maxUsed;
 if(P.audit){audit.sparseChecks=P.audit.checks;audit.sparseMaxError=P.audit.maxError}
 return {...z,regret,audit};
}
function cohort16(name){
 if(name==="standard")return {n:96,seed:2220001,cap:2,b:6,stages:3};
 if(name==="symmetry")return {n:48,seed:2230001,cap:1,b:6,stages:3};
 return {n:32,seed:2240001,cap:2,b:8,stages:4};
}
function root16(name,seed,stages){
 const r=fixture(seed,3,stages);
 if(name==="symmetry")r.branches=Array.from({length:3},()=>({prior:r.branches[0].prior.slice(),sensors:r.branches[0].sensors.slice()}));
 return r;
}
function experiment16(name){
 const begin=Date.now(),{n,seed,cap,b,stages}=cohort16(name),kinds=["dense16","sparse16","persistent16","dense48","sparse48","persistent48"],all=Object.fromEntries(kinds.map(k=>[k,[]]));
 const exact={labeledStates:0,labeledActions:0,labeledOutcomes:0,quotientStates:0,quotientActions:0,quotientOutcomes:0,hits:0,nonidenticalHits:0,canonicalizations:0,auditStates:0,auditActions:0,maxError:0};
 const sparse={rootChecks:0,queryChecks:0,maxError:0,digestChecks:0,digestMismatch:0,maxUtilityMismatch:0};
 const baselines={optimal:[],receding2:[]},recedingWork={allocCombinations:0,h1Outcomes:0,h2Outcomes:0,evalStates:0,evalTransitions:0};
 for(let i=0;i<n;i++){
  const root=root16(name,seed+i,stages),OP=new Problem(root,cap),oracle=new Engine(OP,"optimal",null),opt=oracle.rec(OP.initial(),b);
  const Q=new Quotient16(new Problem(root,cap));Q.budget=b;const q=Q.solve(Q.P.initial(),b);ok(Math.abs(q.v-opt.v)<1e-10,"root quotient equality");
  exact.labeledStates+=oracle.stats.states;exact.labeledActions+=oracle.stats.actions;exact.labeledOutcomes+=oracle.stats.transitions;
  for(const [k,v] of Object.entries(Q.stats)){const target={states:"quotientStates",actions:"quotientActions",outcomes:"quotientOutcomes"}[k]??k;exact[target]+=v}
  const a=checkQuotient16(oracle,Q,i<4);exact.auditStates+=a.count;exact.auditActions+=a.actions;exact.maxError=Math.max(exact.maxError,a.maxError);
  const dense=new AllocationProblem(root,cap),sp=new Sparse16(root,cap,false);
  for(let t=0;t<=b;t++){
   const err=Math.abs(dense.alloc(dense.initial(),t).v-sp.alloc(sp.initial(),t).v);
   ok(err<1e-10,"root sparse comparison");sparse.rootChecks++;sparse.maxError=Math.max(sparse.maxError,err);
  }
  const RP=new AllocationProblem(root,cap),R=new Engine(RP,"receding2",null),rr=R.rec(RP.initial(),b);
  baselines.optimal.push(opt.v);baselines.receding2.push(rr.v);
  for(const k of ["allocCombinations","h1Outcomes","h2Outcomes"])recedingWork[k]+=RP.work[k];
  recedingWork.evalStates+=R.stats.states;recedingWork.evalTransitions+=R.stats.transitions;
  const out={};
  for(const total of [16,48])for(const kind of ["dense","sparse","persistent"]){
   const key=kind+total,z=policy16(root,cap,b,total,kind,oracle,i<4&&kind!=="dense");out[key]=z;all[key].push(z);
   sparse.queryChecks+=z.audit.sparseChecks;sparse.maxError=Math.max(sparse.maxError,z.audit.sparseMaxError);
  }
  for(const t of [16,48]){
   const a=out["dense"+t],c=out["sparse"+t];sparse.digestChecks++;
   sparse.digestMismatch+=Number(a.digest!==c.digest);sparse.maxUtilityMismatch=Math.max(sparse.maxUtilityMismatch,Math.abs(a.v-c.v));
  }
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const kind of kinds){
  const a=all[kind],work=Object.fromEntries(effortKeys16.map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]));
  rows.push({kind,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedEvictions:mean(a.map(x=>x.evictions)),work,expectedCertificateRate:work.certified/work.decisions,maxUsed:Math.max(...a.map(x=>x.maxUsed)),peakNodes:max("peakNodes"),peakEdges:max("peakEdges"),audit:{visits:sum(a.map(x=>x.audit.visits)),actions:sum(a.map(x=>x.audit.actionChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxRegret:max("maxRegret"),maxGapViolation:max("maxGapViolation")}});
 }
 for(const total of [16,48])for(const ref of ["sparse"+total,"dense"+total,"receding2","optimal"]){
  const a=all["persistent"+total],other=baselines[ref]??all[ref].map(x=>x.v),d=a.map((x,i)=>x.v-other[i]);
  paired.push({kind:"persistent"+total,ref,...bootstrap(d,(0xC0160000+seed+total*100+["sparse"+total,"dense"+total,"receding2","optimal"].indexOf(ref))>>>0)});
 }
 return {status:"PASS",scope:"independent finite branch model; numeric work and exact expectation, not CPU/RSS",name,roots:n,cap,budget:b,exact,sparse,baselines:{optimal:mean(baselines.optimal),receding2:mean(baselines.receding2),recedingWork},rows,paired,elapsedMs:Date.now()-begin};
}
export {desc16,canon16,align16,Sparse16,copyReach16,PersistentPlanner16,effortKeys16,emptyEffort16,policy16,experiment16};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const cohort=process.argv.includes("--symmetry")?"symmetry":process.argv.includes("--stress")?"stress":"standard";
 console.log(JSON.stringify(experiment16(cohort),null,2));
}
