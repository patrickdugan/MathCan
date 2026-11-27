import {pathToFileURL} from "node:url";
// CRD-22: metered whole-action order and bounded exact memo policy.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {align16} from "./persistent_symmetry.mjs";
import {EPS,quant,key,STOP,charges,setup,affordable,Planner,addWork,rootFor} from "./metered_refinement.mjs";
import {snapshot19,cheapRoot19,policy19} from "./incremental_refinement.mjs";
import {meter21} from "./indexed_refinement.mjs";
import {reference20} from "./progressive_refinement.mjs";

const ev22=["cacheMisses","cacheTouches","victimScans","cacheCopies","cacheCopyAborts","orderCost","estimatedTotal","actualTotal","completedCostPairs","concordant","discordant","costTies","skippedActions","usefulWhole","attemptedWhole"];
function meter22(limit){const m=meter21(limit);Object.assign(m.c,Object.fromEntries(ev22.map(k=>[k,0])));return m}
const blank22=()=>meter22(0).c;
const specs22={
 cheap128:{order:"cheap",cap:128,eviction:"fifo"},gap128:{order:"gap",cap:128,eviction:"fifo"},ratio128:{order:"ratio",cap:128,eviction:"fifo"},
 cheap32:{order:"cheap",cap:32,eviction:"fifo"},cheap8:{order:"cheap",cap:8,eviction:"fifo"},lru32:{order:"cheap",cap:32,eviction:"lru"},lru8:{order:"cheap",cap:8,eviction:"lru"},
 persist32:{order:"cheap",cap:32,eviction:"lru",persistent:true},ratio32:{order:"ratio",cap:32,eviction:"fifo"}
};
class Cache22{
 constructor(M,spec,old=null){
  this.M=M;this.spec=spec;this.v=new Float64Array(spec.cap);this.t=new Float64Array(spec.cap);this.keys=Array(spec.cap);this.index=new Map();this.next=0;this.clock=0;this.size=0;
  if(old){
   this.next=old.next;this.clock=old.clock;this.size=old.size;
   for(let i=0;i<old.keys.length;i++)if(old.keys[i]!==undefined){this.keys[i]=old.keys[i];this.index.set(this.keys[i],i);this.v[i]=old.v[i];this.t[i]=old.t[i]}
  }
  M.c.memoPeak=Math.max(M.c.memoPeak,this.size);
 }
 map(prefix){
  const c=this;return {has(k){const found=c.index.has(prefix+k);if(!found)c.M.event("cacheMisses");return found},get(k){
   const i=c.index.get(prefix+k);ok(i!==undefined,"cache miss get");
   if(c.spec.eviction==="lru"){c.M.take("traverseEdge");c.M.event("cacheTouches");c.t[i]=++c.clock}
   c.M.event("memoHits");return c.v[i]
  },set(k,v){c.set(prefix+k,v);return this}};
 }
 set(k,v){
  const M=this.M;M.take("nodeInit");
  let i=this.index.get(k),existing=i!==undefined;
  if(!existing){
   if(this.spec.eviction==="fifo")i=this.next;
   else if(this.size<this.spec.cap)i=this.size;
   else{
    i=0;
    for(let j=0;j<this.spec.cap;j++){M.take("lookup");M.event("victimScans");if(this.t[j]<this.t[i])i=j}
   }
   if(this.keys[i]!==undefined)M.take("traverseEdge");
  }
  // All charges precede mutation, including eviction scan.
  if(!existing){
   if(this.keys[i]!==undefined){this.index.delete(this.keys[i]);M.event("memoEvictions")}else this.size++;
   if(this.spec.eviction==="fifo")this.next=(i+1)%this.spec.cap;
   this.keys[i]=k;this.index.set(k,i);
  }
  this.v[i]=v;this.t[i]=++this.clock;M.event("memoWrites");M.c.memoPeak=Math.max(M.c.memoPeak,this.size);
  ok(this.index.size===this.size&&this.size<=this.spec.cap,"cache capacity");
 }
 clone(M){
  try{
   for(const k of this.keys)if(k!==undefined){M.take("copyNode");M.take("copyEdge");M.event("cacheCopies")}
   return new Cache22(M,this.spec,this);
  }catch(e){if(e!==STOP)throw e;M.event("cacheCopyAborts");return null}
 }
}
class Order22 extends Planner{
 constructor(P,M,spec,retained){
  super(P,M,"prophet",null);this.spec=spec;this.memo22=new Cache22(M,spec,retained);this.lv=this.memo22.map("L:");this.av=this.memo22.map("A:");this.hm=this.memo22.map("H:");
 }
 h1(s,b){
  if(b<=0)return 0;this.M.take("lookup");const k=key(s,b);if(this.hm.has(k))return this.hm.get(k);
  let v=0;for(const a of this.raw({s,b},false)){
   this.M.take("rangeEval");let q=0;for(const o of a.os){this.M.take("rangeOutcome");q+=o.p*(o.hit?1:this.alloc(o.s,b-1))}
   v=Math.max(v,q);
  }this.hm.set(k,v);return v;
 }
 estimate(os,b){
  const M=this.M;let cost=1;
  for(const o of os){
   M.take("rangeOutcome");cost++;
   if(o.hit||b<=0)continue;
   const as=this.P.legal(o.s,b);let F=1;
   for(const x of affordable(this.P,o.s,b)){M.take("option");F+=4*b+2**x.m*3*x.m}
   for(const a of as){M.take("actionEnum");cost+=1+F}
  }
  return cost;
 }
 solve(s,b,fallback,finish=false){
  const M=this.M;M.event("decisions");let snap=null,cheap=null,pairs=[];
  try{
   const c=cheapRoot19(this.P,s,b,M);snap=cheap=c.snap;
   const rows=c.rows.map(x=>({...x})),order=[];
   if(!snap.certified||finish){
    const begin=M.used;
    for(let i=0;i<rows.length;i++){
     M.take("rangeEval");const r=rows[i],gap=Math.max(0,r.U-cheap.bestL);
     const cost=this.spec.order==="ratio"?this.estimate(c.raw[i].os,b-1):null;
     const score=this.spec.order==="cheap"?r.L:this.spec.order==="gap"?gap:gap/(cost??1);
     order.push({i,score,cost});
    }
    order.sort((a,c)=>{M.take("lookup");return quant(c.score)-quant(a.score)||rows[c.i].a.id-rows[a.i].a.id});
    M.event("orderCost",M.used-begin);
    for(const task of order){
     if(snap.certified&&!finish)break;
     const i=task.i;
     M.take("rangeEval");
     if(!finish&&rows[i].U+EPS<snap.bestL){M.event("skippedActions");continue}
     M.event("attemptedWhole");const before=M.used;
     M.take("rangeEval");let v=0;
     for(const o of c.raw[i].os){M.take("rangeOutcome");v+=o.p*(o.hit?1:this.h1(o.s,b-1))}
     const L=Math.max(rows[i].L,v);ok(L<=rows[i].U+EPS,"whole lower");
     for(const row of rows)M.take("rangeEval");
     rows[i]={...rows[i],L:Math.min(rows[i].U,L)};
     snap=snapshot19(rows);M.event("wholeCompleted");
     if(task.cost!==null){
      const actual=M.used-before;pairs.push([task.cost,actual]);M.event("estimatedTotal",task.cost);M.event("actualTotal",actual);M.event("completedCostPairs");
     }
    }
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  // Cost-rank diagnostics are evaluator-only: no decisions depend on pairs.
  for(let i=0;i<pairs.length;i++)for(let j=0;j<i;j++){
   const d=(pairs[i][0]-pairs[j][0])*(pairs[i][1]-pairs[j][1]);
   M.event(d>0?"concordant":d<0?"discordant":"costTies");
  }
  if(!snap){M.event("fallback");return {a:fallback,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap.bestL>cheap.bestL+EPS)M.event("usefulWhole");if(snap.certified)M.event("certified");return snap;
 }
}
function unit22(){
 let checks=0,evictions=0;
 for(const ev of ["fifo","lru"])for(const cap of [8,32,128]){
  const M=meter22(Infinity),spec={cap,eviction:ev},c=new Cache22(M,spec),m=c.map("L:"),ref=new Map();
  for(let j=0;j<3*cap;j++){
   const k=String(j);m.set(k,j+.125);ref.set(k,j+.125);
   if(ref.size>cap)ref.delete(ref.keys().next().value);
   // Only touch in insertion order, so reference FIFO and LRU coincide.
   for(const [k,v] of ref){ok(m.has(k)&&m.get(k)===v,"memo live");checks++}
   ok(c.size===ref.size&&c.v.byteLength+c.t.byteLength===16*cap,"numeric bytes");checks++;
  }
  evictions+=M.c.memoEvictions;
  const copy=c.clone(meter22(Infinity));ok(copy.size===c.size&&copy.clock===c.clock,"clone metadata");checks++;
  for(const [k,v] of ref){ok(copy.map("L:").get(k)===v,"clone value");checks++}
  // Abort precisely before eviction mutation: one write charge, zero victim/eviction room.
  const B=meter22(1);const z=new Cache22(B,spec,c);
  try{z.set("new",42);throw Error("expected abort")}catch(e){if(e!==STOP)throw e}
  ok(z.size===c.size&&!z.index.has("new")&&z.keys.every((k,i)=>k===c.keys[i]),"atomic full eviction abort");checks++;
 }
 // Distinct LRU fixture: touch the oldest, then ensure it survives.
 const M=meter22(Infinity),l=new Cache22(M,{cap:8,eviction:"lru"}),q=l.map("L:");
 for(let i=0;i<8;i++)q.set(String(i),i);q.get("0");q.set("8",8);ok(q.has("0")&&!q.has("1"),"LRU touch");checks++;
 return {checks,evictions};
}
function complete22(root,cap,b){
 const Q=new AllocationProblem(root,cap);setup(Q);const ref=reference20(Q,Q.initial(),b);
 let checks=0,error=0,evictions=0;
 for(const k of ["cheap128","ratio128","cheap8","lru8","persist32"]){
  const P=new Problem(root,cap);setup(P);const M=meter22(Infinity),g=new Order22(P,M,specs22[k],null);
  const r=g.solve(P.initial(),b,P.legal(P.initial(),b)[0],true);
  for(const a of r.ranges){const q=ref.find(x=>x.id===a.id),e=Math.abs(a.L-q.L);ok(e<1e-10,"complete H2 equivalence "+JSON.stringify({k,a,q,e}));checks++;error=Math.max(error,e)}
  evictions+=M.c.memoEvictions;
 }return {checks,error,evictions};
}
function policy22(root,cap,budget,total,mode,oracle){
 const spec=specs22[mode],P=new Problem(root,cap),pre=setup(P),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakMemo:0,evictions:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank22(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,b)=>b.id-a.id)[0];
  const M=meter22(Math.min(left,Math.ceil(2*left/b))),g=new Order22(P,M,spec,retained),r=g.solve(s,b,fallback);
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);
  ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakMemo=Math.max(audit.peakMemo,M.c.memoPeak);audit.evictions+=M.c.memoEvictions;
  ok(g.memo22.size<=spec.cap&&audit.peakMemo<=spec.cap,"memo cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  for(const o of P.outcomes(s,r.a)){
   if(o.hit){v+=o.p;continue}
   const C=meter22(left-M.used);let copy=null;
   if(spec.persistent&&b>1&&P.legal(o.s,b-1).length)copy=g.memo22.clone(C);
   addWork(work,C.c,o.p);
   const q=rec(o.s,b-1,left-M.used-C.used,copy);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceilings");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),budget,total,null),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");
 return {...r,regret,audit,pre};
}
function cohort22(name){
 if(name==="standard")return {n:40,seed:2820001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:20,seed:2830001,cap:2,b:8,stages:4};
 return {n:24,seed:2840001,cap:2,b:6,stages:2};
}
function experiment22(name){
 const start=Date.now(),{n,seed,cap,b,stages}=cohort22(name),modes=["metered2","incCheap",...Object.keys(specs22)],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]};
 const audit={unit:unit22(),unlimitedRoots:0,unlimitedActions:0,unlimitedEvictions:0,maxError:0};
 for(let i=0;i<n;i++){
  const root=name==="population"?fixture(seed+i,5,2):rootFor(name,seed+i,stages),P=new Problem(root,cap);setup(P);
  const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);ref.optimal.push(opt.v);
  const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(i<2){const u=complete22(root,cap,b);audit.unlimitedRoots++;audit.unlimitedActions+=u.checks;audit.unlimitedEvictions+=u.evictions;audit.maxError=Math.max(audit.maxError,u.error)}
  for(const t of limits)for(const mode of modes){
   const r=mode in specs22?policy22(root,cap,b,t,mode,oracle):policy19(root,cap,b,t,mode,oracle,false);
   r.work={...blank22(),...r.work};all[mode+t].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const t of limits)for(const mode of modes){
  const k=mode+t,a=all[k],work=Object.fromEntries(Object.keys(blank22()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0)),spec=specs22[mode];
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:spec?16*spec.cap:null,costRankTau:work.concordant+work.discordant>0?(work.concordant-work.discordant)/(work.concordant+work.discordant):null,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakMemo:spec?max("peakMemo"):null,offlineEvictions:spec?sum(a.map(x=>x.audit.evictions)):null}});
 }
 for(const t of limits)for(const [k,r] of [["ratio128","cheap128"],["ratio128","gap128"],["gap128","cheap128"],["cheap32","cheap128"],["cheap8","cheap128"],["lru32","cheap32"],["lru8","cheap8"],["persist32","lru32"],["ratio32","cheap32"],["cheap128","metered2"],["ratio128","metered2"],["persist32","incCheap"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0220000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite independent synthetic model, metered work proxy and numeric cache payload",name,roots:n,cap,budget:b,audit,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-start};
}
export {meter22,blank22,specs22,Cache22,Order22,policy22,complete22,experiment22};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const name22=process.argv.includes("--deep")?"deep":process.argv.includes("--population")?"population":"standard";
 console.log(JSON.stringify(experiment22(name22),null,2));
}
