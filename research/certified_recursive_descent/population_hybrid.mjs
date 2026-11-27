// CRD-23: population-aware H2/incremental hybrid and charged linked LRU.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {desc16,align16} from "./persistent_symmetry.mjs";
import {EPS,quant,clip,key,STOP,charges,setup,affordable,deadline,Planner,addWork} from "./metered_refinement.mjs";
import {snapshot19,cheapRoot19,Inc19,copyInc19,policy19} from "./incremental_refinement.mjs";
import {reference20} from "./progressive_refinement.mjs";
import {meter22,policy22} from "./cost_ordered_actions.mjs";

const ev23=["linkWrites","filterScans","filterChecks","h2Attempts","h2Complete","h2Units","h2Abort","h1Seeds","capacityCalls","capacityStrict","capacityOutcomes","mergedSnapshots"];
function meter23(limit){const m=meter22(limit);Object.assign(m.c,Object.fromEntries(ev23.map(k=>[k,0])));return m}
const blank23=()=>meter23(0).c;
class Linked23{
 constructor(M,cap=32,entries=[]){
  this.M=M;this.cap=cap;this.v=new Float64Array(cap);this.prev=new Int32Array(cap).fill(-1);this.next=new Int32Array(cap).fill(-1);
  this.keys=Array(cap);this.index=new Map();this.head=-1;this.tail=-1;this.size=0;
  // Entries are copied MRU to LRU, all copy charges paid by source.
  for(const [k,v] of entries){const i=this.size++;ok(i<cap,"restore cap");this.keys[i]=k;this.index.set(k,i);this.v[i]=v;this.prev[i]=this.tail;if(this.tail>=0)this.next[this.tail]=i;else this.head=i;this.tail=i}
  M.c.memoPeak=Math.max(M.c.memoPeak,this.size);
 }
 detach(i){
  const p=this.prev[i],n=this.next[i];
  if(p>=0)this.next[p]=n;else this.head=n;
  if(n>=0)this.prev[n]=p;else this.tail=p;
 }
 front(i){
  this.prev[i]=-1;this.next[i]=this.head;
  if(this.head>=0)this.prev[this.head]=i;else this.tail=i;
  this.head=i;
 }
 move(i){if(i!==this.head){this.detach(i);this.front(i)}}
 map(prefix){
  const c=this;return {has(k){const hit=c.index.has(prefix+k);if(!hit)c.M.event("cacheMisses");return hit},get(k){
   const i=c.index.get(prefix+k);ok(i!==undefined,"get miss");const move=i!==c.head;
   c.M.take("traverseEdge",1+(move?6:0));c.M.event("cacheTouches");if(move)c.M.event("linkWrites",6);
   c.move(i);c.M.event("memoHits");return c.v[i]
  },set(k,v){c.set(prefix+k,v);return this}};
 }
 set(k,v){
  const M=this.M;M.take("nodeInit");
  let i=this.index.get(k),existing=i!==undefined;
  const full=!existing&&this.size===this.cap;
  if(!existing)i=full?this.tail:this.size;
  const writes=existing?(i===this.head?0:6):(full?6:4);
  M.take("traverseEdge",writes+(full?1:0));M.event("linkWrites",writes);
  // All writes and eviction charges paid before mutation.
  if(existing)this.move(i);
  else{
   if(full){this.detach(i);this.index.delete(this.keys[i]);M.event("memoEvictions")}else this.size++;
   this.keys[i]=k;this.index.set(k,i);this.front(i);
  }
  this.v[i]=v;M.event("memoWrites");M.c.memoPeak=Math.max(M.c.memoPeak,this.size);
  ok(this.index.size===this.size&&this.size<=this.cap,"linked cache capacity");
 }
 entries(){
  const out=[];for(let i=this.head;i>=0;i=this.next[i]){ok(out.length<this.cap,"cycle");out.push([this.keys[i],this.v[i]])}
  ok(out.length===this.size,"list size");return out;
 }
 validate(){
  const seen=new Set();let p=-1,n=0;
  for(let i=this.head;i>=0;i=this.next[i]){ok(!seen.has(i)&&this.prev[i]===p&&this.index.get(this.keys[i])===i,"linked invariant");seen.add(i);p=i;n++}
  ok(p===this.tail&&n===this.size&&this.v.byteLength+this.prev.byteLength+this.next.byteLength===this.cap*16,"linked endpoints and bytes");return n;
 }
 selective(P,s,b,M,audit=false){
  if(this.size===0)return [];
  try{
   const allowed=new Set();
   for(const x of affordable(P,s,b)){
    M.take("lookup");const d=desc16(P,x.i,x.id);
    for(let t=x.m+1;t<=b;t++){M.take("option");allowed.add("L:"+d+":"+t)}
   }
   const out=[];
   for(let i=this.head;i>=0;i=this.next[i]){
    M.take("traverseNode");M.take("lookup");M.event("filterScans");
    if(allowed.has(this.keys[i])){M.take("copyNode");M.take("copyEdge");out.push([this.keys[i],this.v[i]]);M.event("cacheCopies")}
   }
   if(audit){
    const expected=this.entries().filter(([k])=>{
     if(!k.startsWith("L:"))return false;
     const end=k.lastIndexOf(":"),d=k.slice(2,end),t=Number(k.slice(end+1));
     return s.some((id,i)=>id>=0&&desc16(P,i,id)===d&&P.local[i].L-P.local[i].at(id).stage+1<=t&&t<=b);
    });
    ok(JSON.stringify(expected)===JSON.stringify(out),"selective filter reference");M.event("filterChecks");
   }
   return out;
  }catch(e){if(e!==STOP)throw e;M.event("cacheCopyAborts");return []}
 }
}
function attach23(P,M,owner,retained=[]){
 owner.memo23=new Linked23(M,32,retained);
 owner.lv=owner.memo23.map("L:");owner.av=owner.memo23.map("A:");owner.dv=owner.memo23.map("D:");owner.hm=owner.memo23.map("H:");
}
function h123(G,s,b){
 if(b<=0)return 0;const M=G.M,k=key(s,b);M.take("lookup");if(G.hm.has(k))return G.hm.get(k);
 let v=0;
 for(const a of G.raw({s,b},false)){
  M.take("rangeEval");let q=0;for(const o of a.os){M.take("rangeOutcome");q+=o.p*(o.hit?1:G.alloc(o.s,b-1))}
  v=Math.max(v,q);
 }
 G.hm.set(k,v);return v;
}
function h223(G,os,b){
 G.M.take("rangeEval");let v=0;for(const o of os){G.M.take("rangeOutcome");v+=o.p*(o.hit?1:h123(G,o.s,b-1))}
 return v;
}
function capEligible23(P,s,b){return P.active(s).length===P.cap&&affordable(P,s,b).some(x=>x.id===0)}
function capUpper23(P,s,b,M=null,dl=null){
 if(!capEligible23(P,s,b))return dl?dl(s,b):deadline(P,s,b,M);
 if(M)M.event("capacityCalls");
 const D=dl??((s,b)=>deadline(P,s,b,M));let v=0;
 for(const a of P.legal(s,b)){
  if(M){M.take("actionEnum");M.take("rangeEval")}
  let q=0;
  if(a.t===0){
   // First paid screen in the relaxed model. Preserve the original victim.
   if(M){M.take("outcomeGen",2);M.take("rangeOutcome",2);M.event("capacityOutcomes",2)}
   const f=P.local[a.i].at(s[a.i]).mass,next=s.slice();next[a.i]=-1;if(a.evict>=0)next[a.evict]=-1;
   q=f+(1-f)*D(next,b-1);
  }else{
   const count=P.local[a.i].outcomes(s[a.i],a.t).length;
   if(M){M.take("outcomeGen",count);M.event("capacityOutcomes",count)}
   for(const o of P.outcomes(s,a)){if(M)M.take("rangeOutcome");q+=o.p*(o.hit?1:D(o.s,b-1))}
  }
  v=Math.max(v,q);
 }
 return clip(v);
}
function handCap23(){
 const P=new Problem({seed:0,branches:[{prior:[1,1,1,1,1,1],sensors:[60]},{prior:[1,1,1,1,1,1],sensors:[60]},{prior:[1,1,1,1,1,1],sensors:[60,60]}]},2);
 setup(P);const s=P.initial();s[0]=P.local[0].intern(1,[1,0,0,1,0,0]);s[1]=P.local[1].intern(1,[1,0,0,1,0,0]);
 const u=capUpper23(P,s,3),d=deadline(P,s,3),v=new Engine(P,"optimal",null).rec(s,3).v;
 ok(Math.abs(u-.75)<EPS&&Math.abs(d-.875)<EPS&&v<=u+EPS,"cap-aware hand");
 return {u,d,v};
}
class Whole23 extends Planner{
 constructor(P,M,retained){super(P,M,"prophet",null);attach23(P,M,this,retained)}
 solve(s,b,fallback,finish=false){
  const M=this.M;M.event("decisions");let snap=null,cheap=null;
  try{
   const c=cheapRoot19(this.P,s,b,M);snap=cheap=c.snap;
   const rows=c.rows.map(x=>({...x})),order=[];const start=M.used;
   if(!snap.certified||finish){
    for(let i=0;i<rows.length;i++){M.take("rangeEval");order.push(i)}
    order.sort((i,j)=>{M.take("lookup");return quant(rows[j].L)-quant(rows[i].L)||rows[j].a.id-rows[i].a.id});
    M.event("orderCost",M.used-start);
    for(const i of order){
     if(snap.certified&&!finish)break;
     M.take("rangeEval");if(!finish&&rows[i].U+EPS<snap.bestL){M.event("skippedActions");continue}
     M.event("attemptedWhole");const q=h223(this,c.raw[i].os,b),L=Math.max(rows[i].L,q);ok(L<=rows[i].U+EPS,"whole bound");
     for(const r of rows)M.take("rangeEval");
     rows[i]={...rows[i],L:Math.min(L,rows[i].U)};snap=snapshot19(rows);M.event("wholeCompleted");
    }
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  if(!snap){M.event("fallback");return {a:fallback,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap.bestL>cheap.bestL+EPS)M.event("usefulWhole");if(snap.certified)M.event("certified");return snap;
 }
}
class Hybrid23 extends Inc19{
 constructor(P,M,mode,retained){
  super(P,M,"incCheap",retained,false);this.mode23=mode;attach23(P,M,this);
 }
 node(s,b){
  const k=key(s,b);this.M.take("lookup");const fresh=!this.cache.has(k),n=super.node(s,b);
  if(fresh){
   this.M.take("lookup");
   if(this.hm.has(k)){const v=this.hm.get(k);ok(v<=n.U+EPS,"H1 seed upper");if(v>n.L){n.L=Math.min(n.U,v);this.M.event("h1Seeds")}}
  }return n;
 }
 tightenDL(n){
  super.tightenDL(n);
  if(this.mode23==="hybridCap"&&n.U-n.L>EPS&&capEligible23(this.P,n.s,n.b)){
   const u=capUpper23(this.P,n.s,n.b,this.M,(s,b)=>this.dl(s,b)),old=n.U;
   this.tighten(n,u);if(old-n.U>EPS)this.M.event("capacityStrict");
  }
 }
 stage(s,b,c){
  const M=this.M,limit=M.limit,start=M.used;let snap=c.snap;
  M.limit=Math.min(limit,start+Math.floor(limit/4));
  try{
   let i=-1,score=-Infinity;
   for(let j=0;j<c.rows.length;j++){
    M.take("rangeEval");const a=c.rows[j],v=this.mode23==="hybridConst"?a.L:Math.max(0,a.U-c.snap.bestL);
    if(i<0||quant(v)>quant(score)||(quant(v)===quant(score)&&a.a.id>c.rows[i].a.id)){i=j;score=v}
   }
   if(i>=0){
    M.event("h2Attempts");const q=h223(this,c.raw[i].os,b),L=Math.max(c.rows[i].L,q);
    ok(L<=c.rows[i].U+EPS,"hybrid H2 lower");
    const rows=c.rows.slice();for(const a of rows)M.take("rangeEval");
    rows[i]={...rows[i],L:Math.min(rows[i].U,L)};snap=snapshot19(rows);M.event("h2Complete");
   }
  }catch(e){if(e!==STOP)throw e;M.event("h2Abort")}finally{M.limit=limit;M.event("h2Units",M.used-start)}
  return snap;
 }
 solve(s,b,fallback){
  const M=this.M;M.event("decisions");let snap=null,c;
  try{
   c=cheapRoot19(this.P,s,b,M);snap=c.snap;
   if(!snap.certified&&this.mode23!=="boundedInc")snap=this.stage(s,b,c);
   if(!snap.certified){
    const root=this.node(s,b);if(!root.actions)this.expand(root);
    for(;;){
     this.refresh(root);const as=this.choices(root),prev=new Map(snap.ranges.map(r=>[r.id,r])),rows=[];
     for(const a of as){
      M.take("rangeEval");const r=prev.get(a.a.id);ok(r,"merged action");
      const L=Math.max(r.L,a.L),U=Math.min(r.U,a.U);ok(L<=U+EPS,"merged envelope");
      rows.push({a:a.a,os:a.os,L:clip(L),U:clip(Math.max(L,U))});
     }
     snap=snapshot19(rows,root);M.event("mergedSnapshots");
     if(snap.certified)break;const n=this.leaf(root,true);if(!n)break;this.expand(n);
    }
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  if(!snap){M.event("fallback");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap.certified)M.event("certified");return snap;
 }
}
function unit23(){
 let checks=0,evictions=0;
 for(const cap of [8,32,128]){
  const M=meter23(Infinity),c=new Linked23(M,cap),map=c.map("L:"),ref=new Map(),r=rng(2950001+cap);
  for(let t=0;t<cap*8;t++){
   const k=String(Math.floor(r()*cap*3));
   if(ref.has(k)&&r()<.55){
    const v=ref.get(k);ok(map.has(k)&&map.get(k)===v,"linked hit");ref.delete(k);ref.set(k,v);
   }else{
    map.set(k,t+.25);ref.delete(k);ref.set(k,t+.25);if(ref.size>cap)ref.delete(ref.keys().next().value);
   }
   c.validate();ok(JSON.stringify(c.entries())===JSON.stringify([...ref].reverse().map(([k,v])=>["L:"+k,v])),"reference LRU");checks+=2;
  }
  evictions+=M.c.memoEvictions;
  const B=meter23(1),z=new Linked23(B,cap,c.entries());
  try{z.set("new",7);throw Error("expected quota abort")}catch(e){if(e!==STOP)throw e}
  ok(JSON.stringify(z.entries())===JSON.stringify(c.entries()),"atomic link write");checks++;
 }
 const P=new Problem(fixture(2950999,3,3),2);setup(P);const M=meter23(Infinity),c=new Linked23(M,32),s=P.initial(),b=4;
 for(const x of affordable(P,s,b))for(let t=x.m+1;t<=b;t++)c.set("L:"+desc16(P,x.i,x.id)+":"+t,x.mass);
 c.set("H:ignored",.5);c.set("A:ignored",.6);
 const copy=c.selective(P,s,b,M,true);ok(copy.length>0&&copy.every(([k])=>k.startsWith("L:"))&&M.c.filterChecks===1,"selective unit");checks++;
 return {checks,evictions,hand:handCap23()};
}
function complete23(root,cap,b){
 const Q=new AllocationProblem(root,cap);setup(Q);const ref=reference20(Q,Q.initial(),b);
 let checks=0,maxError=0;
 for(const mode of ["linked","hybrid"]){
  const P=new Problem(root,cap);setup(P);const M=meter23(Infinity),G=mode==="linked"?new Whole23(P,M,[]):new Hybrid23(P,M,"hybridGap",null);
  let rows;
  if(mode==="linked")rows=G.solve(P.initial(),b,P.legal(P.initial(),b)[0],true).ranges;
  else{const c=cheapRoot19(P,P.initial(),b,M);rows=c.rows.map((a,i)=>({id:a.a.id,L:Math.max(a.L,h223(G,c.raw[i].os,b))}))}
  for(const r of rows){const x=ref.find(a=>a.id===r.id),e=Math.abs(r.L-x.L);ok(e<EPS,"H2 completion");checks++;maxError=Math.max(maxError,e)}
 }
 return {checks,maxError};
}
function policy23(root,cap,budget,total,mode,oracle,auditFilter){
 const P=new Problem(root,cap),pre=setup(P),inc=mode==="boundedInc"||mode.startsWith("hybrid"),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakMemo:0,peakNodes:0,peakEdges:0,filterChecks:0};
 function rec(s,b,left,graph,entries){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank23(),used:0,maxUsed:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0];
  const M=meter23(Math.min(left,Math.ceil(2*left/b))),G=inc?new Hybrid23(P,M,mode,graph):new Whole23(P,M,entries??[]),r=G.solve(s,b,fallback);
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakMemo=Math.max(audit.peakMemo,M.c.memoPeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,G.peakEdges);
  ok(G.memo23.size<=32&&M.c.memoPeak<=32,"memo cap");if(auditFilter)G.memo23.validate();
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){
   if(o.hit){v+=o.p;continue}
   const C=meter23(left-M.used);let keep=null,copy=[];
   if(o.n.b>0&&P.legal(o.n.s,o.n.b).length){
    if(inc&&r.os)keep=copyInc19(o.n,C);
    if(mode==="carry32")copy=G.memo23.selective(P,o.n.s,o.n.b,C,auditFilter);
   }
   audit.filterChecks+=C.c.filterChecks;addWork(work,C.c,o.p);
   const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep,copy);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");
  return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),budget,total,null,[]),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre};
}
function cohort23(name){
 if(name==="standard")return {n:32,seed:2920001,pop:3,stages:3,b:6};
 if(name==="population")return {n:24,seed:2930001,pop:5,stages:2,b:6};
 return {n:16,seed:2940001,pop:7,stages:2,b:5};
}
function experiment23(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort23(name),cap=2,modes=["incCheap","metered2","ratio32","lru32","linked32","carry32","hybridConst","hybridGap","hybridCap","boundedInc"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]};
 const audit={unit:unit23(),completeRoots:0,completeActions:0,maxCompleteError:0,capacityChecks:0,capacityStrict:0,capacityMaxViolation:0,capacityMeanTighten:0,filterChecks:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),P=new Problem(root,cap);setup(P);
  const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);ref.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(i<2){
   const u=complete23(root,cap,b);audit.completeRoots++;audit.completeActions+=u.checks;audit.maxCompleteError=Math.max(audit.maxCompleteError,u.maxError);
   for(const x of [...oracle.memo.values()].filter(x=>x.s&&x.action&&capEligible23(P,x.s,x.b)).slice(0,128)){
    const d=deadline(P,x.s,x.b),u=capUpper23(P,x.s,x.b),v=Math.max(0,x.v-u,Math.min(d,u)-d);
    // capUpper itself may exceed unrestricted deadline; intersection is the bound.
    ok(x.v<=Math.min(d,u)+1e-9,"capacity upper audit");
    audit.capacityChecks++;audit.capacityStrict+=Number(d-u>EPS);audit.capacityMaxViolation=Math.max(audit.capacityMaxViolation,v);audit.capacityMeanTighten+=Math.max(0,d-u);
   }
  }
  for(const t of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,t,mode,oracle,false):["ratio32","lru32"].includes(mode)?policy22(root,cap,b,t,mode,oracle):policy23(root,cap,b,t,mode,oracle,i<2);
   r.work={...blank23(),...r.work};all[mode+t].push(r);audit.filterChecks+=r.audit.filterChecks??0;
  }
 }
 audit.capacityMeanTighten/=Math.max(1,audit.capacityChecks);
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const t of limits)for(const mode of modes){
  const k=mode+t,a=all[k],work=Object.fromEntries(Object.keys(blank23()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:512,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakMemo:max("peakMemo"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}});
 }
 for(const t of limits)for(const [k,r] of [["hybridGap","boundedInc"],["hybridGap","incCheap"],["hybridConst","hybridGap"],["hybridCap","hybridGap"],["boundedInc","incCheap"],["linked32","lru32"],["carry32","linked32"],["hybridGap","ratio32"],["hybridGap","metered2"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0230000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite independent synthetic model, shared work proxy and bounded numeric memo",name,roots:n,population:pop,cap,budget:b,audit,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-start};
}
const name23=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
console.log(JSON.stringify(experiment23(name23),null,2));
