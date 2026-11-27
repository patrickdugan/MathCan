// CRD-21: indexed lower-envelope tasks, delta sums, streaming whole-action control.
import {ok,sum,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {align16} from "./persistent_symmetry.mjs";
import {EPS,quant,clip,key,STOP,charges,setup,Planner,addWork,rootFor} from "./metered_refinement.mjs";
import {snapshot19,cheapValue19,cheapRoot19,policy19} from "./incremental_refinement.mjs";
import {blank20,meter20,reference20,policy20} from "./progressive_refinement.mjs";

const ev21=["heapPush","heapPop","heapCompare","heapSwap","stalePops","dominatedPops","phaseBuilds","deltaUpdates","memoWrites","memoEvictions","memoHits","memoPeak","wholeCompleted","childCompleted","arenaBlocked","traceChecks","deltaAudit","usefulDecisions"];
const blank21=()=>({...blank20(),...Object.fromEntries(ev21.map(k=>[k,0]))});
function meter21(limit){const m=meter20(limit);m.c=blank21();return m}
// Bounded numeric value store. Key metadata is deliberately outside byte count.
class Memo21{
 constructor(M,cap=128){this.M=M;this.v=new Float64Array(cap);this.keys=Array(cap);this.index=new Map();this.next=0;this.size=0}
 map(prefix){
  const m=this;return {has(k){return m.index.has(prefix+k)},get(k){m.M.event("memoHits");return m.v[m.index.get(prefix+k)]},set(k,v){m.set(prefix+k,v);return this}};
 }
 set(k,v){
  const M=this.M;M.take("nodeInit");
  if(this.index.has(k)){this.v[this.index.get(k)]=v;M.event("memoWrites");return}
  const i=this.next,old=this.keys[i];
  if(old!==undefined)M.take("traverseEdge");
  if(old!==undefined){this.index.delete(old);M.event("memoEvictions")}else this.size++;
  this.keys[i]=k;this.index.set(k,i);this.v[i]=v;this.next=(i+1)%this.v.length;M.event("memoWrites");M.c.memoPeak=Math.max(M.c.memoPeak,this.size);
  ok(this.index.size<=this.v.length,"memo capacity");
 }
}
class Arena21{
 constructor(M,cap){this.M=M;this.cap=cap;this.a=new Float64Array(cap*8);this.n=0}
 admit(n){if(this.n+n>this.cap)return -1;this.M.take("nodeInit",n);const i=this.n;this.n+=n;this.M.c.arenaPeak=Math.max(this.M.c.arenaPeak,this.n);return i}
 get(i,j){return this.a[8*i+j]}
 set(i,j,x){ok(i>=0&&i<this.n&&j>=0&&j<8,"arena index");this.a[8*i+j]=x}
}
// Heap stores only child record indices. Slot 6 contains the last upper key.
class Heap21{
 constructor(A,M,cap){this.A=A;this.M=M;this.buf=new Int32Array(cap);this.n=0}
 higher(a,b){
  this.M.take("lookup");this.M.event("heapCompare");
  const x=this.A.get(a,6),y=this.A.get(b,6);
  return x>y||(x===y&&a<b)
 }
 swap(i,j){this.M.take("traverseEdge");this.M.event("heapSwap");const t=this.buf[i];this.buf[i]=this.buf[j];this.buf[j]=t}
 push(x){
  this.M.take("leafVisit");this.M.event("heapPush");ok(this.n<this.buf.length,"heap capacity");
  let i=this.n++;this.buf[i]=x;
  while(i){const p=(i-1)>>1;if(!this.higher(this.buf[i],this.buf[p]))break;this.swap(i,p);i=p}
 }
 pop(){
  this.M.take("leafVisit");this.M.event("heapPop");ok(this.n>0,"empty heap");
  const r=this.buf[0];this.n--;if(this.n){this.buf[0]=this.buf[this.n];let i=0;
   for(;;){let j=i,l=2*i+1,h=l+1;if(l<this.n&&this.higher(this.buf[l],this.buf[j]))j=l;if(h<this.n&&this.higher(this.buf[h],this.buf[j]))j=h;if(j===i)break;this.swap(i,j);i=j}}
  return r;
 }
}
class Bounded21 extends Planner{
 constructor(P,M){super(P,M,"prophet",null);this.memo21=new Memo21(M);this.lv=this.memo21.map("L:");this.av=this.memo21.map("A:");this.hm=this.memo21.map("H:")}
 h1(s,b){
  if(b<=0)return 0;this.M.take("lookup");const k=key(s,b);if(this.hm.has(k))return this.hm.get(k);
  let v=0;for(const a of this.raw({s,b},false)){
   this.M.take("rangeEval");let q=0;for(const o of a.os){this.M.take("rangeOutcome");q+=o.p*(o.hit?1:this.alloc(o.s,b-1))}
   v=Math.max(v,q);
  }this.hm.set(k,v);return v;
 }
}
class Whole21 extends Bounded21{
 solve(s,b,fallback,finish=false){
  const M=this.M;M.event("decisions");let snap=null,cheap=null;
  try{
   const c=cheapRoot19(this.P,s,b,M);snap=cheap=c.snap;
   const rows=c.rows.map(x=>({...x})),order=rows.map((_,i)=>i).sort((i,j)=>quant(rows[j].L)-quant(rows[i].L)||rows[j].a.id-rows[i].a.id);
   for(const i of order){
    if(snap.certified&&!finish)break;
    M.take("rangeEval");let v=0;
    for(const o of c.raw[i].os){M.take("rangeOutcome");v+=o.p*(o.hit?1:this.h1(o.s,b-1))}
    const z=Math.max(rows[i].L,v);ok(z<=rows[i].U+EPS,"whole bound");
    for(const a of rows)M.take("rangeEval");
    rows[i]={...rows[i],L:Math.min(z,rows[i].U)};
    snap=snapshot19(rows);M.event("wholeCompleted");
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  if(!snap){M.event("fallback");return {a:fallback,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap.bestL>cheap.bestL+EPS)M.event("usefulDecisions");if(snap.certified)M.event("certified");return snap;
 }
}
class Stream21 extends Bounded21{
 constructor(P,M,mode,cap,audit=false,finish=false){
  super(P,M);this.kind21=mode;this.A=new Arena21(M,cap);this.H=new Heap21(this.A,M,cap);
  this.meta=new Map();this.rows=[];this.childIds=[];this.best=-1;this.upper=0;this.phase=0;this.cheap=null;this.active21=false;this.audit21=audit;this.finish21=finish;this.trace=[];
 }
 init(s,b){
  const M=this.M;
  // Preserve a complete cheap snapshot before allocating any graph records.
  const c=cheapRoot19(this.P,s,b,M);this.cheap=c.snap;
  if(c.snap.certified&&!this.finish21)return;
  const children=new Map(),roster=[];
  let n=0;
  for(let i=0;i<c.raw.length;i++){
   const a=c.raw[i],row={a:a.a,idx:n++,os:[]};roster.push(row);
   for(const o of a.os){
    const d={idx:n++,p:o.p,hit:o.hit,child:null};
    if(!o.hit){
     M.take("lookup");const k=key(o.s,b-1);
     if(!children.has(k))children.set(k,{idx:n++,s:o.s.slice(),b:b-1,refs:[]});
     d.child=children.get(k);d.child.refs.push({row:row.idx,edge:d.idx});
    }row.os.push(d);
   }
  }
  if(n>this.A.cap){M.event("arenaBlocked");return}
  // Compute child cheap bounds outside admission, then atomically admit.
  const childBounds=new Map();for(const x of children.values())childBounds.set(x.idx,cheapValue19(this.P,x.s,x.b,M));
  const start=this.A.admit(n);ok(start===0,"root admission");const A=this.A;
  for(const row of roster){
   const r=c.rows.find(x=>x.a.id===row.a.id);A.set(row.idx,0,r.L);A.set(row.idx,1,r.U);A.set(row.idx,2,row.a.id);this.meta.set(row.idx,row);this.rows.push(row.idx);
   for(const d of row.os){A.set(d.idx,0,d.p);A.set(d.idx,1,d.hit?-1:d.child.idx);A.set(d.idx,2,row.idx)}
   this.upper=Math.max(this.upper,r.U);
   if(this.best<0||this.better(row.idx,r.L,this.best,A.get(this.best,0)))this.best=row.idx;
  }
  for(const x of children.values()){
   const r=childBounds.get(x.idx);A.set(x.idx,0,r.L);A.set(x.idx,1,r.U);A.set(x.idx,2,0);A.set(x.idx,3,0);A.set(x.idx,4,0);A.set(x.idx,5,0);A.set(x.idx,6,0);A.set(x.idx,7,0);
   x.actions=null;this.meta.set(x.idx,x);this.childIds.push(x.idx)
  }
  this.active21=true;if(this.audit21)this.auditCurrent();
 }
 better(i,l,j,r){const q=quant(l)-quant(r);return q>0||(q===0&&this.A.get(i,2)>this.A.get(j,2))}
 snap(){
  if(!this.active21)return this.cheap;
  const A=this.A,i=this.best,L=A.get(i,0),U=this.upper,gap=Math.max(0,U-L);
  return {a:this.meta.get(i).a,L,U,gap,certified:gap<=EPS,bestL:L,ranges:this.rows.map(j=>({id:A.get(j,2),L:A.get(j,0),U:A.get(j,1)}))};
 }
 priority(i){
  const A=this.A,M=this.M;M.take("leafVisit");M.event("taskScans");
  if(A.get(i,1)-A.get(i,0)<=EPS/10)return 0;
  if(this.phase===0&&A.get(i,2)===1)return 0;
  if(this.phase===1&&(A.get(i,5)===1||(A.get(i,4)===1&&A.get(i,3)>=A.get(i,7))))return 0;
  let reach=0;const best=A.get(this.best,0);
  for(const d of this.meta.get(i).refs){M.take("rangeEval");if(this.finish21||A.get(d.row,1)+EPS>=best){M.take("rangeOutcome");reach+=A.get(d.edge,0)}}
  return reach*Math.max(0,A.get(i,1)-A.get(i,0));
 }
 chooseScan(){
  for(;this.phase<2;this.phase++){
   let best=-1,score=0;
   for(const i of this.childIds){const p=this.priority(i);if(p>score||(p===score&&p>0&&i<best)){best=i;score=p}}
   if(best>=0)return best;
  }return -1;
 }
 build(){
  this.M.event("phaseBuilds");for(const i of this.childIds){const p=this.priority(i);if(p>0){this.A.set(i,6,p);this.H.push(i)}}
 }
 chooseHeap(){
  const H=this.H,A=this.A,M=this.M;
  if(!this.built){this.build();this.built=true}
  for(;;){
   while(H.n){
    const i=H.pop(),old=A.get(i,6),p=this.priority(i);ok(p<=old+1e-10,"priority must decrease");
    if(p<=0){M.event("dominatedPops");continue}
    if(p<old){M.event("stalePops");A.set(i,6,p)}
    if(H.n&&H.higher(H.buf[0],i)){H.push(i);continue}
    return i;
   }
   if(++this.phase>=2)return -1;this.build()
  }
 }
 commit(i,value,flag,cursor=null){
  const A=this.A,M=this.M,x=this.meta.get(i),old=A.get(i,0),z=Math.max(old,Math.min(A.get(i,1),value));
  ok(value<=A.get(i,1)+EPS,"child lower exceeds upper");
  M.take("backup");const delta=z-old,changes=new Map();
  if(delta>0)for(const d of x.refs){
   M.take("traverseEdge");M.take("rangeOutcome");changes.set(d.row,(changes.get(d.row)??A.get(d.row,0))+A.get(d.edge,0)*delta)
  }
  let best=this.best;
  for(const [j,v] of changes){
   M.take("rangeEval");const l=Math.min(A.get(j,1),v),r=changes.has(best)?Math.min(A.get(best,1),changes.get(best)):A.get(best,0);
   if(this.better(j,l,best,r))best=j;
  }
  // Atomic numeric commit: no charged operation after first mutation.
  A.set(i,0,z);if(flag)A.set(i,2,1);if(cursor!==null)A.set(i,3,cursor);
  for(const [j,v] of changes){A.set(j,0,Math.min(A.get(j,1),v));M.event("deltaUpdates")}
  this.best=best;M.event("commits");if(this.audit21)this.auditCurrent();
 }
 auditCurrent(){
  const A=this.A;for(const i of this.rows){const r=this.meta.get(i);let v=0;
   for(const o of r.os)v+=A.get(o.idx,0)*(o.hit?1:A.get(A.get(o.idx,1),0));
   ok(Math.abs(v-A.get(i,0))<1e-10,"delta reconstruction");this.M.event("deltaAudit");
   ok(!this.better(i,A.get(i,0),this.best,A.get(this.best,0)),"running best root");
  }
  ok(A.n<=A.cap&&this.H.n<=A.cap,"arena/heap");
 }
 task(i){
  const A=this.A,M=this.M,c=this.meta.get(i);
  this.trace.push(this.phase+":"+i+":"+A.get(i,3));
  if(this.phase===0){const v=this.alloc(c.s,c.b);this.commit(i,v,true);M.event("staticTerms");return}
  if(A.get(i,4)===0){
   const actions=this.P.legal(c.s,c.b);
   for(const a of actions)M.take("actionEnum");
   const start=A.admit(actions.length);
   if(start<0){A.set(i,5,1);M.event("arenaBlocked");return}
   c.actions=actions;
   for(let j=0;j<actions.length;j++){const a=actions[j];A.set(start+j,0,a.i);A.set(start+j,1,a.t);A.set(start+j,2,a.evict);A.set(start+j,3,a.id)}
   A.set(i,4,1);A.set(i,7,actions.length);M.event("childRosters");
  }
  const j=A.get(i,3);if(j>=A.get(i,7))return;
  const a=c.actions[j],n=this.P.local[a.i].outcomes(c.s[a.i],a.t).length;M.take("outcomeGen",n);M.take("rangeEval");
  let q=0;for(const o of this.P.outcomes(c.s,a)){M.take("rangeOutcome");q+=o.p*(o.hit?1:this.alloc(o.s,c.b-1))}
  this.commit(i,q,false,j+1);M.event("childCompleted");M.event("secondTerms");
 }
 solve(s,b,fallback){
  const M=this.M;M.event("decisions");
  try{
   this.init(s,b);
   while(this.active21&&(this.finish21||!this.snap().certified)){
    const i=this.kind21==="scan"?this.chooseScan():this.chooseHeap();if(i<0)break;
    this.task(i);
    if(this.kind21!=="scan"&&this.phase===1){const p=this.priority(i);if(p>0){this.A.set(i,6,p);this.H.push(i)}}
   }
  }catch(e){if(e!==STOP)throw e;M.event("aborted")}
  const r=this.snap();
  if(!r){M.event("fallback");return {a:fallback,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(r.bestL>this.cheap.bestL+EPS)M.event("usefulDecisions");if(r.certified)M.event("certified");return r;
 }
}
function unlimited21(root,cap,b){
 const Q=new AllocationProblem(root,cap);setup(Q);const ref=reference20(Q,Q.initial(),b);
 let checks=0,maxError=0,traceMismatch=0,updates=0,traces=[];
 for(const mode of ["scan","indexed","whole"]){
  const P=new Problem(root,cap);setup(P);const M=meter21(Infinity),g=mode==="whole"?new Whole21(P,M):new Stream21(P,M,mode,512,true,true);
  const r=g.solve(P.initial(),b,P.legal(P.initial(),b)[0],true);
  for(const a of r.ranges){const x=ref.find(x=>x.id===a.id),e=Math.abs(a.L-x.L);ok(e<1e-10,"unlimited lower mismatch "+JSON.stringify({mode,a,x,e}));checks++;maxError=Math.max(maxError,e)}
  updates+=M.c.deltaAudit;if(g.trace)traces.push(g.trace)
 }traceMismatch+=Number(JSON.stringify(traces[0])!==JSON.stringify(traces[1]));
 return {checks,maxError,traceMismatch,updates};
}
function policy21(root,cap,budget,total,mode,arena,oracle,auditMode){
 const P=new Problem(root,cap),pre=setup(P),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakRecords:0,updates:0,peakMemo:0};
 function rec(s,b,left){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank21(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,b)=>b.id-a.id)[0];
  const M=meter21(Math.min(left,Math.ceil(2*left/b))),g=mode==="whole"?new Whole21(P,M):new Stream21(P,M,mode,arena,auditMode),r=g.solve(s,b,fallback);
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakRecords=Math.max(audit.peakRecords,g.A?.n??0);audit.peakMemo=Math.max(audit.peakMemo,M.c.memoPeak);audit.updates+=M.c.deltaAudit;
  ok(audit.peakRecords<=arena&&audit.peakMemo<=128,"numeric cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  for(const o of P.outcomes(s,r.a)){if(o.hit){v+=o.p;continue}
   const q=rec(o.s,b-1,left-M.used);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*q.used;maxUsed=Math.max(maxUsed,M.used+q.maxUsed);addWork(work,q.work,o.p)}
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");
  return {v,calls,used,maxUsed,work}
 }
 const r=rec(P.initial(),budget,total),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");
 return {...r,regret,audit,pre};
}
function cohort21(name){
 if(name==="standard")return {n:48,seed:2720001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:24,seed:2730001,cap:2,b:8,stages:4};
 return {n:32,seed:2740001,cap:1,b:5,stages:4};
}
function experiment21(name){
 const begin=Date.now(),{n,seed,cap,b,stages}=cohort21(name),modes=["metered2","incCheap","weighted96","weighted32","scan","indexed","indexed32","whole"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]},audit={unlimitedRoots:0,unlimitedActions:0,maxError:0,traceMismatch:0,unlimitedUpdates:0,updates:0};
 for(let i=0;i<n;i++){
  const root=rootFor(name,seed+i,stages),P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);
  ref.optimal.push(opt.v);const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(i<4){const u=unlimited21(root,cap,b);audit.unlimitedRoots++;audit.unlimitedActions+=u.checks;audit.maxError=Math.max(audit.maxError,u.maxError);audit.traceMismatch+=u.traceMismatch;audit.unlimitedUpdates+=u.updates}
  for(const t of limits)for(const mode of modes){
   let r;
   if(["metered2","incCheap"].includes(mode))r=policy19(root,cap,b,t,mode,oracle,false);
   else if(mode.startsWith("weighted"))r=policy20(root,cap,b,t,"weighted",mode==="weighted32"?32:96,oracle,false);
   else r=policy21(root,cap,b,t,mode==="indexed32"?"indexed":mode,mode==="indexed32"?32:96,oracle,i<2);
   r.work={...blank21(),...r.work};all[mode+t].push(r);if(["scan","indexed","indexed32","whole"].includes(mode))audit.updates+=r.audit.updates??0;
  }
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const k of keys){
  const a=all[k],work=Object.fromEntries(Object.keys(blank21()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  const fresh=k.startsWith("scan")||k.startsWith("indexed")||k.startsWith("whole"),arena=k.startsWith("indexed32")?32:96;
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:fresh?(k.startsWith("whole")?1024:arena*68+1024):null,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakRecords:fresh&&!k.startsWith("whole")||k.startsWith("weighted")?max("peakRecords"):null,peakMemo:fresh?max("peakMemo"):null}});
 }
 for(const t of limits)for(const [k,r] of [["indexed","scan"],["indexed","weighted96"],["indexed","metered2"],["indexed","incCheap"],["indexed32","indexed"],["whole","metered2"],["whole","indexed"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0210000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite independent synthetic decision model, weighted work and explicitly bounded numeric arrays",name,roots:n,cap,budget:b,audit,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-begin};
}
const cohortName21=process.argv.includes("--deep")?"deep":process.argv.includes("--tight")?"tight":"standard";
console.log(JSON.stringify(experiment21(cohortName21),null,2));
