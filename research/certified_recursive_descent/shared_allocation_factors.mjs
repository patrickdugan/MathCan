import {pathToFileURL} from "node:url";
// CRD-24: shared min-product allocation factors, metered bounded memo.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {desc16,align16} from "./persistent_symmetry.mjs";
import {EPS,clip,key,STOP,charges,setup,Planner,addWork} from "./metered_refinement.mjs";
import {meter19,Inc19,Two19,copyInc19,policy19} from "./incremental_refinement.mjs";

const ev24=["storeHits","storeMisses","storeWrites","storeEvictions","storePeak","truncationHits","scalarHits","leafHits","segmentHits","rootHits","deadlineHits","factorLeaves","vectorInit","mergeCalls","identitySkips","supportReads","segmentEntries","factorQueries","vectorReads","vectorWrites"];
function meter24(limit){const m=meter19(limit);Object.assign(m.c,Object.fromEntries(ev24.map(k=>[k,0])));return m}
const blank24=()=>meter24(0).c;
const hitKind24={S:"scalarHits",L:"leafHits",P:"segmentHits",R:"rootHits",D:"deadlineHits"};
class Store24{
 constructor(M,slots,width){this.M=M;this.slots=slots;this.width=width;this.buf=new Float64Array(slots*width);this.keys=Array(slots);this.index=new Map();this.next=0}
 has(k,n=1){const z=this.index.get(k);return z!==undefined&&z.n>=n}
 read(k,n,charge=true){
  const M=this.M;if(charge)M.take("lookup");
  const z=this.index.get(k);
  if(!z||z.n<n){M.event("storeMisses");return null}
  M.take("copyNode",n);M.event("storeHits");M.event("vectorReads",n);
  M.event(hitKind24[k[0]]??"scalarHits");if(z.n>n)M.event("truncationHits");
  return this.buf.slice(z.i*this.width,z.i*this.width+n);
 }
 put(k,v){
  const M=this.M;ok(v.length>0&&v.length<=this.width&&v.every(Number.isFinite),"memo vector domain");
  const old=this.index.get(k),i=old?old.i:this.next,prior=this.keys[i];
  M.take("nodeInit",v.length);
  if(!old&&prior!==undefined)M.take("traverseEdge");
  // Atomic store after every charge; returned read vectors are independent.
  if(!old){if(prior!==undefined){this.index.delete(prior);M.event("storeEvictions")}this.keys[i]=k;this.next=(i+1)%this.slots}
  this.buf.set(v,i*this.width);this.index.set(k,{i,n:v.length});
  M.event("storeWrites");M.event("vectorWrites",v.length);M.c.storePeak=Math.max(M.c.storePeak,this.index.size);
  ok(this.index.size<=this.slots,"memo capacity");
 }
 scalar(prefix){
  const S=this;return {has(k){const yes=S.has(prefix+k);if(!yes)S.M.event("storeMisses");return yes},get(k){const z=S.read(prefix+k,1,false);ok(z,"scalar read");return z[0]},set(k,v){S.put(prefix+k,[v]);return this}};
 }
}
function support24(v,M){
 const out=[0];
 for(let i=1;i<v.length;i++){if(M){M.take("rangeOutcome");M.event("supportReads")}if(v[i]<v[i-1])out.push(i)}
 return out;
}
function merge24(a,g,M){
 ok(a.length===g.length,"convolution horizon");
 if(M)M.event("mergeCalls");
 let sa=support24(a,M),sg=support24(g,M);
 if(sa.length===1){if(M){M.take("rangeEval");M.event("identitySkips")}return g}
 if(sg.length===1){if(M){M.take("rangeEval");M.event("identitySkips")}return a}
 if(sa.length<sg.length){[a,g]=[g,a];sg=sa}
 if(M){M.take("nodeInit",a.length);M.event("vectorInit",a.length)}
 const out=new Float64Array(a.length);
 for(let r=0;r<a.length;r++){
  let best=1;
  for(const t of sg){if(t>r)break;if(M)M.take("allocation");best=Math.min(best,a[r-t]*g[t])}
  out[r]=r?Math.min(out[r-1],best):best;
 }
 return out;
}
class Factor24 extends Planner{
 constructor(P,M,kind,B){
  super(P,M,"prophet",null);this.kind24=kind;this.B=B;
  const slots=kind==="tree16"?16:64,width=B+1;
  this.store=new Store24(M,kind==="scalar"?slots*width:slots,kind==="scalar"?1:width);
  this.bytes=this.store.buf.byteLength;this.lastVec=null;
  if(kind==="scalar"){this.lv=this.store.scalar("S:L:");this.av=this.store.scalar("S:A:")}
  else this.lv={has(){return false},set(){return this}};
  this.dv=this.store.scalar("D:");
 }
 leaf(i,id,b){
  const M=this.M,k="L:"+desc16(this.P,i,id),cached=this.store.read(k,b+1);
  if(cached)return cached;
  M.event("factorLeaves");M.take("nodeInit",b+1);M.event("vectorInit",b+1);M.take("option");
  const f=new Float64Array(b+1).fill(1);
  if(id>=0){
   const l=this.P.local[i],m=l.L-l.at(id).stage;let last=1;
   for(let t=1;t<=b;t++){
    if(t>m&&t<=m+3){M.take("option");last=Math.min(last,clip(1-super.val(i,id,t)))}
    f[t]=last;
   }
  }
  this.store.put(k,f);return f;
 }
 val(i,id,b){return this.kind24==="scalar"?super.val(i,id,b):clip(1-this.leaf(i,id,b)[b])}
 seg(s,b,lo,hi){
  if(hi-lo===1)return this.leaf(lo,s[lo],b);
  const M=this.M;
  M.take("option",hi-lo);M.event("segmentEntries",hi-lo);
  const k=(lo===0&&hi===s.length?"R:":"P:")+lo+":"+hi+":"+s.slice(lo,hi).join(",");
  const old=this.store.read(k,b+1);if(old)return old;
  const mid=this.kind24==="prefix"?hi-1:(lo+hi)>>1;
  const a=this.seg(s,b,lo,mid),g=this.seg(s,b,mid,hi),v=merge24(a,g,M);
  this.store.put(k,v);return v;
 }
 alloc(s,b){
  const M=this.M;M.event("factorQueries");
  ok(b>=0&&b<=this.B,"factor horizon");
  if(this.kind24==="scalar")return super.alloc(s,b);
  let v;
  if(this.kind24==="fold"){
   M.take("option",s.length);M.event("segmentEntries",s.length);
   const k="R:0:"+s.length+":"+s.join(","),old=this.store.read(k,b+1);
   if(old)v=old;
   else{
    for(let i=0;i<s.length;i++){const x=this.leaf(i,s[i],b);v=i?merge24(v,x,M):x}
    this.store.put(k,v);
   }
  }else v=this.seg(s,b,0,s.length);
  this.lastVec=v;return clip(1-v[b]);
 }
}
class Inc24 extends Inc19{
 constructor(P,M,kind,B,retained){super(P,M,"incCheap",retained,false);this.factor24=new Factor24(P,M,kind,B)}
 val(i,id,b){return this.factor24.val(i,id,b)}
 alloc(s,b){return this.factor24.alloc(s,b)}
 dl(s,b){return this.factor24.dl(s,b)}
}
class Two24 extends Two19{
 constructor(P,M,B){super(P,M,"prophet",null);this.factor24=new Factor24(P,M,"tree",B)}
 val(i,id,b){return this.factor24.val(i,id,b)}
 alloc(s,b){return this.factor24.alloc(s,b)}
 dl(s,b){return this.factor24.dl(s,b)}
}
function unit24(){
 const r=rng(3050001);let assoc=0,identity=0,sparse=0;
 function dense(a,b){
  return a.map((_,i)=>{let v=null;for(let t=0;t<=i;t++){const x=a[i-t]*b[t];if(v===null||x<v)v=x}return v})
 }
 function small(a,b){
  const s=[0];for(let i=1;i<b.length;i++)if(b[i]<b[i-1])s.push(i);
  return a.map((_,i)=>{let v=null;for(const t of s){if(t>i)break;const x=a[i-t]*b[t];if(v===null||x<v)v=x}return v})
 }
 for(let j=0;j<256;j++){
  const B=1+Math.floor(r()*10),vec=()=>{let last=10n;return Array.from({length:B+1},(_,i)=>{if(i)last=last-BigInt(Math.floor(r()*(Number(last)+1)));return last})};
  const a=vec(),b=vec(),c=vec(),one=a.map(()=>1n),ab=dense(a,b),left=dense(ab,c),right=dense(a,dense(b,c)),id=dense(a,one),sp=small(a,b);
  for(let i=0;i<=B;i++){ok(left[i]===right[i],"associativity");assoc++;ok(id[i]===a[i],"identity");identity++;ok(sp[i]===ab[i],"integer sparse support");sparse++}
  const f=new Float64Array(a.map(x=>Number(x)/10)),g=new Float64Array(b.map(x=>Number(x)/10)),z=merge24(f,g,null);
  for(let i=0;i<=B;i++)ok(Math.abs(z[i]-Number(ab[i])/100)<1e-12,"production convolution");
 }
 const M=meter24(Infinity),S=new Store24(M,2,4);S.put("L:a",[1,.8,.6,.5]);const a=S.read("L:a",2);
 ok(a[1]===.8&&!S.has("L:a",5),"truncation");S.put("P:b",[1,.7]);S.put("R:c",[1,.9,.2]);
 ok(!S.has("L:a")&&a[1]===.8&&S.index.size===2&&S.buf.byteLength===64,"eviction alias");
 const before=S.buf.slice(),keys=[...S.index.keys()];M.limit=M.used+1;
 try{S.put("R:d",[1,.2]);throw Error("expected meter abort")}catch(e){if(e!==STOP)throw e}
 ok(S.buf.every((x,i)=>x===before[i])&&JSON.stringify([...S.index.keys()])===JSON.stringify(keys),"atomic store abort");
 return {assoc,identity,sparse,storeChecks:3};
}
function queries24(P,B){
 const root=P.initial(),out=[{s:root,b:B,depth:0,changed:0}];
 for(const a of P.legal(root,B))for(const o of P.outcomes(root,a)){
  if(o.hit)continue;
  out.push({s:o.s,b:B-1,depth:1,changed:o.s.filter((x,i)=>x!==root[i]).length});
  for(const aa of P.legal(o.s,B-1))for(const z of P.outcomes(o.s,aa))if(!z.hit)
   out.push({s:z.s,b:B-2,depth:2,changed:z.s.filter((x,i)=>x!==o.s[i]).length});
 }return out;
}
function trace24(root,cap,B,auditVec){
 const P=new Problem(root,cap);setup(P);
 const qs=queries24(P,B),ref=new AllocationProblem(root,cap);setup(ref);
 const truth=qs.map(q=>ref.alloc(align16(P,q.s,ref),q.b).v),modes=["direct","scalar","fold","prefix","tree","tree16"],rows=[];
 let coeffChecks=0,maxError=0;
 for(const kind of modes){
  const M=meter24(Infinity),G=kind==="direct"?new Planner(P,M,"prophet",null):new Factor24(P,M,kind,B);
  let error=0;
  for(let i=0;i<qs.length;i++){
   const q=qs[i],v=G.alloc(q.s,q.b),e=Math.abs(v-truth[i]);
   ok(e<1e-10,"static trace disagreement "+JSON.stringify({kind,q,v,truth:truth[i],e}));error=Math.max(error,e);
   if(auditVec&&G.lastVec){
    const aligned=align16(P,q.s,ref);
    for(let t=0;t<=q.b;t++){
     const e=Math.abs(1-G.lastVec[t]-ref.alloc(aligned,t).v);ok(e<1e-10,"factor coefficient");coeffChecks++;error=Math.max(error,e)
    }
   }
  }
  ok(M.used===sum(charges.map(k=>M.c[k])),"trace ledger");
  rows.push({kind,queries:qs.length,work:M.used,typedBytes:G.bytes??null,stats:M.c,maxError:error});
  maxError=Math.max(maxError,error);
 }
 const changed=[0,0,0,0];for(const q of qs.slice(1))changed[Math.min(3,q.changed)]++;
 return {queries:qs.length,distinct:new Set(qs.map(q=>key(q.s,q.b))).size,changed,depth1:qs.filter(q=>q.depth===1).length,depth2:qs.filter(q=>q.depth===2).length,coeffChecks,maxError,rows};
}
function policy24(root,cap,B,total,kind,oracle){
 const P=new Problem(root,cap),pre=setup(P),inc=kind!=="tree2",audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakSlots:0,peakNodes:0,peakEdges:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank24(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0];
  const M=meter24(Math.min(left,Math.ceil(2*left/b))),G=inc?new Inc24(P,M,kind,B,retained):new Two24(P,M,B),r=G.solve(s,b,fallback);
  if(!r.ranges&&inc&&M.c.fallback===0)M.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));
  let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);
  ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakSlots=Math.max(audit.peakSlots,M.c.storePeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,G.peakEdges);
  ok(G.factor24.store.index.size<=G.factor24.store.slots,"policy store");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){
   if(o.hit){v+=o.p;continue}
   const C=meter24(left-M.used);let keep=null;
   if(inc&&r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyInc19(o.n,C);
   addWork(work,C.c,o.p);
   const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep);
   v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),B,total,null),regret=oracle.rec(oracle.P.initial(),B).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre};
}
function cohort24(name){
 if(name==="standard")return {n:32,seed:3020001,pop:3,stages:3,b:6};
 if(name==="population")return {n:24,seed:3030001,pop:5,stages:2,b:6};
 return {n:16,seed:3040001,pop:7,stages:2,b:5};
}
function experiment24(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort24(name),cap=2,modes=["incCheap","metered2","scalar","fold","prefix","tree","tree16","tree2"],traceModes=["direct","scalar","fold","prefix","tree","tree16"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]},traces=[];
 const audit={unit:unit24(),queries:0,distinct:0,depth1:0,depth2:0,changed:[0,0,0,0],valueChecks:0,coeffChecks:0,maxError:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),t=trace24(root,cap,b,i<2);traces.push(t);
  for(const k of ["queries","distinct","depth1","depth2","coeffChecks"])audit[k]+=t[k];for(let j=0;j<4;j++)audit.changed[j]+=t.changed[j];
  audit.valueChecks+=t.queries*t.rows.length;audit.maxError=Math.max(audit.maxError,t.maxError);
  const P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);ref.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  for(const total of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,total,mode,oracle,false):policy24(root,cap,b,total,mode,oracle);
   r.work={...blank24(),...r.work};all[mode+total].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,traceRows=[],tracePairs=[],rows=[],paired=[];
 for(const kind of traceModes){
  const a=traces.map(t=>t.rows.find(r=>r.kind===kind)),stats=Object.fromEntries(Object.keys(blank24()).map(k=>[k,k==="storePeak"?Math.max(...a.map(x=>x.stats[k])):sum(a.map(x=>x.stats[k]))]));
  traceRows.push({kind,roots:n,queries:audit.queries,totalWork:sum(a.map(x=>x.work)),meanWorkPerQuery:sum(a.map(x=>x.work))/audit.queries,typedBytes:a[0].typedBytes,stats,maxError:Math.max(...a.map(x=>x.maxError))});
 }
 for(const [k,r] of [["tree","scalar"],["tree","fold"],["tree","direct"],["prefix","fold"],["tree16","tree"]]){
  const d=traces.map(t=>t.rows.find(x=>x.kind===k).work-t.rows.find(x=>x.kind===r).work);
  tracePairs.push({kind:k,ref:r,...bootstrap(d,(0xC0241000+seed+traceModes.indexOf(k)*20+traceModes.indexOf(r))>>>0)});
 }
 for(const total of limits)for(const mode of modes){
  const k=mode+total,a=all[k],work=Object.fromEntries(Object.keys(blank24()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:(mode==="tree16"?16:64)*(b+1)*8,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakSlots:max("peakSlots"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}});
 }
 for(const t of limits)for(const [k,r] of [["tree","scalar"],["tree","incCheap"],["tree","fold"],["prefix","fold"],["tree16","tree"],["tree2","metered2"],["scalar","incCheap"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0240000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)});
 }
 return {status:"PASS",scope:"finite independent branch model, trace equivalence and metered policy proxy",name,roots:n,population:pop,budget:b,cap,audit,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},traceRows,tracePairs,rows,paired,elapsedMs:Date.now()-start};
}
export {meter24,blank24,Store24,Factor24,merge24,experiment24};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const name24=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
 console.log(JSON.stringify(experiment24(name24),null,2));
}
