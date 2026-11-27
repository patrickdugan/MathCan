import {pathToFileURL} from "node:url";
// CRD-25: packed Pareto supports, sibling-local products and joint likelihoods.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {desc16,align16} from "./persistent_symmetry.mjs";
import {EPS,clip,key,STOP,charges,setup,Planner,addWork} from "./metered_refinement.mjs";
import {Inc19,copyInc19,policy19} from "./incremental_refinement.mjs";
import {meter24,Factor24} from "./shared_allocation_factors.mjs";

const ev25=["packHits","packMisses","packWrites","packEvictions","packSuperseded","packReads","packWritten","packPeakPairs","packPeakRecords","packTruncated","pairMerges","denseMerges","pairChecks","outputPairs","identity25","baseHits","baseBuilds","baseResets","jointSweeps","jointWords","jointOutputs","leafHits25","leafBuilds25","productHits25","factorQueries25","segment25"];
function meter25(limit){const m=meter24(limit);Object.assign(m.c,Object.fromEntries(ev25.map(k=>[k,0])));m.stores25=[];return m}
const blank25=()=>meter25(0).c;
class Packed25{
 constructor(M,cap){
  this.M=M;this.cap=cap;this.buf=new Float64Array(2*cap);this.index=new Map();this.q=[];this.next=0;this.used=0;
  M.stores25.push(this)
 }
 has(k,b){const x=this.index.get(k);return x!==undefined&&x.b>=b}
 read(k,b,charge=true){
  const M=this.M;if(charge)M.take("lookup");const x=this.index.get(k);
  if(!x||x.b<b){M.event("packMisses");return null}
  M.event("packHits");if(x.b>b)M.event("packTruncated");
  let n=x.n;
  if(x.b>b&&x.last>b){
   n=0;
   for(let j=0;j<x.n;j++){M.take("rangeOutcome");if(this.buf[2*((x.pos+j)%this.cap)]>b)break;n++}
  }
  M.take("copyNode",2*n);M.event("packReads",2*n);
  const out=[];
  for(let j=0;j<n;j++){const p=2*((x.pos+j)%this.cap);out.push(this.buf[p],this.buf[p+1])}
  return out;
 }
 put(k,b,v){
  const M=this.M,n=v.length/2,need=Math.max(1,n);
  ok(Number.isInteger(n)&&need<=this.cap&&v.every(Number.isFinite),"packed domain");
  const old=this.index.get(k);
  if(old&&old.b>=b)return;
  let remove=0,free=this.cap-this.used;
  while(free<need){ok(remove<this.q.length,"packed free");M.take("traverseEdge");free+=this.q[remove++].need}
  M.take("nodeInit",2*need);
  // Commit only after all charges. FIFO physical records remain contiguous
  // around the ring; superseded metadata is removed on physical eviction.
  for(let j=0;j<remove;j++){
   const x=this.q[j];if(this.index.get(x.k)===x)this.index.delete(x.k);this.used-=x.need;M.event("packEvictions")
  }
  if(remove)this.q.splice(0,remove);
  if(old&&this.index.get(k)===old)M.event("packSuperseded");
  const pos=this.next,x={k,b,n,need,pos,last:n?v[v.length-2]:0};
  for(let j=0;j<need;j++){
   const p=2*((pos+j)%this.cap);this.buf[p]=n?v[2*j]:0;this.buf[p+1]=n?v[2*j+1]:1;
  }
  this.next=(pos+need)%this.cap;this.used+=need;this.q.push(x);this.index.set(k,x);
  M.event("packWrites");M.event("packWritten",2*need);
  M.c.packPeakPairs=Math.max(M.c.packPeakPairs,sum(M.stores25.map(z=>z.used)));
  M.c.packPeakRecords=Math.max(M.c.packPeakRecords,sum(M.stores25.map(z=>z.q.length)));
  ok(this.used<=this.cap&&this.q.length<=this.cap&&this.index.size<=this.q.length,"packed capacity");
 }
 reset(){
  this.M.take("nodeInit");this.index.clear();this.q=[];this.used=0;this.next=0;
 }
 scalar(prefix){
  const S=this;return {has(k){const yes=S.has(prefix+k,0);if(!yes)S.M.event("packMisses");return yes},get(k){const z=S.read(prefix+k,0,false);ok(z&&z.length===2,"scalar pair");return z[1]},set(k,v){S.put(prefix+k,0,[0,v]);return this}}
 }
 validate(){
  const seen=new Set();let used=0,offset=this.q.length?this.q[0].pos:this.next;
  for(const x of this.q){
   ok(x.pos===offset,"ring contiguity");offset=(offset+x.need)%this.cap;used+=x.need;
   for(let j=0;j<x.need;j++){const p=(x.pos+j)%this.cap;ok(!seen.has(p),"ring overlap");seen.add(p)}
  }
  ok(used===this.used&&offset===this.next&&used<=this.cap,"ring occupancy");
  for(const [k,x] of this.index)ok(x.k===k&&this.q.includes(x),"ring index");
 }
}
const valAt25=(a,b)=>{let v=1;for(let i=0;i<a.length;i+=2){if(a[i]>b)break;v=a[i+1]}return v};
function merge25(a,g,b,M=null,force=null){
 if(!a.length||!g.length){if(M){M.take("rangeEval");M.event("identity25")}return a.length?a:g}
 const k=a.length/2+1,l=g.length/2+1;
 const pairEst=2*k*l,denseEst=(b+1)*Math.min(k,l)+2*(b+1);
 const mode=force??(pairEst<=denseEst?"pair":"dense");
 if(M){M.event(mode==="pair"?"pairMerges":"denseMerges");M.take("nodeInit",b+1)}
 const f=new Float64Array(b+1).fill(1);
 if(mode==="pair"){
  for(let i=-2;i<a.length;i+=2){
   const x=i<0?0:a[i],p=i<0?1:a[i+1];
   for(let j=-2;j<g.length;j+=2){
    const y=j<0?0:g[j];if(M){M.take("rangeOutcome");M.event("pairChecks")}
    const r=x+y;if(r>b)break;
    if(M)M.take("allocation");f[r]=Math.min(f[r],p*(j<0?1:g[j+1]));
   }
  }
 }else{
  if(a.length<g.length)[a,g]=[g,a];
  if(M)M.take("nodeInit",b+1);
  const d=new Float64Array(b+1);let at=0,v=1;
  for(let r=0;r<=b;r++){
   if(M)M.take("rangeOutcome");
   if(at<a.length&&a[at]===r){v=a[at+1];at+=2}
   d[r]=v;
  }
  for(let r=0;r<=b;r++){
   if(M)M.take("allocation");let v=d[r];
   for(let j=0;j<g.length;j+=2){
    if(g[j]>r){if(M){M.take("rangeOutcome");M.event("pairChecks")}break}
    if(M)M.take("allocation");v=Math.min(v,d[r-g[j]]*g[j+1]);
   }
   f[r]=v;
  }
 }
 const out=[];let last=1;
 for(let r=1;r<=b;r++){
  if(M)M.take("rangeOutcome");
  if(f[r]<last){if(M){M.take("nodeInit",2);M.event("outputPairs")}last=f[r];out.push(r,last)}
 }
 return out;
}
const pred25=(j,x)=>j===0?x%2:j===1?Number(x<3):Number(x%3===0);
class Factor25 extends Planner{
 constructor(P,M,kind,B){
  super(P,M,"prophet",null);this.kind=kind;this.B=B;this.isSibling=kind.startsWith("sibling");this.joint=kind==="siblingJoint";
  const split=this.isSibling||kind==="splitTree",cap=32*(B+1);
  this.leaves=new Packed25(M,split?cap/2:cap);this.products=split?new Packed25(M,cap/2):this.leaves;
  this.bytes=2*cap*8;this.context=null;this.lastSupport=null;
  this.lv={has(){return false},set(){return this}};
  this.dv=this.leaves.scalar("D:");
 }
 jointLeaf(i,id,b){
  const M=this.M,l=this.P.local[i],s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m),values=Array(k+1).fill(0);
  M.take("localMiss",k);
  if(k>=3)values[3]=s.mass;
  const n=Math.min(2,k);
  if(m===0){
   const w=s.p.slice(0,3).sort((a,b)=>b-a);let v=0;
   for(let j=1;j<=n;j++){M.take("rangeOutcome");v+=w[j-1];values[j]=v}
  }else if(n>0){
   M.event("jointSweeps");
   for(let u=0;u<2**m;u++){
    M.take("likelihood",3*m);M.event("jointWords");
    const w=s.p.slice(0,3);
    for(let t=0;t<m;t++){
     const j=s.stage+t,a=l.spec.sensors[j]/100,bit=(u>>t)&1;
     for(let x=0;x<3;x++)w[x]*=pred25(j,x)===bit?a:1-a
    }
    w.sort((a,b)=>b-a);let v=0;
    for(let j=1;j<=n;j++){M.take("rangeOutcome");M.event("jointOutputs");v+=w[j-1];values[j]+=v}
   }
  }
  return values;
 }
 leaf(i,id,b){
  const M=this.M;M.take("option");
  if(id<0||b<=0)return [];
  const l=this.P.local[i],s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
  if(k<=0||s.mass<=0)return [];
  const d="L:"+desc16(this.P,i,id),old=this.leaves.read(d,b);
  if(old){M.event("leafHits25");return old}
  M.event("leafBuilds25");
  const vals=this.joint?this.jointLeaf(i,id,b):null,out=[];let last=1;
  for(let j=1;j<=k;j++){
   M.take("option");const v=clip(1-(vals?vals[j]:super.val(i,id,m+j)));
   if(v<last){M.take("nodeInit",2);M.event("outputPairs");out.push(m+j,v);last=v}
  }
  this.leaves.put(d,b,out);return out;
 }
 val(i,id,b){const a=this.leaf(i,id,b);this.M.take("rangeEval");return clip(1-(a.length?a[a.length-1]:1))}
 fold(s,b,exclude=null){
  let v=[];
  for(let i=0;i<s.length;i++){
   if(exclude&&exclude.has(i))continue;
   const x=this.leaf(i,s[i],b);v=merge25(v,x,b,this.M)
  }
  return v;
 }
 seg(s,b,lo,hi){
  if(hi-lo===1)return this.leaf(lo,s[lo],b);
  const M=this.M;M.take("option",hi-lo);M.event("segment25",hi-lo);
  const k=(lo===0&&hi===s.length?"R:":"P:")+lo+":"+hi+":"+s.slice(lo,hi).join(",");
  const old=this.products.read(k,b);
  if(old){M.event("productHits25");return old}
  const mid=(lo+hi)>>1,a=this.seg(s,b,lo,mid),g=this.seg(s,b,mid,hi),v=merge25(a,g,b,M);
  this.products.put(k,b,v);return v;
 }
 begin(parent,b){
  if(!this.isSibling)return;
  this.products.reset();this.M.event("baseResets");this.context={s:parent,b};
 }
 end(){this.context=null}
 alloc(s,b){
  const M=this.M;M.event("factorQueries25");ok(b>=0&&b<=this.B,"support horizon");
  let v;
  if(this.isSibling){
   const c=this.context;
   if(c&&c.b===b){
    M.take("option",s.length);const changed=s.map((id,i)=>id!==c.s[i]?i:-1).filter(i=>i>=0);
    if(changed.length<=2){
     const k="X:"+changed.join(","),old=this.products.read(k,b);
     if(old){M.event("baseHits");v=old}
     else{M.event("baseBuilds");v=this.fold(c.s,b,new Set(changed));this.products.put(k,b,v)}
     for(const i of changed)v=merge25(v,this.leaf(i,s[i],b),b,M)
    }
   }
   if(v===undefined)v=this.fold(s,b);
  }else if(this.kind==="packedFold"){
   M.take("option",s.length);M.event("segment25",s.length);
   const k="R:0:"+s.length+":"+s.join(","),old=this.products.read(k,b);
   if(old){M.event("productHits25");v=old}
   else{v=this.fold(s,b);this.products.put(k,b,v)}
  }else v=this.seg(s,b,0,s.length);
  this.lastSupport=v;M.take("rangeEval");return clip(1-(v.length?v[v.length-1]:1));
 }
}
class Inc25 extends Inc19{
 constructor(P,M,kind,B,retained){super(P,M,"incCheap",retained,false);this.factor25=kind==="scalar"?new Factor24(P,M,"scalar",B):new Factor25(P,M,kind,B)}
 val(i,id,b){return this.factor25.val(i,id,b)}
 alloc(s,b){return this.factor25.alloc(s,b)}
 dl(s,b){return this.factor25.dl(s,b)}
 expand(n){
  try{this.factor25.begin?.(n.s,n.b-1);super.expand(n)}
  finally{this.factor25.end?.()}
 }
}
function unit25(){
 const r=rng(3150001);let integer=0,identity=0,forced=0;
 for(let j=0;j<256;j++){
  const B=1+Math.floor(r()*9),vec=()=>{let last=10n;return Array.from({length:B+1},(_,i)=>{if(i)last-=BigInt(Math.floor(r()*(Number(last)+1)));return last})};
  const a=vec(),g=vec(),to=v=>v.flatMap((x,i)=>i&&x<v[i-1]?[i,Number(x)/10]:[]),x=to(a),y=to(g);
  const p=merge25(x,y,B,null,"pair"),d=merge25(x,y,B,null,"dense"),z=merge25(x,y,B);
  for(let t=0;t<=B;t++){
   let f=100n;for(let i=0;i<=t;i++){const q=a[i]*g[t-i];if(q<f)f=q}
   const truth=Number(f)/100;
   ok(Math.abs(valAt25(p,t)-truth)<1e-12,"pair rational");integer++;
   ok(Math.abs(valAt25(d,t)-truth)<1e-12&&Math.abs(valAt25(z,t)-truth)<1e-12,"dense and adaptive rational");forced+=2;
   ok(valAt25(merge25(x,[],B),t)===Number(a[t])/10,"identity");identity++;
  }
 }
 const M=meter25(Infinity),S=new Packed25(M,5);
 S.put("L:a",5,[1,.9,3,.7,5,.5]);const a=S.read("L:a",3);
 ok(JSON.stringify(a)===JSON.stringify([1,.9,3,.7])&&!S.has("L:a",6),"horizon truncation");
 S.put("P:b",4,[1,.8,2,.6]);S.put("L:c",5,[2,.75,4,.4]);S.validate();
 ok(!S.has("L:a",1)&&JSON.stringify(a)===JSON.stringify([1,.9,3,.7])&&S.used===4,"wrapped FIFO alias");
 S.put("P:b",6,[2,.7,4,.4]);S.validate();ok(JSON.stringify(S.read("P:b",6))===JSON.stringify([2,.7,4,.4]),"superseded");
 const old=S.buf.slice(),meta=JSON.stringify([S.q,S.next,S.used,[...S.index.keys()]]);
 M.limit=M.used+1;try{S.put("P:d",8,[1,.8,2,.6,3,.4]);throw Error("expected abort")}catch(e){if(e!==STOP)throw e}
 ok(old.every((x,i)=>x===S.buf[i])&&meta===JSON.stringify([S.q,S.next,S.used,[...S.index.keys()]]),"atomic packed abort");S.validate();
 return {integer,identity,forced,storeChecks:4};
}
function queries25(P,B){
 const s=P.initial(),groups=[{parent:null,b:B,qs:[{s,b:B,changed:0}]}],first=[],second=[],seen=new Set(),sat=[];
 function outcomes(s,b,evictOnly=false){
  const a=[];for(const x of P.legal(s,b))if(!evictOnly||x.evict>=0)for(const o of P.outcomes(s,x))if(!o.hit){
   const changed=o.s.filter((id,i)=>id!==s[i]).length;
   ok(changed===1||changed===2,"query changed");if(evictOnly)ok(changed===2&&o.s[x.evict]===-1,"eviction change");
   a.push({s:o.s,b:b-1,changed})
  }return a;
 }
 first.push(...outcomes(s,B));groups.push({parent:s,b:B-1,qs:first});
 for(const o of first){
  const q=outcomes(o.s,B-1);groups.push({parent:o.s,b:B-2,qs:q});second.push(...q);
  for(const z of q)if(P.active(z.s).length===P.cap&&P.legal(z.s,z.b).some(a=>a.evict>=0)){
   const k=key(z.s,z.b);if(!seen.has(k)){seen.add(k);sat.push(z)}
  }
 }
 for(const z of sat.slice(0,8)){
  groups.push({parent:null,b:z.b,qs:[{s:z.s,b:z.b,changed:0}]});
  groups.push({parent:z.s,b:z.b-1,qs:outcomes(z.s,z.b,true)});
 }
 return groups.filter(x=>x.qs.length);
}
function trace25(root,cap,B,auditAll){
 const P=new Problem(root,cap);setup(P);const groups=queries25(P,B),qs=groups.flatMap(g=>g.qs),R=new AllocationProblem(root,cap);setup(R);
 const truth=qs.map(q=>{const s=align16(P,q.s,R);return auditAll?Array.from({length:q.b+1},(_,t)=>R.alloc(s,t).v):[R.alloc(s,q.b).v]});
 const modes=["direct","scalar","tree","packedFold","packedTree","splitTree","sibling","siblingJoint"],rows=[];
 let coeffChecks=0,maxError=0;
 for(const kind of modes){
  const M=meter25(Infinity),G=kind==="direct"?new Planner(P,M,"prophet",null):["scalar","tree"].includes(kind)?new Factor24(P,M,kind,B):new Factor25(P,M,kind,B);
  let i=0,error=0;
  for(const g of groups){
   if(g.parent)G.begin?.(g.parent,g.b);
   for(const q of g.qs){
    const v=G.alloc(q.s,q.b),e=Math.abs(v-truth[i].at(-1));ok(e<1e-10,"trace value "+JSON.stringify({kind,q,v,e}));error=Math.max(error,e);
    if(auditAll&&(G.lastSupport||G.lastVec)){
     for(let t=0;t<=q.b;t++){
      const x=G.lastSupport?1-valAt25(G.lastSupport,t):1-G.lastVec[t],e=Math.abs(x-truth[i][t]);ok(e<1e-10,"support coefficient");coeffChecks++;error=Math.max(error,e)
     }
    }i++;
   }G.end?.();
  }
  for(const S of M.stores25)S.validate();
  ok(M.used===sum(charges.map(k=>M.c[k])),"trace ledger");maxError=Math.max(maxError,error);
  rows.push({kind,queries:qs.length,work:M.used,typedBytes:G.bytes??null,stats:M.c,maxError:error});
 }
 const changed=[0,0,0];for(const q of qs)changed[q.changed]++;
 return {queries:qs.length,distinct:new Set(qs.map(q=>key(q.s,q.b))).size,groups:groups.length,changed,valueChecks:qs.length*modes.length,coeffChecks,maxError,rows};
}
function policy25(root,cap,B,total,kind,oracle){
 const P=new Problem(root,cap),pre=setup(P),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakPairs:0,peakSlots:0,peakNodes:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank25(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,c)=>c.id-a.id)[0],M=meter25(Math.min(left,Math.ceil(2*left/b))),G=new Inc25(P,M,kind,B,retained),r=G.solve(s,b,fallback);
  if(!r.ranges&&M.c.fallback===0)M.event("fallback");
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"root enclosure");if(r.certified)ok(regret<=EPS+1e-9,"certified");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);
  audit.peakPairs=Math.max(audit.peakPairs,M.c.packPeakPairs);audit.peakSlots=Math.max(audit.peakSlots,M.c.storePeak);audit.peakNodes=Math.max(audit.peakNodes,G.peakNodes);
  for(const S of M.stores25)S.validate();
  ok(M.c.packPeakPairs<=32*(B+1),"pair cap");
  const work={...M.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let v=0,calls=1,used=M.used,maxUsed=M.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){if(o.hit){v+=o.p;continue}
   const C=meter25(left-M.used);let keep=null;
   if(r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyInc19(o.n,C);
   addWork(work,C.c,o.p);
   const q=rec(o.n.s,o.n.b,left-M.used-C.used,keep);v+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(C.used+q.used);maxUsed=Math.max(maxUsed,M.used+C.used+q.maxUsed);addWork(work,q.work,o.p)
  }
  ok(maxUsed<=left&&calls<=b+EPS,"path ceiling");ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"ledger");return {v,calls,used,maxUsed,work};
 }
 const r=rec(P.initial(),B,total,null),regret=oracle.rec(oracle.P.initial(),B).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");return {...r,regret,audit,pre}
}
function cohort25(name){
 if(name==="standard")return {n:24,seed:3120001,pop:3,stages:3,b:6};
 if(name==="population")return {n:20,seed:3130001,pop:5,stages:2,b:6};
 return {n:12,seed:3140001,pop:7,stages:2,b:5};
}
function experiment25(name){
 const start=Date.now(),{n,seed,pop,stages,b}=cohort25(name),cap=2,modes=["incCheap","metered2","scalar","packedFold","splitTree","sibling","siblingJoint"],traceModes=["direct","scalar","tree","packedFold","packedTree","splitTree","sibling","siblingJoint"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),refs={optimal:[],receding2:[]},traces=[];
 const audit={unit:unit25(),queries:0,distinct:0,groups:0,changed:[0,0,0],valueChecks:0,coeffChecks:0,maxError:0,oracleStates:0};
 for(let i=0;i<n;i++){
  const root=fixture(seed+i,pop,stages),t=trace25(root,cap,b,i<2);traces.push(t);
  for(const k of ["queries","distinct","groups","valueChecks","coeffChecks"])audit[k]+=t[k];for(let j=0;j<3;j++)audit.changed[j]+=t.changed[j];audit.maxError=Math.max(audit.maxError,t.maxError);
  const P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);refs.optimal.push(opt.v);audit.oracleStates+=oracle.stats.states;
  const R=new AllocationProblem(root,cap);setup(R);refs.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  for(const t of limits)for(const mode of modes){
   const r=["incCheap","metered2"].includes(mode)?policy19(root,cap,b,t,mode,oracle,false):policy25(root,cap,b,t,mode,oracle);
   r.work={...blank25(),...r.work};all[mode+t].push(r)
  }
 }
 const mean=a=>sum(a)/a.length,traceRows=[],tracePairs=[],rows=[],paired=[];
 for(const kind of traceModes){
  const a=traces.map(t=>t.rows.find(r=>r.kind===kind)),stats=Object.fromEntries(Object.keys(blank25()).map(k=>[k,["storePeak","packPeakPairs","packPeakRecords"].includes(k)?Math.max(...a.map(x=>x.stats[k])):sum(a.map(x=>x.stats[k]))]));
  traceRows.push({kind,roots:n,queries:audit.queries,totalWork:sum(a.map(x=>x.work)),typedBytes:a[0].typedBytes,stats,maxError:Math.max(...a.map(x=>x.maxError))})
 }
 for(const [k,r] of [["siblingJoint","scalar"],["splitTree","packedTree"],["siblingJoint","sibling"],["sibling","splitTree"],["packedFold","tree"],["siblingJoint","direct"]]){
  const d=traces.map(t=>t.rows.find(x=>x.kind===k).work-t.rows.find(x=>x.kind===r).work);
  tracePairs.push({kind:k,ref:r,...bootstrap(d,(0xC0251000+seed+traceModes.indexOf(k)*20+traceModes.indexOf(r))>>>0)})
 }
 for(const total of limits)for(const mode of modes){
  const k=mode+total,a=all[k],work=Object.fromEntries(Object.keys(blank25()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]??0));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,typedBytes:["incCheap","metered2"].includes(mode)?null:64*(b+1)*8,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakPairs:max("peakPairs"),peakSlots:max("peakSlots"),peakNodes:max("peakNodes")}})
 }
 for(const t of limits)for(const [k,r] of [["siblingJoint","scalar"],["siblingJoint","incCheap"],["siblingJoint","sibling"],["sibling","splitTree"],["splitTree","packedFold"],["scalar","incCheap"]]){
  const d=all[k+t].map((x,i)=>x.v-all[r+t][i].v);paired.push({kind:k+t,ref:r+t,...bootstrap(d,(0xC0250000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r+t))>>>0)})
 }
 return {status:"PASS",scope:"finite synthetic independent model; packed numeric payload and metered proxy",name,roots:n,population:pop,budget:b,cap,audit,baselines:{optimal:mean(refs.optimal),receding2:mean(refs.receding2)},traceRows,tracePairs,rows,paired,elapsedMs:Date.now()-start}
}
export {queries25,Factor25,experiment25};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const name25=process.argv.includes("--population")?"population":process.argv.includes("--larger")?"larger":"standard";
 console.log(JSON.stringify(experiment25(name25),null,2));
}
