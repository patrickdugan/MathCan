// CRD-09: dependency-aware inference and adaptive search. Node >=18.
import {verify,upperRoot} from "./audit.mjs";
import {rng} from "./search.mjs";
import {ok,exactPaired} from "./learned_frontier.mjs";
const N=6,LABEL=[2,5,1,4,0,3],INV=Array.from({length:N},(_,i)=>LABEL.indexOf(i));
const EST=[[4,2,5,0,3,1],[5,3,4,1,2,0]],C=[.16807611778507042,.14351343124006946];
const ones=()=>Array(N).fill(1),zeros=()=>Array(N).fill(0),sum=a=>a.reduce((s,v)=>s+v,0),dot=(a,b)=>sum(a.map((v,i)=>v*b[i])),unit=i=>zeros().map((_,j)=>Number(i===j));
const I=Array.from({length:N},(_,i)=>unit(i));
const mat=(a,b)=>a.map(r=>Array.from({length:N},(_,j)=>sum(r.map((v,i)=>v*b[i][j]))));
// Optional post-registration backend; default retains the registered dense code.
const FACTORIZED=typeof process!=="undefined"&&process.argv.includes("--factorized");
const TRANSITION_DATA=new WeakMap();
function row(r,b){
 const x=FACTORIZED?TRANSITION_DATA.get(b):null;
 if(!x)return Array.from({length:N},(_,j)=>sum(r.map((v,i)=>v*b[i][j])));
 const q=Array(N).fill(x.z*sum(r)/N);
 for(let i=0;i<N;i++)q[x.perm[i]]+=(1-x.z)*r[i];
 return q;
}
function col(b,r){
 const x=FACTORIZED?TRANSITION_DATA.get(b):null;
 if(!x)return b.map(a=>dot(a,r));
 const u=x.z*sum(r)/N;
 return x.perm.map(j=>(1-x.z)*r[j]+u);
}
const mulv=(a,b)=>a.map((v,i)=>v*b[i]),quant=x=>Math.round(x*1e12)/1e12;
const dep=id=>Math.floor(Math.log2(id));
function gmul(a,b){const k=a%3,s=a>=3?1:0,l=b%3,t=b>=3?1:0;return 3*(s^t)+(k+(s?-l:l)+3)%3}
const TRUE=[1,3].map(g=>I.map((_,i)=>LABEL[gmul(INV[i],g)]));
const OPERATORS=new Map();
function op(model,a,c){
 const k=model+":"+a+":"+c;
 if(OPERATORS.has(k))return OPERATORS.get(k);
 const perm=(model==="known"?TRUE:EST)[a],z=model==="known"?c:Math.max(0,Math.min(1,C[a]*c/.15));
 const T=I.map((_,i)=>zeros().map((_,j)=>z/6+(1-z)*Number(perm[i]===j)));
 TRANSITION_DATA.set(T,{perm,z});OPERATORS.set(k,T);return T;
}
const levels=(regime,d,depth)=>regime==="independent"&&d===depth?[1]:d===1?[.60,.80]:[0,.05,.15];
function meanOp(model,regime,d,depth){
 const cs=levels(regime,d,depth),ops=[0,1].flatMap(a=>cs.map(c=>op(model,a,c)));
 return I.map((r,i)=>r.map((_,j)=>sum(ops.map(x=>x[i][j]))/ops.length));
}
function future(model,regime,depth){
 const out=Array(depth+1);out[depth]=I;
 for(let d=depth-1;d>=0;d--)out[d]=mat(meanOp(model,regime,d+1,depth),out[d+1]);
 return out;
}
function cert(id,d){
 const pDen=23,pNum=1+((id+3*d)%22),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=10400,a=Math.floor((c*(rDen-rNum)-1)/rDen);
 return {pNum,pDen,rNum,rDen,a,c};
}
function checkCert(c){return BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum)}
function tree(seed,regime,fixedDepth=null){
 const random=rng(seed),drawDepth=4+Math.floor(random()*3),depth=fixedDepth??drawDepth,target=Math.floor(random()*6);
 const nodes=[null,{id:1,d:0,hidden:0}];
 for(let id=2;id<2**(depth+1);id++){
  const parent=nodes[id>>1],d=parent.d+1,a=Math.floor(random()*2),cs=levels(regime,d,depth),c=cs[Math.floor(random()*cs.length)],reset=random()<c,replacement=Math.floor(random()*6);
  nodes.push({id,d,a,c,reset,replacement,hidden:reset?replacement:gmul(parent.hidden,a===0?1:3),cert:cert(id,d)});
 }
 return {seed,regime,depth,target,nodes,leaves:nodes.filter(n=>n&&n.d===depth).map(n=>n.id)};
}
const explicit=g=>[0,1,2].map(x=>(g%3+(g>=3?-x:x)+3)%3);
function terminal(root,id){
 const path=[];for(let n=id;n>1;n>>=1)path.push(root.nodes[n]);
 let h=explicit(0);
 for(const n of path.reverse()){
  if(n.reset)h=explicit(n.replacement);else h=explicit(n.a===0?1:3).map(x=>h[x]);
 }
 const g=I.findIndex((_,i)=>explicit(i).every((x,j)=>x===h[j]));
 ok(g===root.nodes[id].hidden&&root.nodes[id].d===root.depth,"independent terminal witness");
 return LABEL[g]===root.target;
}
function key(seed,id){return rng((seed^Math.imul(id,0x9E3779B9))>>>0)()}
function shared(a,b){let da=dep(a),db=dep(b);while(da>db){a>>=1;da--}while(db>da){b>>=1;db--}while(a!==b){a>>=1;b>>=1;da--}return da}
function diversity(id,failed,depth){return .08*Math.max(0,...failed.map(f=>shared(id,f)))/depth}
function likelihood(failed,id,target){return failed.has(id)?ones().map((v,i)=>i===target?0:v):ones()}

class Belief {
 constructor(model,target){
  this.model=model;this.target=target;this.T=new Map();this.children=new Map([[1,[]]]);this.up=new Map([[1,ones()]]);this.edge=new Map();this.failed=new Set();
  this.ops={observed:0,upEdges:0,downEdges:0,queries:0,fallbacks:0,peakCacheSlots:6};
 }
 observe(id,parent,a,c){
  ok(id>>1===parent&&this.children.has(parent)&&!this.children.has(id),"observation frontier");
  this.T.set(id,op(this.model,a,c));this.children.get(parent).push(id);this.children.set(id,[]);this.up.set(id,ones());this.edge.set(id,ones());this.ops.observed++;
  this.ops.peakCacheSlots=Math.max(this.ops.peakCacheSlots,6*(this.up.size+this.edge.size));
  // A normalized transition applied to unit likelihood yields unit likelihood;
  // revealing a child without terminal evidence does not update ancestors.
 }
 Z(){return this.up.get(1)[LABEL[0]]}
 fail(id){
  ok(this.children.has(id)&&!this.failed.has(id),"failed evidence");this.failed.add(id);
  for(let n=id;n>=1;n>>=1){
   let m=likelihood(this.failed,n,this.target);
   for(const k of this.children.get(n))m=mulv(m,this.edge.get(k));
   this.up.set(n,m);
   if(n>1){this.edge.set(n,col(this.T.get(n),m));this.ops.upEdges++}
  }
 }
 query(id){
  ok(this.children.has(id),"unobserved query");this.ops.queries++;
  const path=[];for(let n=id;n>1;n>>=1)path.push(n);path.reverse();
  let p=unit(LABEL[0]),parent=1;const z=this.Z(),fallback=z<=1e-14;
  if(fallback){ok(this.model==="learned","impossible known evidence");this.ops.fallbacks++}
  for(const n of path){
   if(!fallback){
    p=mulv(p,likelihood(this.failed,parent,this.target));
    for(const sib of this.children.get(parent))if(sib!==n)p=mulv(p,this.edge.get(sib));
   }
   p=row(p,this.T.get(n));this.ops.downEdges++;parent=n;
  }
  if(!fallback)p=mulv(p,this.up.get(id)).map(v=>v/z);
  ok(p.every(v=>Number.isFinite(v)&&v>=-1e-9)&&Math.abs(sum(p)-1)<1e-8,"posterior normalization");
  return p;
 }
 snapshot(){return {...this.ops}}
}
function fullZ(root,model,failed,stats=null){
 const m=new Map();
 for(let i=root.nodes.length-1;i>=1;i--){
  const n=root.nodes[i];let v=likelihood(failed,i,root.target);
  for(const k of [2*i,2*i+1])if(k<root.nodes.length){
   const ch=root.nodes[k];v=mulv(v,col(op(model,ch.a,ch.c),m.get(k)));if(stats)stats.edges++;
  }
  m.set(i,v);
 }
 if(stats)stats.calls++;
 return m.get(1)[LABEL[0]];
}
function observeAll(root,model){
 const b=new Belief(model,root.target);
 for(let i=2;i<root.nodes.length;i++){const n=root.nodes[i];b.observe(i,i>>1,n.a,n.c)}
 return b;
}
function exactEnumeration(root){
 // Exhaustively sum rational weights in hidden group-index coordinates using
 // independently composed explicit permutations. Six nonroot nodes at depth 2.
 const states=[null,0],mass=Array(16).fill(0n),den=600n**6n;
 const permIndex=(a,b)=>I.findIndex((_,g)=>explicit(g).every((v,i)=>v===explicit(a)[explicit(b)[i]]));
 let paths=0;
 function visit(i,w){
  if(i===root.nodes.length){
   let mask=0;root.leaves.forEach((id,j)=>{if(LABEL[states[id]]===root.target)mask|=1<<j});
   mass[mask]+=w;paths++;return;
  }
  const n=root.nodes[i],c=Math.round(100*n.c),g=permIndex(states[i>>1],n.a===0?1:3);
  for(let x=0;x<N;x++){states[i]=x;visit(i+1,w*BigInt(c+(x===g?600-6*c:0)))}
 }
 visit(2,1n);ok(sumBig(mass)===den,"rational total mass");
 const z=mask=>mass.reduce((a,v,i)=>a+((i&mask)===0?v:0n),0n);
 let masks=0,posteriorChecks=0,zero=0,maxError=0;
 for(let mask=0;mask<16;mask++){
  const b=observeAll(root,"known");root.leaves.forEach((id,j)=>{if(mask&(1<<j))b.fail(id)});
  const truth=Number(z(mask))/Number(den);maxError=Math.max(maxError,Math.abs(truth-b.Z()));
  ok(Math.abs(truth-b.Z())<1e-10&&Math.abs(truth-fullZ(root,"known",b.failed))<1e-10,"exact rational evidence");masks++;
  if(z(mask)===0n){zero++;continue}
  root.leaves.forEach((id,j)=>{if(!(mask&(1<<j))){
   const p=1-Number(z(mask|(1<<j)))/Number(z(mask)),q=b.query(id)[root.target];maxError=Math.max(maxError,Math.abs(p-q));ok(Math.abs(p-q)<1e-10,"exact rational posterior");posteriorChecks++;
  }});
 }
 return {seed:root.seed,regime:root.regime,paths,masks,posteriorChecks,zero,maxError};
}
const sumBig=a=>a.reduce((s,v)=>s+v,0n);
function combos(a,k){
 const out=[];function rec(i,x){if(x.length===k){out.push(x);return}for(let j=i;j<=a.length-(k-x.length);j++)rec(j+1,x.concat(a[j]))}
 rec(0,[]);return out;
}
function optimize(root,k,marg,stats){
 let best=null,bestZ=Infinity;
 for(const subset of combos(root.leaves,k)){
  const z=fullZ(root,"known",new Set(subset),stats);
  if(quant(z)<quant(bestZ)){bestZ=z;best=subset}
 }
 ok(best&&best.length===k,"oracle subset");
 return best.sort((a,b)=>quant(marg[b])-quant(marg[a])||b-a);
}
function rankIds(ids,score){return ids.map(id=>({id,s:quant(score(id))})).sort((a,b)=>b.s-a.s||b.id-a.id).map(x=>x.id)}
function plan(root,kind,k,diagnostic=false){
 const model=kind.startsWith("learned")?"learned":"known",feedback=kind.endsWith("Feedback");
 const b=["depth","random"].includes(kind)?null:observeAll(root,model),marg={},failed=[],order=[],costs=[],audit={checks:0,maxError:0};
 if(b&&!feedback)for(const id of root.leaves)marg[id]=b.query(id)[root.target];
 for(let j=0;j<k;j++){
  const remaining=root.leaves.filter(id=>!order.includes(id)),score={};
  for(const id of remaining){
   score[id]=kind==="depth"?id:kind==="random"?key(root.seed,id):feedback?b.query(id)[root.target]:marg[id]-(kind==="diversity"?diversity(id,failed,root.depth):0);
   if(diagnostic&&feedback&&b.Z()>1e-14){
    const z=fullZ(root,model,b.failed),next=fullZ(root,model,new Set([...b.failed,id])),error=Math.abs(score[id]-(1-next/z));
    audit.checks++;audit.maxError=Math.max(audit.maxError,error);ok(error<1e-10&&Math.abs(z-b.Z())<1e-10,"full posterior comparison");
   }
  }
  const id=rankIds(remaining,i=>score[i])[0];order.push(id);costs.push(b?b.snapshot():{observed:0,upEdges:0,downEdges:0,queries:0,fallbacks:0,peakCacheSlots:0});
  if(j+1<k){failed.push(id);if(feedback)b.fail(id)}
 }
 return {order,costs,audit};
}
function actualProbe(root,order){
 let success=false,probes=0;
 for(const id of order){probes++;if(terminal(root,id)){success=true;break}}
 ok(probes<=order.length&&new Set(order).size===order.length,"probe accounting");
 return {success,probes};
}
function expectedProbe(root,order){
 let expected=0,failed=new Set(),z=1;
 for(const id of order){expected+=z;failed.add(id);z=fullZ(root,"known",failed)}
 return {value:1-z,expected};
}
const kinds=["depth","random","knownMarginal","learnedMarginal","diversity","knownFeedback","learnedFeedback","oracle"];
function terminalExperiment(regime){
 const roots=Array.from({length:192},(_,i)=>tree(1550001+i,regime,3)),rows=[],paired=[],oracleStats={calls:0,edges:0},fullAudit={checks:0,maxError:0};
 let executedPrefix=0,terminalChecks=0,logicalEpisodes=0,eligible=0;
 for(const r of roots){
  for(let i=2;i<r.nodes.length;i++){ok(verify(r.nodes[i].cert)==="valid"&&checkCert(r.nodes[i].cert),"prefix verification");executedPrefix++}
  eligible+=Number(r.leaves.some(id=>terminal(r,id)));
 }
 for(const k of [2,4]){
  const records=Object.fromEntries(kinds.map(x=>[x,[]]));
  for(let index=0;index<roots.length;index++){
   const r=roots[index],marg={},b=observeAll(r,"known");
   for(const id of r.leaves)marg[id]=b.query(id)[r.target];
   const opt=optimize(r,k,marg,oracleStats),best=expectedProbe(r,opt).value;
   for(const kind of kinds){
    const p=kind==="oracle"?{order:opt,costs:null,audit:{checks:0,maxError:0}}:plan(r,kind,k,index<16);
    const actual=actualProbe(r,p.order),e=expectedProbe(r,p.order),regret=best-e.value;
    ok(regret>=-1e-10,"oracle regret");
    if(regime==="independent")ok(Math.abs(e.value-(1-(5/6)**k))<1e-10,"independent control");
    fullAudit.checks+=p.audit.checks;fullAudit.maxError=Math.max(fullAudit.maxError,p.audit.maxError);
    terminalChecks+=actual.probes;logicalEpisodes++;
    const cost=p.costs?p.costs[actual.probes-1]:null;
    records[kind].push({...actual,...e,regret,cost,order:p.order});
   }
  }
  for(const kind of kinds){
   const a=records[kind],s=key=>sum(a.map(v=>v[key])),cost=key=>kind==="oracle"?null:sum(a.map(v=>v.cost[key]));
   rows.push({regime,k,kind,n:a.length,solved:a.filter(x=>x.success).length,expectedSuccess:s("value")/a.length,meanRegret:s("regret")/a.length,meanExpectedProbes:s("expected")/a.length,meanActualProbes:s("probes")/a.length,meanCalls:14+s("probes")/a.length,upEdges:cost("upEdges"),downEdges:cost("downEdges"),queries:cost("queries"),fallbacks:cost("fallbacks"),peakCacheSlots:kind==="oracle"?null:Math.max(...a.map(v=>v.cost.peakCacheSlots))});
  }
  for(const kind of ["knownFeedback","learnedFeedback","oracle"])for(const ref of ["knownMarginal","learnedMarginal","diversity","knownFeedback"]){
   if(kind===ref)continue;const a=records[kind],b=records[ref];
   paired.push({regime,k,kind,ref,...exactPaired(a,b),meanExpectedGain:sum(a.map((v,i)=>v.value-b[i].value))/a.length,orderChanges:a.filter((v,i)=>v.order.join(",")!==b[i].order.join(",")).length});
  }
 }
 return {roots:roots.length,eligible,executedPrefix,logicalPrefix:logicalEpisodes*14,terminalChecks,logicalEpisodes,oracleStats,fullAudit,rows,paired,falseAccepts:0};
}
const adaptiveKinds=["depth","depthRandom","knownMarginal","learnedMarginal","knownFeedback","learnedFeedback","diversity"];
function runAdaptive(root,kind,cap,budget){
 const model=kind.startsWith("learned")?"learned":"known",feedback=kind.endsWith("Feedback"),b=kind==="depth"||kind==="depthRandom"?null:new Belief(model,root.target),F=b?future(model,root.regime,root.depth):null;
 let bank=[1],failed=[],calls=0,prefix=0,probes=0,scoreReads=0,peakBank=1,transient=1,success=false,trace=[],reached=new Set([1]),expanded=new Set();
 function score(id){
  const d=dep(id);if(kind==="depth")return 2*d;
  if(kind==="depthRandom")return 2*d+key(root.seed,id);
  const p=b.query(id),q=row(p,F[d])[root.target];
  return 2*d+q-(kind==="diversity"?diversity(id,failed,root.depth):0);
 }
 while(bank.length&&calls<budget){
  const id=bank.shift();ok(reached.has(id)&&!expanded.has(id),"expansion frontier");expanded.add(id);
  if(dep(id)===root.depth){
   calls++;probes++;success=terminal(root,id);trace.push({type:"probe",id,success});
   if(success)break;
   failed.push(id);if(feedback)b.fail(id);
  }else{
   for(const child of [id*2,id*2+1]){
    if(calls>=budget)break;const n=root.nodes[child];
    calls++;prefix++;ok(verify(n.cert)==="valid"&&checkCert(n.cert),"edge certificate");ok(!reached.has(child),"repeat edge");reached.add(child);
    if(b)b.observe(child,id,n.a,n.c);bank.push(child);trace.push({type:"edge",id:child,parent:id});
   }
  }
  transient=Math.max(transient,bank.length);scoreReads+=bank.length;bank=rankIds(bank,score).slice(0,cap);peakBank=Math.max(peakBank,bank.length);
 }
 ok(calls===prefix+probes&&calls<=budget&&peakBank<=cap&&transient<=cap+1,"adaptive accounting");
 const seen=new Set([1]),checked=new Set(),terminalSeen=new Set();let hit=false;
 for(const t of trace){
  ok(!hit,"event after success");
  if(t.type==="edge"){ok(seen.has(t.parent)&&t.id>>1===t.parent&&!checked.has(t.id)&&checkCert(root.nodes[t.id].cert),"edge replay");checked.add(t.id);seen.add(t.id)}
  else{ok(seen.has(t.id)&&dep(t.id)===root.depth&&!terminalSeen.has(t.id),"probe replay");terminalSeen.add(t.id);hit=terminal(root,t.id);ok(hit===t.success,"terminal replay")}
 }
 ok(hit===success&&calls===trace.length,"replay end");
 return {success,calls,prefix,probes,scoreReads,peakBank,transient,ops:b?b.snapshot():{observed:0,upEdges:0,downEdges:0,queries:0,fallbacks:0,peakCacheSlots:0}};
}
function adaptiveExperiment(regime){
 const roots=Array.from({length:192},(_,i)=>tree(1560001+i,regime)),rows=[],paired=[];let episodes=0,checkedCalls=0;
 for(const [cap,budget] of [[4,24],[16,48]]){
  const all={};
  for(const kind of adaptiveKinds){
   const a=roots.map(r=>runAdaptive(r,kind,cap,budget));all[kind]=a;episodes+=a.length;const s=k=>sum(a.map(x=>x[k])),o=k=>sum(a.map(x=>x.ops[k]));checkedCalls+=s("calls");
   rows.push({regime,cap,budget,kind,n:a.length,solved:a.filter(x=>x.success).length,meanCalls:s("calls")/a.length,prefix:s("prefix"),probes:s("probes"),scoreReads:s("scoreReads"),peakBank:Math.max(...a.map(x=>x.peakBank)),transient:Math.max(...a.map(x=>x.transient)),upEdges:o("upEdges"),downEdges:o("downEdges"),queries:o("queries"),fallbacks:o("fallbacks"),peakCacheSlots:Math.max(...a.map(x=>x.ops.peakCacheSlots))});
  }
  for(const kind of ["knownFeedback","learnedFeedback"])for(const ref of adaptiveKinds){if(kind===ref)continue;paired.push({regime,cap,budget,kind,ref,...exactPaired(all[kind],all[ref])})}
 }
 return {roots:roots.length,episodes,checkedCalls,rows,paired,falseAccepts:0};
}
function experiment09(){
 const begin=Date.now(),audit=Array.from({length:4},(_,i)=>exactEnumeration(tree(1540001+i,i<2?"correlated":"independent",2)));
 const probe={},adaptive={};
 for(const regime of ["correlated","independent"]){probe[regime]=terminalExperiment(regime);adaptive[regime]=adaptiveExperiment(regime)}
 return {status:"PASS",scope:"synthetic shared-prefix tree inference and search, not factoring",audit,probe,adaptive,backend:FACTORIZED?"factorized":"dense",sharedTransitionSlots:36*OPERATORS.size,sharedPermutationMetadataSlots:OPERATORS.size*(N+1),elapsedMs:Date.now()-begin};
}
console.log(JSON.stringify(experiment09(),null,2));
