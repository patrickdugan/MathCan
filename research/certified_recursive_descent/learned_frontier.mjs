// CRD-03 registered experiment. Node >=18.
import {verify} from "./audit.mjs";
import {rng, makeRoot} from "./search.mjs";
function ok(x,m){if(!x)throw Error(m)}

function dep(id){return id==="start"?0:Number(id.slice(1,id.indexOf(":")))}

function sigmoid(x){return 1/(1+Math.exp(-Math.max(-30,Math.min(30,x))))}

function oracle(root){
 const memo=new Map([[root.goal,true]]);
 function rec(id){if(memo.has(id))return memo.get(id);const yes=(root.adj[id]||[]).some(e=>verify(e.cert)==="valid"&&rec(e.dst));memo.set(id,yes);return yes}
 ok(rec("start"),"unsolvable");
 return rec;
}

function features(e,ctx){const d=dep(e.id);return [d/ctx.depth,(ctx.depth-d)/10,Math.min(2,(ctx.calls-e.birth)/64),Math.min(4,ctx.inDegree.get(e.id)||0)/4,(ctx.layerCount[d]||0)/ctx.width,e.sibling,(ctx.budget-ctx.calls)/ctx.budget]}

function episode(root,budget,cap,policy,collect=null){
 const rand=rng((root.seed^0xAC1D91E3)>>>0),ctx={depth:root.depth,width:root.width,budget,calls:0,inDegree:new Map(),layerCount:[]};
 let bank=[{id:"start",birth:0,order:0,key:rand(),sibling:1,path:[]}],seq=1,peak=1,transient=1,scores=0,invalid=0,duplicates=0,evictions=0,success=false,path=[],trace=[],expansions=[];
 const expanded=new Set();
 while(bank.length&&ctx.calls<budget){
  const current=bank.shift();ok(!expanded.has(current.id),"repeat expand");
  expanded.add(current.id);const d=dep(current.id);ctx.layerCount[d]=(ctx.layerCount[d]||0)+1;expansions.push(current.id);
  let checked=0,valid=0,added=[];
  for(const e of root.adj[current.id]||[]){
   if(ctx.calls>=budget)break;
   ctx.calls++;checked++;
   const result=verify(e.cert);trace.push({src:e.src,dst:e.dst,result});
   if(result!=="valid"){invalid++;continue}
   valid++;ctx.inDegree.set(e.dst,(ctx.inDegree.get(e.dst)||0)+1);
   if(e.dst===root.goal){success=true;path=[...current.path,e];break}
   if(expanded.has(e.dst)||bank.some(x=>x.id===e.dst)||added.some(x=>x.id===e.dst)){duplicates++;continue}
   added.push({id:e.dst,birth:ctx.calls,order:seq++,key:rand(),sibling:0,path:[...current.path,e]});
  }
  if(success)break;
  for(const e of added)e.sibling=valid/Math.max(1,checked);
  bank.push(...added);transient=Math.max(transient,bank.length);
  if(collect)for(const e of bank)collect(features(e,ctx),e.id);
  const rank=bank.map(e=>({e,s:policy(e,ctx)}));scores+=rank.length;
  rank.sort((a,b)=>b.s-a.s||b.e.order-a.e.order);
  evictions+=Math.max(0,rank.length-cap);bank=rank.slice(0,cap).map(r=>r.e);
  peak=Math.max(peak,bank.length);
 }
 return {success,calls:ctx.calls,peak,transient,scores,invalid,duplicates,evictions,path,trace,expansions};
}

function replay(root,x,budget,cap){
 ok(x.calls===x.trace.length&&x.calls<=budget&&x.peak<=cap&&x.transient<=cap+4,"accounting");
 const reached=new Set(["start"]),expanded=new Set(),seen=new Set();let at=0,hit=false;
 const valid=c=>BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum);
 for(const id of x.expansions){
  ok(!hit&&reached.has(id)&&!expanded.has(id),"expansion replay");expanded.add(id);
  for(const e of root.adj[id]||[]){
   if(at>=budget||hit)break;
   const t=x.trace[at++];ok(t&&t.src===id&&t.dst===e.dst&&!seen.has(id+"->"+e.dst),"trace");
   seen.add(id+"->"+e.dst);const v=valid(e.cert);ok(v===(t.result==="valid"),"exact certificate");
   if(v){reached.add(e.dst);hit=e.dst===root.goal}
  }
 }
 ok(at===x.calls&&hit===x.success,"replay stop");
 if(hit){let at="start";for(const e of x.path){ok(e.src===at&&valid(e.cert)&&root.adj[at].includes(e),"bad path");at=e.dst}ok(at===root.goal&&x.path.length===root.depth,"bad goal")}
 else ok(!x.path.length,"false path");
}

function init(kind,seed){
 const rand=rng(seed),n=kind==="linear"?8:137;
 return Array.from({length:n},(_,i)=>(rand()-.5)*.2);
}

function forward(w,x,kind){
 if(kind==="linear")return {p:sigmoid(w[7]+x.reduce((s,v,j)=>s+v*w[j],0))};
 const states=[Array(8).fill(0)];
 for(let t=0;t<3;t++){const h=states[t],next=[];for(let i=0;i<8;i++){let z=w[120+i];for(let j=0;j<7;j++)z+=w[i*7+j]*x[j];for(let j=0;j<8;j++)z+=w[56+i*8+j]*h[j];next.push(Math.tanh(z))}states.push(next)}
 let z=w[136];for(let i=0;i<8;i++)z+=w[128+i]*states[3][i];return {p:sigmoid(z),states};
}

function grad(w,x,y,kind,g){
 const {p,states}=forward(w,x,kind),dz=p-y;
 if(kind==="linear"){for(let j=0;j<7;j++)g[j]+=dz*x[j];g[7]+=dz;return}
 g[136]+=dz;let dh=[];
 for(let i=0;i<8;i++){g[128+i]+=dz*states[3][i];dh[i]=dz*w[128+i]}
 for(let t=3;t>=1;t--){
  const prev=Array(8).fill(0);
  for(let i=0;i<8;i++){const a=dh[i]*(1-states[t][i]**2);g[120+i]+=a;for(let j=0;j<7;j++)g[i*7+j]+=a*x[j];for(let j=0;j<8;j++){g[56+i*8+j]+=a*states[t-1][j];prev[j]+=a*w[56+i*8+j]}}
  dh=prev;
 }
}

function gradientCheck(){
 const x=[.1,.2,.3,.4,.5,.6,.7],y=1;let max=0;
 for(const kind of ["linear","recurrent"]){const w=init(kind,777),g=w.map(()=>0);grad(w,x,y,kind,g);for(let i=0;i<w.length;i++){const orig=w[i],eps=1e-5;w[i]=orig+eps;const a=-Math.log(forward(w,x,kind).p);w[i]=orig-eps;const b=-Math.log(forward(w,x,kind).p);w[i]=orig;max=Math.max(max,Math.abs(g[i]-(a-b)/(2*eps)))}}
 ok(max<1e-6,"gradient error");return max;
}

function exactPaired(a,b){
 let win=0,loss=0;for(let i=0;i<a.length;i++){win+=Number(a[i].success&&!b[i].success);loss+=Number(!a[i].success&&b[i].success)}
 const n=win+loss,k=Math.min(win,loss);let term=2**(-n),sum=term;for(let j=1;j<=k;j++){term*=((n-j+1)/j);sum+=term}return {win,loss,p:Math.min(1,2*sum)};
}

function experiment03(){
 const start=Date.now(),gradientError=gradientCheck();
 const roots=(start,n,split)=>Array.from({length:n},(_,i)=>makeRoot(start+i,split));
 const dev=roots(410001,512,"development"),validation=roots(520001,128,"validation");
 const fixed={lifo:e=>e.order,fifo:e=>-e.order,random:e=>e.key,depth:e=>dep(e.id)*10000+e.order};
 let data=[],positives=0,trainingEpisodes=0;
 for(const root of dev){const label=oracle(root);for(const cap of [4,16])for(const name of ["lifo","random"]){const x=episode(root,64,cap,fixed[name],(f,id)=>{const y=Number(label(id));data.push({f,y});positives+=y});replay(root,x,64,cap);trainingEpisodes++}}
 const choices={},learning=[];
 for(const kind of ["linear","recurrent"]){
  const w=init(kind,kind==="linear"?502:503),rand=rng(711),lr=.08;let best=null;
  for(let epoch=1;epoch<=16;epoch++){
   for(let batch=0;batch<64;batch++){const g=w.map(()=>0);for(let j=0;j<32;j++){const row=data[Math.floor(rand()*data.length)];grad(w,row.f,row.y,kind,g)}for(let i=0;i<w.length;i++)w[i]-=lr*g[i]/32}
   if([1,4,8,16].includes(epoch)){
    let solved=0,calls=0;const pred=(e,c)=>forward(w,features(e,c),kind).p;
    for(const r of validation){const x=episode(r,64,4,pred);replay(r,x,64,4);solved+=Number(x.success);calls+=x.calls}
    const ck={kind,epoch,solved,calls,weights:w.slice()};learning.push({kind,epoch,solved,calls});
    if(!best||solved>best.solved||(solved===best.solved&&calls<best.calls))best=ck;
   }
  }
  choices[kind]=best;
 }
 // Selection is finalized before constructing the test roots.
 const test=roots(630001,256,"heldout"),policies={...fixed};
 for(const kind of ["linear","recurrent"])policies[kind]=(e,c)=>forward(choices[kind].weights,features(e,c),kind).p;
 const rows=[],paired=[];let testEpisodes=0,checkedCalls=0;
 for(const cap of [4,16])for(const budget of [32,64,128]){
  const all={};
  for(const [name,policy] of Object.entries(policies)){
   const results=test.map(r=>{const x=episode(r,budget,cap,policy);replay(r,x,budget,cap);testEpisodes++;checkedCalls+=x.calls;return x});
   all[name]=results;
   rows.push({cap,budget,policy:name,solved:results.filter(r=>r.success).length,roots:results.length,meanCalls:results.reduce((n,r)=>n+r.calls,0)/results.length,scoreEvaluations:results.reduce((n,r)=>n+r.scores,0),peak:Math.max(...results.map(r=>r.peak)),transient:Math.max(...results.map(r=>r.transient)),evictions:results.reduce((n,r)=>n+r.evictions,0)});
  }
  for(const ref of ["depth","linear","lifo","random"])paired.push({cap,budget,policy:"recurrent",reference:ref,...exactPaired(all.recurrent,all[ref])});
 }
 return {status:"PASS",scope:"synthetic recurrent scorer; no factoring result",gradientError,training:{roots:dev.length,episodes:trainingEpisodes,examples:data.length,positives,epochs:16,batchesPerEpoch:64,batchSize:32,learningRate:.08,parameters:{linear:8,recurrent:137}},validationRoots:validation.length,learning,choices,testRoots:test.length,testEpisodes,checkedCalls,rows,paired,falseAccepts:0,elapsedMs:Date.now()-start};
}

console.log(JSON.stringify(experiment03(),null,2));
