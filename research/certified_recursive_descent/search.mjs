// CRD-02 synthetic search and exact receipt replay. Node >=18.
import { verify, upperRoot } from "./audit.mjs";
function check(ok,msg){if(!ok)throw Error(msg)}

function rng(seed){let s=seed>>>0;return ()=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)/4294967296}}

function shuffle(xs,rand){const a=xs.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(rand()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}

function makeRoot(seed,split){
 const rand=rng(seed),pick=n=>Math.floor(rand()*n);
 const cfg={development:[4,5,7,11,3],validation:[6,7,13,17,3],heldout:[8,10,19,23,4]}[split];
 if(!cfg)throw Error("split");
 const [minDepth,maxDepth,pd0,pd1,degree]=cfg,depth=minDepth+pick(maxDepth-minDepth+1),width=split==="heldout"?9:6;
 const layers=[["start"],...Array.from({length:depth},(_,i)=>Array.from({length:width},(_,j)=>`L${i+1}:${j}`))];
 const planted=layers.map(layer=>layer[pick(layer.length)]),goal=planted[depth],adj={};
 const cert=valid=>{
  const pDen=pick(2)?pd0:pd1,pNum=1+pick(pDen-1),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=[4000,8000,10400,16000][pick(4)];
  const a=Math.floor((c*(rDen-rNum)-1)/rDen);
  const b={pNum,pDen,rNum,rDen,a,c};
  if(valid)return b;
  return pick(2)?{...b,a:a+1}:{...b,rNum:rNum-1};
 };
 for(let d=0;d<depth;d++)for(const src of layers[d]){
  let targets=shuffle(layers[d+1],rand).slice(0,degree);
  if(src===planted[d]&&!targets.includes(planted[d+1]))targets[targets.length-1]=planted[d+1];
  adj[src]=shuffle(targets.map(dst=>({src,dst,cert:cert((src===planted[d]&&dst===planted[d+1])||rand()<0.42)})),rand);
 }
 return {seed,split,depth,width,goal,adj};
}

function run(root,budget,capacity){
 let active=root.adj.start.slice().reverse(),deferred=[],reached=new Set(["start"]),parents=new Map(),calls=0,invalid=0,duplicates=0,dropped=0,peakDeferred=0,peakActive=active.length;
 const trace=[];
 while(calls<budget&&(active.length||deferred.length)){
  const e=active.length?active.pop():deferred.pop();
  calls++;
  const result=verify(e.cert);trace.push({src:e.src,dst:e.dst,result});
  if(result!=="valid"){invalid++;continue}
  if(reached.has(e.dst)){duplicates++;continue}
  reached.add(e.dst);parents.set(e.dst,e);
  if(e.dst===root.goal){
   const path=[];let node=e.dst;while(node!=="start"){const edge=parents.get(node);path.push(edge);node=edge.src}
   return {success:true,calls,invalid,duplicates,dropped,peakDeferred,peakActive,path:path.reverse(),trace};
  }
  deferred.push(...active);
  if(deferred.length>capacity){const excess=deferred.length-capacity;deferred.splice(0,excess);dropped+=excess}
  peakDeferred=Math.max(peakDeferred,deferred.length);
  active=(root.adj[e.dst]||[]).slice().reverse();
  peakActive=Math.max(peakActive,active.length);
 }
 return {success:false,calls,invalid,duplicates,dropped,peakDeferred,peakActive,path:[],trace};
}

function independentCheck(root,result,budget,capacity){
 check(result.calls===result.trace.length&&result.calls<=budget,"call count");
 check(result.peakDeferred<=capacity,"capacity");
 const reached=new Set(["start"]);
 let invalid=0,duplicates=0,hit=false;
 const valid=c=>BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum);
 for(const t of result.trace){
  check(!hit&&reached.has(t.src),"invalid frontier");
  const e=(root.adj[t.src]||[]).find(e=>e.dst===t.dst);check(!!e,"unknown edge");
  const ok=valid(e.cert);check(ok===(t.result==="valid"),"independent arithmetic");
  if(!ok){invalid++;continue}
  if(reached.has(t.dst)){duplicates++;continue}
  reached.add(t.dst);hit=t.dst===root.goal;
 }
 check(hit===result.success&&invalid===result.invalid&&duplicates===result.duplicates,"replay result");
 if(hit){
  check(result.path.length===root.depth,"path length");
  let at="start";for(const edge of result.path){check(edge.src===at&&valid(edge.cert)&&root.adj[at].includes(edge),"path certificate");at=edge.dst}
  check(at===root.goal,"path goal");
 }else check(result.path.length===0,"failure with path");
}

function shortest(root){
 let memo=new Map([[root.goal,0]]);
 function visit(node){
  if(memo.has(node))return memo.get(node);
  let best=Infinity;
  for(const e of root.adj[node]||[])if(verify(e.cert)==="valid")best=Math.min(best,1+visit(e.dst));
  memo.set(node,best);return best;
 }
 return visit("start");
}

function phaseCertificate(){
 const C=[1700,1600],edges=[
  {i:0,j:1,pNum:1,pDen:2,rNum:4,rDen:5,a:400},
  {i:1,j:0,pNum:1,pDen:8,rNum:1,rDen:2,a:700}
 ];
 function validate(constants){
  return edges.every(e=>BigInt(e.rNum)**3n*BigInt(e.pDen)>=BigInt(e.pNum)*BigInt(e.rDen)**3n&&BigInt(e.a)*BigInt(e.rDen)+BigInt(constants[e.j])*BigInt(e.rNum)<BigInt(constants[e.i])*BigInt(e.rDen));
 }
 check(validate(C),"coupled phase certificate");
 check(!validate([1600,1550]),"reject equality at upper-envelope fixed point");
 check(!validate([1700,1500]),"reject insufficient phase constant");
 return {strictCertificate:C,upperEnvelopeFixedPoint:[1600,1500],note:"Exact rational upper-envelope fixed point is [1600,1500]; strict slack tested independently."};
}

function experiment(){
 const splits=[["development",110001,96],["validation",220001,48],["heldout",330001,96]],budgets=[8,16,32,64,128],capacities=[0,4,16,64,Infinity],rows=[];
 let roots=0,replays=0,checkedCalls=0;
 for(const [split,start,count] of splits){
  const rs=Array.from({length:count},(_,i)=>makeRoot(start+i,split));roots+=count;
  for(const r of rs)check(shortest(r)===r.depth,"unreachable root");
  for(const budget of budgets){
   let baseline=null;
   for(const cap of capacities){
    const results=rs.map(r=>{const x=run(r,budget,cap);independentCheck(r,x,budget,cap);replays++;checkedCalls+=x.calls;return x;});
    if(!baseline)baseline=results;
    let gain=0,loss=0,success=0,calls=0,successCalls=0,peak=0,drop=0;
    results.forEach((r,i)=>{success+=Number(r.success);calls+=r.calls;successCalls+=r.success?r.calls:0;peak=Math.max(peak,r.peakDeferred);drop+=r.dropped;gain+=Number(r.success&&!baseline[i].success);loss+=Number(!r.success&&baseline[i].success)});
    rows.push({split,budget,capacity:Number.isFinite(cap)?cap:"unbounded",roots:count,success,gain,loss,totalCalls:calls,meanCalls:calls/count,meanSuccessCalls:success?successCalls/success:null,peakDeferred:peak,dropped:drop});
   }
  }
 }
 const phase=phaseCertificate();
 return {status:"PASS",scope:"synthetic exact search; no neural training",roots,replays,checkedCalls,phase,rows};
}

console.log(JSON.stringify(experiment(),null,2));
