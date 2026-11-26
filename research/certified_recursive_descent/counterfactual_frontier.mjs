// CRD-04 registered counterfactual utility pilot. Node >=18.
import {verify} from "./audit.mjs";
import {rng,makeRoot} from "./search.mjs";
import {ok,dep,sigmoid,features,replay,init,forward,grad,exactPaired} from "./learned_frontier.mjs";
function copy04(s){
 return {...s,ctx:{...s.ctx,inDegree:new Map(s.ctx.inDegree),layerCount:s.ctx.layerCount.slice()},bank:s.bank.slice(),expanded:new Set(s.expanded),trace:s.trace.slice(),expansions:s.expansions.slice()};
}

function episode04(root,budget,cap,policy,collector=null,snapshot=null,forced=null){
 const key=order=>rng((root.seed^0xAC1D91E3^Math.imul(order+1,0x9E3779B9))>>>0)();
 const s=snapshot?copy04(snapshot):{ctx:{depth:root.depth,width:root.width,budget,calls:0,inDegree:new Map(),layerCount:[]},bank:[{id:"start",birth:0,order:0,key:key(0),sibling:1,path:[]}],seq:1,peak:1,transient:1,scores:0,invalid:0,duplicates:0,evictions:0,success:false,path:[],trace:[],expansions:[],expanded:new Set()};
 const {ctx}=s;
 function schedule(force=null){
  const rank=s.bank.map(e=>({e,score:policy(e,ctx)}));s.scores+=rank.length;
  rank.sort((a,b)=>b.score-a.score||b.e.order-a.e.order);
  if(force!==null){const i=rank.findIndex(r=>r.e.id===force);ok(i>=0,"forced candidate absent");rank.unshift(rank.splice(i,1)[0])}
  s.evictions+=Math.max(0,rank.length-cap);s.bank=rank.slice(0,cap).map(r=>r.e);s.peak=Math.max(s.peak,s.bank.length);
 }
 if(snapshot){ok(s.ctx.budget===budget&&forced!==null,"bad resume");schedule(forced)}
 while(s.bank.length&&ctx.calls<budget){
  const current=s.bank.shift();ok(!s.expanded.has(current.id),"repeat expand");
  s.expanded.add(current.id);const d=dep(current.id);ctx.layerCount[d]=(ctx.layerCount[d]||0)+1;s.expansions.push(current.id);
  let checked=0,valid=0,added=[];
  for(const e of root.adj[current.id]||[]){
   if(ctx.calls>=budget)break;
   ctx.calls++;checked++;
   const result=verify(e.cert);s.trace.push({src:e.src,dst:e.dst,result});
   if(result!=="valid"){s.invalid++;continue}
   valid++;ctx.inDegree.set(e.dst,(ctx.inDegree.get(e.dst)||0)+1);
   if(e.dst===root.goal){s.success=true;s.path=[...current.path,e];break}
   if(s.expanded.has(e.dst)||s.bank.some(x=>x.id===e.dst)||added.some(x=>x.id===e.dst)){s.duplicates++;continue}
   const order=s.seq++;added.push({id:e.dst,birth:ctx.calls,order,key:key(order),sibling:0,path:[...current.path,e]});
  }
  if(s.success)break;
  for(const e of added)e.sibling=valid/Math.max(1,checked);
  s.bank.push(...added);s.transient=Math.max(s.transient,s.bank.length);
  if(collector&&s.bank.length>=2&&ctx.calls<budget)collector(s);
  schedule();
 }
 return {success:s.success,calls:ctx.calls,peak:s.peak,transient:s.transient,scores:s.scores,invalid:s.invalid,duplicates:s.duplicates,evictions:s.evictions,path:s.path,trace:s.trace,expansions:s.expansions};
}

function pairGrad(w,row,kind,g){
 const a=forward(w,row.a,kind).p,b=forward(w,row.b,kind).p;
 const logit=p=>Math.log(p/(1-p)),z=logit(a)-logit(b),d=sigmoid(z)-row.y;
 grad(w,row.a,a-d,kind,g);grad(w,row.b,b+d,kind,g);
}

function pairCheck(){
 const row={a:[.1,.2,.3,.4,.5,.6,.7],b:[.2,.4,.1,.6,.3,.5,.2],y:1};let max=0;
 for(const kind of ["linear","recurrent"]){
  const w=init(kind,892),g=w.map(()=>0);pairGrad(w,row,kind,g);
  const loss=()=>{const a=forward(w,row.a,kind).p,b=forward(w,row.b,kind).p;return -Math.log(sigmoid(Math.log(a/(1-a))-Math.log(b/(1-b))))};
  for(let i=0;i<w.length;i++){const z=w[i],eps=1e-5;w[i]=z+eps;const a=loss();w[i]=z-eps;const b=loss();w[i]=z;max=Math.max(max,Math.abs(g[i]-(a-b)/(2*eps)))}
 }
 ok(max<1e-6,"pair gradient");return max;
}

function experiment04(){
 const started=Date.now(),gradientError=pairCheck(),data=[],fixed={depth:e=>dep(e.id),depthRandom:e=>2*dep(e.id)+e.key,fifo:e=>-e.order,random:e=>e.key};
 let teacherRollouts=0,teacherCalls=0,prefixReplayCalls=0,trainEpisodes=0,contexts=0,ties=0,tieSuccess=0,positive=0,negative=0,sameDepth=0,sameDepthDisagree=0,teacherSuccess=0;
 const remainingStats={};
 for(let i=0;i<384;i++){
  const root=makeRoot(710001+i,i<192?"development":"validation"),budget=[24,40,64][i%3];
  for(const cap of [4,16])for(const name of ["depth","random"]){
   let sample=[],seen=0;const rand=rng((root.seed^Math.imul(cap,29)^(name==="depth"?0xC3:0xD5))>>>0);
   const collect=s=>{seen++;if(sample.length<3)sample.push(copy04(s));else{const j=Math.floor(rand()*seen);if(j<3)sample[j]=copy04(s)}};
   const behavior=episode04(root,budget,cap,fixed[name],collect);replay(root,behavior,budget,cap);trainEpisodes++;
   for(const s of sample){
    contexts++;const items=s.bank.map(e=>{const r=episode04(root,budget,cap,fixed.depth,null,s,e.id);replay(root,r,budget,cap);ok(r.expansions[s.expansions.length]===e.id,"forced action not executed");teacherRollouts++;teacherCalls+=r.calls-s.ctx.calls;prefixReplayCalls+=s.ctx.calls;teacherSuccess+=Number(r.success);return {f:features(e,s.ctx),y:Number(r.success),depth:dep(e.id)}});
    for(let a=0;a<items.length;a++)for(let b=a+1;b<items.length;b++){
     const x=items[a],z=items[b],y=x.y===z.y?.5:Number(x.y>z.y);
     if(y===.5){ties++;tieSuccess+=x.y}else if(y===1)positive++;else negative++;
     if(x.depth===z.depth){sameDepth++;sameDepthDisagree+=Number(y!==.5)}
     const key=Math.floor((budget-s.ctx.calls)/8)*8;const stat=remainingStats[key]??={pairs:0,disagree:0};stat.pairs++;stat.disagree+=Number(y!==.5);
     data.push({a:x.f,b:z.f,y});
    }
   }
  }
 }
 ok(data.length===ties+positive+negative&&positive+negative>0,"missing labels");
 const validation=Array.from({length:128},(_,i)=>makeRoot(820001+i,"validation")),choices={},learning=[];
 for(const kind of ["linear","recurrent"]){
  const w=init(kind,kind==="linear"?502:503),rand=rng(711);let best=null;
  for(let epoch=1;epoch<=16;epoch++){
   for(let batch=0;batch<64;batch++){const g=w.map(()=>0);for(let j=0;j<32;j++)pairGrad(w,data[Math.floor(rand()*data.length)],kind,g);for(let k=0;k<w.length;k++)w[k]-=.08*g[k]/32}
   if([1,4,8,16].includes(epoch)){
    const pred=(e,c)=>2*dep(e.id)+forward(w,features(e,c),kind).p;
    let solved=0,calls=0;for(const r of validation){const x=episode04(r,64,4,pred);replay(r,x,64,4);solved+=Number(x.success);calls+=x.calls}
    const ck={kind,epoch,solved,calls,weights:w.slice()};learning.push({kind,epoch,solved,calls});if(!best||solved>best.solved||(solved===best.solved&&calls<best.calls))best=ck;
   }
  }
  choices[kind]=best;
 }
 // Test roots are generated only after checkpoint selection.
 const test=Array.from({length:256},(_,i)=>makeRoot(930001+i,"heldout"));
 const policies={...fixed,linearResidual:(e,c)=>2*dep(e.id)+forward(choices.linear.weights,features(e,c),"linear").p,recurrentResidual:(e,c)=>2*dep(e.id)+forward(choices.recurrent.weights,features(e,c),"recurrent").p,recurrentUnrestricted:(e,c)=>forward(choices.recurrent.weights,features(e,c),"recurrent").p};
 const rows=[],paired=[];let testEpisodes=0,checkedCalls=0;
 for(const cap of [4,16])for(const budget of [32,64,128]){
  const all={};for(const [name,policy] of Object.entries(policies)){
   const results=test.map(r=>{const x=episode04(r,budget,cap,policy);replay(r,x,budget,cap);testEpisodes++;checkedCalls+=x.calls;return x});all[name]=results;
   rows.push({cap,budget,policy:name,solved:results.filter(r=>r.success).length,roots:results.length,meanCalls:results.reduce((n,r)=>n+r.calls,0)/results.length,scoreEvaluations:results.reduce((n,r)=>n+r.scores,0),peak:Math.max(...results.map(r=>r.peak)),transient:Math.max(...results.map(r=>r.transient)),evictions:results.reduce((n,r)=>n+r.evictions,0)});
  }
  for(const ref of ["depth","depthRandom","linearResidual","recurrentUnrestricted"])paired.push({cap,budget,policy:"recurrentResidual",reference:ref,...exactPaired(all.recurrentResidual,all[ref])});
 }
 return {status:"PASS",scope:"synthetic counterfactual utility, exact paired replay",gradientError,trainRoots:384,trainEpisodes,contexts,teacherRollouts,teacherCalls,prefixReplayCalls,teacherSuccess,pairs:data.length,ties,tieSuccess,tieFailure:ties-tieSuccess,positive,negative,sameDepth,sameDepthDisagree,remainingStats,learning,choices,validationRoots:128,testRoots:256,testEpisodes,checkedCalls,rows,paired,falseAccepts:0,elapsedMs:Date.now()-started};
}

console.log(JSON.stringify(experiment04(),null,2));
