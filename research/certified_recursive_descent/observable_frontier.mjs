// CRD-05 registered typed observability and exact replay. Node >=18.
import {verify,upperRoot} from "./audit.mjs";
import {rng,shuffle,makeRoot} from "./search.mjs";
import {ok,dep,sigmoid,replay,init,forward,grad,exactPaired} from "./learned_frontier.mjs";
function tags05(root,latent=null){
 const rand=rng((root.seed^0xA1B2C3D4)>>>0),perm=rng((root.seed^0x165667B1)>>>0);
 const ids=["start",...Array.from({length:root.depth},(_,i)=>Array.from({length:root.width},(_,j)=>`L${i+1}:${j}`)).flat()];
 const tag={},scrambled={};
 for(const id of ids)tag[id]=latent?Number(rand()<.85?latent[id]:!latent[id]):Number(rand()<.5);
 scrambled.start=tag.start;
 for(let d=1;d<=root.depth;d++){
  const layer=ids.filter(id=>dep(id)===d),vals=shuffle(layer.map(id=>tag[id]),perm);
  layer.forEach((id,i)=>scrambled[id]=vals[i]);
  ok(layer.reduce((v,id)=>v+tag[id],0)===layer.reduce((v,id)=>v+scrambled[id],0),"tag histogram");
 }
 return {...root,tag,scrambled,outdegree:root.depth>=8?4:3};
}

function makeTyped05(seed,split){
 const rand=rng(seed),pick=n=>Math.floor(rand()*n),cfg={development:[4,5,7,11,3],validation:[6,7,13,17,3],heldout:[8,10,19,23,4]}[split];
 const [min,max,pd0,pd1,degree]=cfg,depth=min+pick(max-min+1),width=split==="heldout"?9:6;
 const layers=[["start"],...Array.from({length:depth},(_,i)=>Array.from({length:width},(_,j)=>`L${i+1}:${j}`))];
 const planted=layers.map(layer=>layer[pick(layer.length)]),latent={},adj={};
 for(const layer of layers)for(const id of layer)latent[id]=rand()<.5;
 for(const id of planted)latent[id]=true;
 function cert(valid){
  const pDen=pick(2)?pd0:pd1,pNum=1+pick(pDen-1),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=[4000,8000,10400,16000][pick(4)],a=Math.floor((c*(rDen-rNum)-1)/rDen),b={pNum,pDen,rNum,rDen,a,c};
  return valid?b:pick(2)?{...b,a:a+1}:{...b,rNum:rNum-1};
 }
 for(let d=0;d<depth;d++)for(const src of layers[d]){
  let targets=shuffle(layers[d+1],rand).slice(0,degree);
  if(src===planted[d]&&!targets.includes(planted[d+1]))targets[targets.length-1]=planted[d+1];
  adj[src]=shuffle(targets.map(dst=>{
   const p=latent[src]?(latent[dst]?.80:.65):(latent[dst]?.08:.12);
   return {src,dst,cert:cert((src===planted[d]&&dst===planted[d+1])||rand()<p)};
  }),rand);
 }
 return tags05({seed,split,depth,width,goal:planted[depth],adj},latent);
}

function root05(seed,split,regime){return regime==="original"?tags05(makeRoot(seed,split)):makeTyped05(seed,split)}

function key05(seed,id,draw){
 let h=(seed^Math.imul(draw+1,0x9E3779B9))>>>0;
 for(let i=0;i<id.length;i++)h=Math.imul(h^id.charCodeAt(i),16777619)>>>0;
 return rng(h)();
}

function feat05(e,c,view){
 const d=dep(e.id),tag=view==="scrambled"?e.scrambled:e.tag,parent=view==="scrambled"?e.parentScrambled:e.parentTag;
 return [tag,parent,Math.min(4,c.inDegree.get(e.id)||0)/4,e.sibling,(c.layerCount[d]||0)/c.width,Math.min(2,(c.calls-e.birth)/64),(c.budget-c.calls-c.outdegree*(c.depth-d))/c.budget];
}

function copy05(s){return {...s,ctx:{...s.ctx,inDegree:new Map(s.ctx.inDegree),layerCount:s.ctx.layerCount.slice()},bank:s.bank.slice(),expanded:new Set(s.expanded),trace:s.trace.slice(),expansions:s.expansions.slice()}}

function depth05(e){return dep(e.id)}

function randomDepth05(root,draw){return e=>2*dep(e.id)+key05(root.seed,e.id,draw)}

function order05(bank,ctx,cap,policy,rankOnly=false,force=null){
 const rank=(xs,p)=>xs.map(e=>({e,score:p(e,ctx)})).sort((a,b)=>b.score-a.score||b.e.order-a.e.order).map(r=>r.e);
 let ordered=rank(bank,rankOnly?depth05:policy),evaluations=ordered.length;
 if(force!==null){const i=ordered.findIndex(e=>e.id===force);ok(i>=0,"forced candidate absent");ordered.unshift(ordered.splice(i,1)[0])}
 ordered=ordered.slice(0,cap);
 if(rankOnly){ok(force===null,"rank-only force");evaluations+=ordered.length;ordered=rank(ordered,policy)}
 return {ordered,evaluations};
}

function episode05(root,budget,cap,policy,{collect=null,snapshot=null,forced=null,rankOnly=false}={}){
 const s=snapshot?copy05(snapshot):{ctx:{depth:root.depth,width:root.width,outdegree:root.outdegree,budget,calls:0,inDegree:new Map(),layerCount:[]},bank:[{id:"start",birth:0,order:0,tag:root.tag.start,scrambled:root.scrambled.start,parentTag:root.tag.start,parentScrambled:root.scrambled.start,sibling:1,path:[]}],seq:1,peak:1,transient:1,scores:0,invalid:0,duplicates:0,evictions:0,success:false,path:[],trace:[],expansions:[],expanded:new Set()};
 const c=s.ctx;
 function schedule(force=null){
  const r=order05(s.bank,c,cap,policy,rankOnly,force);s.scores+=r.evaluations;s.evictions+=s.bank.length-r.ordered.length;s.bank=r.ordered;s.peak=Math.max(s.peak,s.bank.length);
 }
 if(snapshot){ok(c.budget===budget&&forced!==null,"resume");schedule(forced)}
 while(s.bank.length&&c.calls<budget){
  const current=s.bank.shift();ok(!s.expanded.has(current.id),"repeat expand");
  s.expanded.add(current.id);const d=dep(current.id);c.layerCount[d]=(c.layerCount[d]||0)+1;s.expansions.push(current.id);
  let checked=0,valid=0,added=[];
  for(const e of root.adj[current.id]||[]){
   if(c.calls>=budget)break;
   c.calls++;checked++;
   const result=verify(e.cert);s.trace.push({src:e.src,dst:e.dst,result});
   if(result!=="valid"){s.invalid++;continue}
   valid++;c.inDegree.set(e.dst,(c.inDegree.get(e.dst)||0)+1);
   if(e.dst===root.goal){s.success=true;s.path=[...current.path,e];break}
   if(s.expanded.has(e.dst)||s.bank.some(x=>x.id===e.dst)||added.some(x=>x.id===e.dst)){s.duplicates++;continue}
   added.push({id:e.dst,birth:c.calls,order:s.seq++,tag:root.tag[e.dst],scrambled:root.scrambled[e.dst],parentTag:current.tag,parentScrambled:current.scrambled,sibling:0,path:[...current.path,e]});
  }
  if(s.success)break;
  for(const e of added)e.sibling=valid/Math.max(1,checked);
  s.bank.push(...added);s.transient=Math.max(s.transient,s.bank.length);
  if(collect&&s.bank.length&&c.calls<budget)collect(s);
  schedule();
 }
 return {success:s.success,calls:c.calls,peak:s.peak,transient:s.transient,scores:s.scores,invalid:s.invalid,duplicates:s.duplicates,evictions:s.evictions,path:s.path,trace:s.trace,expansions:s.expansions};
}

function eligible05(s){
 const c=s.ctx,nonterminal=s.bank.filter(e=>dep(e.id)<c.depth),d=Math.max(-1,...nonterminal.map(e=>dep(e.id)));
 if(d<0||c.budget-c.calls>4*(c.depth-d+3))return [];
 return nonterminal.filter(e=>dep(e.id)===d);
}

function collect05(regime){
 const data=[],scrambled=[],stat={roots:256,episodes:0,contexts:0,teacherRollouts:0,teacherCalls:0,prefixReplayCalls:0,actions:0,drawDisagreements:0,pairs:0,ties:0,unequal:0,signaturePairs:0,signatureDisagree:0,sameTagPairs:0,sameTagDisagree:0,tagComparable:0,tagCorrect:0,scrambledComparable:0,scrambledCorrect:0,remaining:{}};
 const start=regime==="original"?1140001:1040001;
 function pushPair(rows,a,b,y){const w=y===.5?.25:1;rows.push({a,b,y,w},{a:b,b:a,y:1-y,w})}
 for(let i=0;i<256;i++){
  const root=root05(start+i,i<128?"development":"validation",regime),budget=[24,40,64][i%3];
  for(const cap of [4,16])for(const behavior of ["depth","random"]){
   const rand=rng((root.seed^Math.imul(cap,29)^(behavior==="depth"?0xC3:0xD5))>>>0),sample=[];let seen=0;
   const collect=s=>{if(eligible05(s).length<2)return;seen++;if(sample.length<3)sample.push(copy05(s));else{const j=Math.floor(rand()*seen);if(j<3)sample[j]=copy05(s)}};
   const ep=episode05(root,budget,cap,behavior==="depth"?depth05:randomDepth05(root,19),{collect});replay(root,ep,budget,cap);stat.episodes++;
   for(let j=0;j<sample.length;j++){
    const s=sample[j],c=s.ctx;stat.contexts++;
    const items=eligible05(s).map(e=>{
     const ys=[];
     for(let draw=0;draw<2;draw++){
      const nonce=1000+100*j+draw+10000*(behavior==="random"?1:0)+100000*cap;
      const r=episode05(root,budget,cap,randomDepth05(root,nonce),{snapshot:s,forced:e.id});
      replay(root,r,budget,cap);ok(r.expansions[s.expansions.length]===e.id,"forced action");
      stat.teacherRollouts++;stat.teacherCalls+=r.calls-c.calls;stat.prefixReplayCalls+=c.calls;ys.push(Number(r.success));
     }
     stat.actions++;stat.drawDisagreements+=Number(ys[0]!==ys[1]);
     return {f:feat05(e,c,"true"),g:feat05(e,c,"scrambled"),q:(ys[0]+ys[1])/2};
    });
    for(let a=0;a<items.length;a++)for(let b=a+1;b<items.length;b++){
     const x=items[a],z=items[b],y=(1+x.q-z.q)/2,diff=y!==.5;stat.pairs++;stat.ties+=Number(!diff);stat.unequal+=Number(diff);
     if(x.f.every((v,k)=>v===z.f[k])){stat.signaturePairs++;stat.signatureDisagree+=Number(diff)}
     if(x.f[0]===z.f[0]){stat.sameTagPairs++;stat.sameTagDisagree+=Number(diff)}
     if(diff&&x.f[0]!==z.f[0]){stat.tagComparable++;stat.tagCorrect+=Number(Math.sign(x.f[0]-z.f[0])===Math.sign(x.q-z.q))}
     if(diff&&x.g[0]!==z.g[0]){stat.scrambledComparable++;stat.scrambledCorrect+=Number(Math.sign(x.g[0]-z.g[0])===Math.sign(x.q-z.q))}
     const k=Math.floor((budget-c.calls)/8)*8,rs=stat.remaining[k]??={pairs:0,unequal:0};rs.pairs++;rs.unequal+=Number(diff);
     pushPair(data,x.f,z.f,y);if(regime==="typed")pushPair(scrambled,x.g,z.g,y);
    }
   }
  }
 }
 ok(stat.pairs===stat.ties+stat.unequal&&data.length===2*stat.pairs&&stat.unequal>0,"pair counts");
 return {data,scrambled,stat};
}

function pairGrad05(w,row,kind,g){
 const a=forward(w,row.a,kind).p,b=forward(w,row.b,kind).p,logit=p=>Math.log(p/(1-p));
 const d=row.w*(sigmoid(logit(a)-logit(b))-row.y);
 grad(w,row.a,a-d,kind,g);grad(w,row.b,b+d,kind,g);
}

function gradient05(){
 const row={a:[.1,.2,.3,.4,.5,.6,.7],b:[.2,.4,.1,.6,.3,.5,.2],y:.75,w:.25};let max=0;
 for(const kind of ["linear","recurrent"]){
  const w=init(kind,892),g=w.map(()=>0);pairGrad05(w,row,kind,g);
  const loss=()=>{const a=forward(w,row.a,kind).p,b=forward(w,row.b,kind).p,p=sigmoid(Math.log(a/(1-a))-Math.log(b/(1-b)));return -row.w*(row.y*Math.log(p)+(1-row.y)*Math.log(1-p))};
  for(let i=0;i<w.length;i++){const z=w[i],eps=1e-5;w[i]=z+eps;const a=loss();w[i]=z-eps;const b=loss();w[i]=z;max=Math.max(max,Math.abs(g[i]-(a-b)/(2*eps)))}
 }
 ok(max<1e-6,"pair gradient");return max;
}

function learned05(weights,kind,view){return (e,c)=>2*dep(e.id)+forward(weights,feat05(e,c,view),kind).p}

function train05(data,regime,view,validation){
 const choices={},learning=[];
 for(const kind of ["linear","recurrent"]){
  const w=init(kind,kind==="linear"?502:503),rand=rng(711);let best=null;
  for(let epoch=1;epoch<=8;epoch++){
   for(let batch=0;batch<48;batch++){const g=w.map(()=>0);for(let j=0;j<32;j++)pairGrad05(w,data[Math.floor(rand()*data.length)],kind,g);for(let i=0;i<w.length;i++)w[i]-=.08*g[i]/32}
   if([1,4,8].includes(epoch)){
    const policy=learned05(w,kind,view);let solved=0,calls=0;
    for(const root of validation){const r=episode05(root,64,4,policy);replay(root,r,64,4);solved+=Number(r.success);calls+=r.calls}
    const ck={regime,kind,epoch,solved,calls,weights:w.slice()};learning.push({regime,kind,epoch,solved,calls});
    if(!best||solved>best.solved||(solved===best.solved&&calls<best.calls))best=ck;
   }
  }
  choices[kind]=best;
 }
 return {choices,learning};
}

function evaluate05(regime,learned,scrambledLearned=null){
 const roots=Array.from({length:192},(_,i)=>root05((regime==="typed"?1060001:1160001)+i,"heldout",regime)),rows=[],paired=[],changes={};
 const choices=learned.choices,lin=learned05(choices.linear.weights,"linear","true"),rec=learned05(choices.recurrent.weights,"recurrent","true");
 const policies={depth:()=>depth05,depthRandom:r=>randomDepth05(r,19),tag:()=>e=>2*dep(e.id)+e.tag,linear:()=>lin,recurrent:()=>rec,rankingOnly:()=>rec};
 if(regime==="typed"){
  policies.tagScrambled=()=>e=>2*dep(e.id)+e.scrambled;
  policies.recurrentScrambled=()=>learned05(choices.recurrent.weights,"recurrent","scrambled");
  policies.trainedScrambled=()=>learned05(scrambledLearned.choices.recurrent.weights,"recurrent","scrambled");
 }
 let testEpisodes=0,checkedCalls=0;
 for(const [cap,budget] of [[4,64],[16,64],[4,128]]){
  const all={};for(const [name,make] of Object.entries(policies)){
   const rs=roots.map(root=>{
    const policy=make(root),collect=name==="depth"&&cap===4&&budget===64?s=>{
     const ref=order05(s.bank,s.ctx,cap,depth05).ordered;
     for(const [k,p] of Object.entries(policies)){
      const x=order05(s.bank,s.ctx,cap,p(root),k==="rankingOnly").ordered,st=changes[k]??={states:0,choiceChanges:0,bankSetChanges:0,bankOrderChanges:0};
      st.states++;st.choiceChanges+=Number(x[0].id!==ref[0].id);st.bankSetChanges+=Number(x.map(e=>e.id).sort().join(",")!==ref.map(e=>e.id).sort().join(","));st.bankOrderChanges+=Number(x.map(e=>e.id).join(",")!==ref.map(e=>e.id).join(","));
     }
    }:null;
    const x=episode05(root,budget,cap,policy,{rankOnly:name==="rankingOnly",collect});replay(root,x,budget,cap);testEpisodes++;checkedCalls+=x.calls;return x;
   });
   all[name]=rs;rows.push({regime,cap,budget,policy:name,roots:rs.length,solved:rs.filter(r=>r.success).length,meanCalls:rs.reduce((s,r)=>s+r.calls,0)/rs.length,scoreEvaluations:rs.reduce((s,r)=>s+r.scores,0),peak:Math.max(...rs.map(r=>r.peak)),transient:Math.max(...rs.map(r=>r.transient)),evictions:rs.reduce((s,r)=>s+r.evictions,0)});
  }
  for(const ref of Object.keys(policies).filter(k=>k!=="recurrent"))paired.push({regime,cap,budget,policy:"recurrent",reference:ref,...exactPaired(all.recurrent,all[ref])});
  if(regime==="typed")paired.push({regime,cap,budget,policy:"tag",reference:"tagScrambled",...exactPaired(all.tag,all.tagScrambled)});
 }
 return {rows,paired,changes,testEpisodes,checkedCalls,falseAccepts:0};
}

function experiment05(){
 const start=Date.now(),gradientError=gradient05(),typed=collect05("typed"),original=collect05("original");
 const vt=Array.from({length:96},(_,i)=>root05(1050001+i,"validation","typed")),vo=Array.from({length:96},(_,i)=>root05(1150001+i,"validation","original"));
 const t=train05(typed.data,"typed","true",vt),s=train05(typed.scrambled,"scrambled","scrambled",vt),o=train05(original.data,"original","true",vo);
 // Held-out roots are constructed only after all model selections are frozen.
 const a=evaluate05("typed",t,s),b=evaluate05("original",o);
 return {status:"PASS",scope:"synthetic typed-observability and exact replay; no factoring or full BPD/TRM result",gradientError,teacher:{typed:typed.stat,original:original.stat},training:{epochs:8,batchesPerEpoch:48,batchSize:32,lr:.08,parameters:{linear:8,recurrent:137},choices:{typed:t.choices,scrambled:s.choices,original:o.choices},validation:[...t.learning,...s.learning,...o.learning]},evaluation:{typed:a,original:b},elapsedMs:Date.now()-start};
}

console.log(JSON.stringify(experiment05(),null,2));
