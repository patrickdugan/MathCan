// CRD-08 registered operator identification and adaptive tree search. Node >=18.
import {verify,upperRoot} from "./audit.mjs";
import {rng,shuffle} from "./search.mjs";
import {ok,exactPaired} from "./learned_frontier.mjs";
const N=6, LABEL=[2,5,1,4,0,3], INV=Array.from({length:6},(_,i)=>LABEL.indexOf(i));
const zeros=n=>Array(n).fill(0), sum=a=>a.reduce((s,v)=>s+v,0), dot=(a,b)=>sum(a.map((v,i)=>v*b[i]));
const unit=i=>zeros(N).map((_,j)=>Number(i===j)), I=Array.from({length:N},(_,i)=>unit(i)), J=I.map(r=>r.map(()=>1/N));
const add=(a,b)=>a.map((r,i)=>r.map((v,j)=>v+b[i][j]));
const scale=(a,c)=>a.map(r=>r.map(v=>v*c));
const sub=(a,b)=>add(a,scale(b,-1));
const mat=(a,b)=>a.map(r=>Array.from({length:N},(_,j)=>sum(r.map((v,i)=>v*b[i][j]))));
const rowmul=(r,b)=>Array.from({length:N},(_,j)=>sum(r.map((v,i)=>v*b[i][j])));
const tr=a=>sum(a.map((r,i)=>r[i])), fnorm=a=>Math.sqrt(sum(a.flat().map(v=>v*v)));
const maxabs=a=>Math.max(...a.flat().map(Math.abs));
function power(a,n){let p=I;for(let i=0;i<n;i++)p=mat(p,a);return p}
function gmul(a,b){const k=a%3,s=a>=3?1:0,l=b%3,t=b>=3?1:0;return ((s^t)*3)+(k+(s?-l:l)+3)%3}
const TRUE=[1,3].map(g=>I.map((_,i)=>unit(LABEL[gmul(INV[i],g)])));
const exactOp=(token,c)=>add(scale(TRUE[token],1-c),scale(J,c));
const identity=()=>unit(LABEL[0]);
function groupAudit(){
 // Independent permutation implementation on Z3: x -> k+(-1)^s*x.
 const p=g=>[0,1,2].map(x=>(g%3+(g>=3?-x:x)+3)%3);
 let pairs=0;
 for(let a=0;a<6;a++)for(let b=0;b<6;b++){
  const x=p(a),y=p(b),z=p(gmul(a,b));ok(z.every((v,i)=>v===x[y[i]]),"independent group action");pairs++;
 }return pairs;
}
function inverse(A){
 const a=A.map((r,i)=>[...r,...I[i]]);let minPivot=Infinity;
 for(let j=0;j<N;j++){
  let k=j;for(let i=j+1;i<N;i++)if(Math.abs(a[i][j])>Math.abs(a[k][j]))k=i;
  [a[j],a[k]]=[a[k],a[j]];const p=a[j][j];ok(Math.abs(p)>1e-10,"singular prefix experiment");minPivot=Math.min(minPivot,Math.abs(p));
  a[j]=a[j].map(v=>v/p);for(let i=0;i<N;i++)if(i!==j){const q=a[i][j];a[i]=a[i].map((v,t)=>v-q*a[j][t])}
 }return {inv:a.map(r=>r.slice(N)),minPivot};
}
function simplex(v){
 const u=v.slice().sort((a,b)=>b-a);let s=0,rho=0,theta=0;
 for(let i=0;i<u.length;i++){s+=u[i];const t=(s-1)/(i+1);if(u[i]>t){rho=i+1;theta=t}}
 ok(rho>0,"simplex");return v.map(x=>Math.max(0,x-theta));
}
function permutations(){
 const out=[];function rec(a,left){if(!left.length){out.push(a);return}for(const v of left)rec(a.concat(v),left.filter(x=>x!==v))}
 rec([],Array.from({length:N},(_,i)=>i));return out;
}
const PERMS=permutations();
function bestPerm(a){
 let best=null,score=-Infinity;for(const p of PERMS){const s=sum(p.map((j,i)=>a[i][j]));if(s>score){score=s;best=p}}
 return {perm:best,matrix:best.map(unit),score};
}
function resetFit(base,observed){
 const d=sub(J,base),e=sub(observed,base);
 const denominator=sum(d.flat().map(v=>v*v));ok(denominator>0,"unidentifiable reset");
 return Math.max(0,Math.min(1,dot(d.flat(),e.flat())/denominator));
}
function simulate(word,seed){
 const random=rng(seed);let h=0;const latent=[];
 for(const [a,c] of word){const reset=random()<c,replacement=Math.floor(random()*6);h=reset?replacement:gmul(h,a===0?1:3);latent.push({reset,replacement})}
 return {word,label:LABEL[h],latent,seed};
}
function seq(seed,min,max,regime){
 const random=rng((seed^0xB5297A4D)>>>0),L=min+Math.floor(random()*(max-min+1)),levels=regime==="shift"?[.25,.35]:[0,.15],word=[];
 for(let t=0;t<L;t++)word.push([Math.floor(random()*2),levels[Math.floor(random()*2)]]);
 return simulate(word,(seed^0x68E31DA4)>>>0);
}
function trainData(){
 const anchors=[[],[0],[0,0],[1],[0,1],[0,0,1]],rows=[],P=[],after=Array.from({length:2},()=>[[],[]]);let seed=1440001;
 function sample(word){
  const count=zeros(N);for(let i=0;i<384;i++){const row=simulate(word,seed++);rows.push({word:row.word,label:row.label});count[row.label]++}
  return count.map(v=>v/384);
 }
 for(const anchor of anchors){
  const prefix=anchor.map(a=>[a,.10]);P.push(sample(prefix));
  for(let a=0;a<2;a++)for(let j=0;j<2;j++)after[a][j].push(sample(prefix.concat([[a,j*.15]])));
 }ok(rows.length===11520,"training size");return {rows,P,after};
}
function identify(data){
 const {P,after}=data,{inv,minPivot}=inverse(P),raw=after.map(pair=>pair.map(y=>mat(inv,y)));
 const residual=maxabs(sub(mat(P,inv),I));ok(residual<1e-9,"inverse error");
 const fit=raw.map(pair=>bestPerm(pair[0])),reset=fit.map((x,a)=>after[a].map(y=>resetFit(mat(P,x.matrix),y)));
 const gauge=after.map(pair=>pair.map(y=>mat(y,inv)));
 let traceError=0;for(let a=0;a<2;a++)for(let j=0;j<2;j++){
  const B=gauge[a][j],A=raw[a][j];ok(maxabs(sub(B,mat(mat(P,A),inv)))<1e-9,"gauge equality");
  for(let k=1;k<=6;k++)traceError=Math.max(traceError,Math.abs(tr(power(A,k))-tr(power(B,k))));
 }
 ok(traceError<1e-8,"trace invariance");
 return {P,raw,perms:fit.map(x=>x.matrix),permIndices:fit.map(x=>x.perm),permScores:fit.map(x=>x.score),reset,traceError,minPivot,inverseResidual:residual};
}
function op(kind,fit,a,c){
 if(kind==="exact")return exactOp(a,c);
 if(kind==="hard")return fit.perms[a];
 if(kind==="structured"){
  const [a0,a1]=fit.reset[a],z=Math.max(0,Math.min(1,a0+(a1-a0)*c/.15));
  return add(scale(fit.perms[a],1-z),scale(J,z));
 }
 const [a0,a1]=fit.raw[a],A=add(a0,scale(sub(a1,a0),c/.15));
 return kind==="raw"?A:A.map(simplex);
}
function rank(A,tol=1e-8){
 const a=A.map(r=>r.slice());let i=0;
 for(let j=0;j<N&&i<N;j++){let k=i;for(let l=i+1;l<N;l++)if(Math.abs(a[l][j])>Math.abs(a[k][j]))k=l;if(Math.abs(a[k][j])<=tol)continue;[a[i],a[k]]=[a[k],a[i]];
  const p=a[i][j];for(let l=i+1;l<N;l++){const q=a[l][j]/p;for(let h=j;h<N;h++)a[l][h]-=q*a[i][h]}i++;
 }return i;
}
function relations(A,B){
 const r2=mat(A,A),r3=mat(r2,A),s2=mat(B,B),srs=mat(mat(B,A),B);
 const named=[I,A,r2,B,mat(A,B),mat(r2,B)];
 const triv=scale(named.reduce(add),1/6),sgn=scale(named.reduce((p,x,i)=>add(p,scale(x,i<3?1:-1)),scale(I,0)),1/6),std=sub(sub(I,triv),sgn);
 const proj=[triv,sgn,std];
 return {relator:{r3:fnorm(sub(r3,I)),s2:fnorm(sub(s2,I)),srs:fnorm(sub(srs,r2))},characters:named.map(tr),projectors:proj.map(Q=>({trace:tr(Q),rank:rank(Q),idempotentDefect:fnorm(sub(mat(Q,Q),Q)),commuteR:fnorm(sub(mat(Q,A),mat(A,Q))),commuteS:fnorm(sub(mat(Q,B),mat(B,Q)))})),orthogonalDefect:Math.max(...proj.flatMap((Q,i)=>proj.filter((_,j)=>j!==i).map(R=>fnorm(mat(Q,R)))))};
}
function structureAudit(fit){
 const exact=relations(...TRUE),raw=relations(...fit.raw.map(x=>x[0])),stochastic=relations(...fit.raw.map(x=>x[0].map(simplex))),structured=relations(...fit.perms);
 const initial=fit.P[0],words=[[],[0],[0,0],[1],[0,1],[0,0,1]];
 const orbit=words.map(w=>{let p=initial;for(const a of w)p=rowmul(p,fit.perms[a]);return p.indexOf(Math.max(...p))});
 return {exact,raw,stochastic,structured,orbit,distinctOrbit:new Set(orbit).size,permutationMatches:fit.perms.map((P,a)=>maxabs(sub(P,TRUE[a]))<1e-12)};
}
function softmax(z){const mx=Math.max(...z),v=z.map(x=>Math.exp(x-mx)),s=sum(v);return v.map(x=>x/s)}
function initR(){const random=rng(502);return Array.from({length:150},()=>.4*random()-.2)}
function encode([a,c]){return [Number(a===0),Number(a===1),c]}
function stepR(w,h,x){return Array.from({length:8},(_,i)=>Math.tanh(w[88+i]+dot(w.slice(i*3,i*3+3),x)+dot(w.slice(24+8*i,24+8*i+8),h)))}
function readR(w,h){return softmax(Array.from({length:6},(_,j)=>w[144+j]+dot(w.slice(96+j*8,104+j*8),h)))}
function gradR(w,row,g){
 const xs=row.word.map(encode),hs=[zeros(8)];for(const x of xs)hs.push(stepR(w,hs[hs.length-1],x));
 const h=hs[hs.length-1],d=readR(w,h);d[row.label]-=1;let dh=zeros(8);
 for(let j=0;j<6;j++){g[144+j]+=d[j];for(let i=0;i<8;i++){g[96+8*j+i]+=d[j]*h[i];dh[i]+=d[j]*w[96+8*j+i]}}
 for(let t=xs.length-1;t>=0;t--){
  const h=hs[t+1],prev=hs[t],x=xs[t],dp=zeros(8);
  for(let i=0;i<8;i++){const a=dh[i]*(1-h[i]*h[i]);g[88+i]+=a;for(let j=0;j<3;j++)g[i*3+j]+=a*x[j];for(let j=0;j<8;j++){g[24+8*i+j]+=a*prev[j];dp[j]+=a*w[24+8*i+j]}}dh=dp;
 }
}
function predR(w,word){let h=zeros(8);for(const x of word)h=stepR(w,h,encode(x));return readR(w,h)}
const ce=(p,y)=>-Math.log(Math.max(1e-12,p[y]));
function gradCheck(){
 const w=initR(),row={word:[[0,.1],[1,.15],[0,0]],label:4},g=zeros(w.length);gradR(w,row,g);let err=0;
 for(let i=0;i<w.length;i++){const z=w[i],eps=1e-5;w[i]=z+eps;const a=ce(predR(w,row.word),row.label);w[i]=z-eps;const b=ce(predR(w,row.word),row.label);w[i]=z;err=Math.max(err,Math.abs(g[i]-(a-b)/(2*eps)))}
 ok(err<1e-6,"RNN gradient");return err;
}
function trainR(rows,val){
 const w=initR(),random=rng(711),history=[];let best=null;
 for(let epoch=1;epoch<=16;epoch++){
  for(let batch=0;batch<64;batch++){const g=zeros(w.length);for(let i=0;i<32;i++)gradR(w,rows[Math.floor(random()*rows.length)],g);for(let i=0;i<w.length;i++)w[i]-=.08*g[i]/32}
  if([1,4,8,16].includes(epoch)){const loss=sum(val.map(r=>ce(predR(w,r.word),r.label)))/val.length;
   const correct=val.filter(r=>argmax(predR(w,r.word))===r.label).length;history.push({epoch,ce:loss,correct});
   if(!best||loss<best.ce)best={epoch,ce:loss,correct,weights:w.slice()};
  }
 }return {best,history};
}
const argmax=p=>p.indexOf(Math.max(...p));
function initial(kind,fit){if(kind==="exact")return identity();if(kind==="rnn")return zeros(8);if(kind==="hard")return [argmax(fit.P[0])];if(kind==="uniform"||kind==="depth"||kind==="depthRandom")return [];return fit.P[0].slice()}
function prepare(kind,fit,w,levels){
 const table=new Map();if(["exact","structured","stochastic","raw","hard"].includes(kind))for(const c of [...new Set([...levels,0,.1,.15])])for(let a=0;a<2;a++)table.set(a+":"+c,op(kind,fit,a,c));
 let avg=I;if(table.size){avg=scale([0,1].flatMap(a=>levels.map(c=>table.get(a+":"+c))).reduce(add),1/(2*levels.length))}
 return {kind,fit,w,table,avg};
}
function step(p,h,x){
 if(p.kind==="rnn")return stepR(p.w,h,encode(x));
 if(p.kind==="hard")return [p.fit.permIndices[x[0]][h[0]]];
 if(!p.table.size)return h;
 return rowmul(h,p.table.get(x.join(":")));
}
function read(p,h){
 if(p.kind==="rnn")return readR(p.w,h);
 if(p.kind==="hard")return unit(h[0]);
 if(!p.table.size)return J[0];return h;
}
function predict(p,word){
 let h=initial(p.kind,p.fit);for(const x of word)h=step(p,h,x);return read(p,h);
}
function checkProb(p){ok(p.every(v=>Number.isFinite(v)&&v>=-1e-9&&v<=1+1e-9)&&Math.abs(sum(p)-1)<1e-8,"nonprobability")}
function metrics(rows,p,exact,view){
 let loss=0,correct=0,brier=0,mse=0,negative=0,maxNegative=0,rowSumError=0,orderChanges=0,macroMax=0;
 for(const row of rows){
  const word=view==="true"?row.word:shuffle(row.word,rng((row.seed^0x9216D5D9)>>>0)),q=predict(exact,row.word),v=predict(p,word);
  if(p.kind!=="raw"){checkProb(v);loss+=ce(v,row.label);brier+=sum(v.map((x,i)=>(x-Number(i===row.label))**2))}
  else{negative+=Number(v.some(x=>x<0));maxNegative=Math.min(maxNegative,...v)}
  rowSumError=Math.max(rowSumError,Math.abs(sum(v)-1));correct+=Number(argmax(v)===row.label);mse+=sum(v.map((x,i)=>(x-q[i])**2));orderChanges+=Number(argmax(q)!==argmax(predict(exact,word)));
  if(p.table.size&&p.kind!=="hard"){
   let h=initial(p.kind,p.fit),A=I;
   // Compose never-trained macro words of length 3, then apply them as blocks.
   for(let i=0;i<word.length;i+=3){A=word.slice(i,i+3).reduce((M,x)=>mat(M,p.table.get(x.join(":"))),I);h=rowmul(h,A)}
   macroMax=Math.max(macroMax,...h.map((x,i)=>Math.abs(x-v[i])));ok(macroMax<1e-8,"macro composition");
  }
 }
 return {n:rows.length,correct,accuracy:correct/rows.length,ce:p.kind==="raw"?null:loss/rows.length,brier:p.kind==="raw"?null:brier/rows.length,posteriorMSE:mse/rows.length,negativeRows:negative,minProbability:maxNegative,maxRowSumError:rowSumError,orderChanges,macroMax};
}
function cert(index,depth){
 const pDen=23,pNum=1+((index+3*depth)%22),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=10400,a=Math.floor((c*(rDen-rNum)-1)/rDen);
 return {pNum,pDen,rNum,rDen,a,c};
}
function checkCert(c){return BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum)}
function tree(seed,regime){
 const random=rng(seed),depth=5+Math.floor(random()*3),target=Math.floor(random()*6),levels=regime==="shift"?[.25,.35]:[0,.15],nodes=[null,{id:1,d:0,hidden:0,word:[]}];
 for(let i=2;i<2**(depth+1);i++){
  const parent=nodes[i>>1],a=Math.floor(random()*2),c=levels[Math.floor(random()*2)],reset=random()<c,replacement=Math.floor(random()*6),h=reset?replacement:gmul(parent.hidden,a===0?1:3);
  nodes.push({id:i,d:parent.d+1,x:[a,c],reset,replacement,hidden:h,word:parent.word.concat([[a,c]]),cert:cert(i,parent.d+1)});
 }return {seed,depth,target,nodes,levels};
}
function terminal(root,id){
 // Independently reconstruct the hidden state via composition of explicit permutations.
 const path=[];for(let i=id;i>1;i>>=1)path.push(root.nodes[i]);
 const perm=g=>[0,1,2].map(x=>(g%3+(g>=3?-x:x)+3)%3);
 let h=perm(0);
 for(const n of path.reverse()){
  if(n.reset)h=perm(n.replacement);else{const q=perm(n.x[0]===0?1:3);h=q.map(v=>h[v])}
 }
 const g=Array.from({length:6},(_,i)=>i).find(i=>perm(i).every((x,j)=>x===h[j]));
 ok(g===root.nodes[id].hidden,"independent hidden state");
 return LABEL[g]===root.target;
}
function key(seed,id){return rng((seed^Math.imul(id,0x9E3779B9))>>>0)()}
function priority(p,h,d,id,root,forecasts){
 if(p.kind==="depth")return 2*d;
 if(p.kind==="depthRandom")return 2*d+key(root.seed,id);
 const v=read(p,h);
 const q=p.kind==="rnn"?v:rowmul(v,forecasts[root.depth-d]);
 return 2*d+Math.round(q[root.target]*1e12)/1e12;
}
function forecasts(p,depth){return Array.from({length:depth+1},(_,i)=>power(p.avg,i))}
function runTree(root,p,cap,budget,diagnostic=null){
 const F=forecasts(p,root.depth),slots=initial(p.kind,p.fit).length;
 let bank=[{id:1,d:0,h:initial(p.kind,p.fit)}],calls=0,prefix=0,probes=0,scoreReads=0,updates=0,peak=slots,peakBank=1,transient=1,success=false;
 const trace=[],expanded=new Set();
 while(bank.length&&calls<budget){
  const a=bank.shift();ok(!expanded.has(a.id),"repeat expansion");expanded.add(a.id);
  if(a.d===root.depth){
   calls++;probes++;success=terminal(root,a.id);trace.push({type:"probe",id:a.id,success});
   if(success)break;
  }else{
   for(const id of [a.id*2,a.id*2+1]){
    if(calls>=budget)break;const n=root.nodes[id];
    calls++;prefix++;ok(verify(n.cert)==="valid"&&checkCert(n.cert),"arithmetic");
    const h=step(p,a.h,n.x);updates++;bank.push({id,d:a.d+1,h});trace.push({type:"edge",parent:a.id,id});
   }
  }
  transient=Math.max(transient,bank.length);peak=Math.max(peak,(bank.length+1)*slots);
  if(diagnostic&&bank.length)diagnostic(bank.map(v=>({id:v.id,d:v.d})));
  const ranked=bank.map(e=>({e,s:priority(p,e.h,e.d,e.id,root,F)}));scoreReads+=ranked.length;
  ranked.sort((x,y)=>y.s-x.s||y.e.id-x.e.id);bank=ranked.slice(0,cap).map(v=>v.e);
  peakBank=Math.max(peakBank,bank.length);
 }
 ok(calls===prefix+probes&&calls<=budget&&peakBank<=cap&&transient<=cap+1,"budget accounting");
 // Replay independent arithmetic and reached nodes, charge every event.
 const reached=new Set([1]),seen=new Set(),probed=new Set();let hit=false;
 for(const t of trace){
  ok(!hit,"event after success");
  if(t.type==="edge"){ok(reached.has(t.parent)&&t.id>>1===t.parent&&!seen.has(t.id)&&checkCert(root.nodes[t.id].cert),"edge replay");seen.add(t.id);reached.add(t.id)}
  else{ok(reached.has(t.id)&&root.nodes[t.id].d===root.depth&&!probed.has(t.id),"probe replay");probed.add(t.id);hit=terminal(root,t.id);ok(hit===t.success,"probe outcome")}
 }
 ok(hit===success&&trace.length===calls,"trace end");
 return {success,calls,prefix,probes,scoreReads,updates,peak,peakBank,transient};
}
function searchEval(regime,fit,w){
 const kinds=["depth","depthRandom","exact","structured","stochastic","hard","rnn"],levels=regime==="shift"?[.25,.35]:[0,.15],policies=Object.fromEntries(kinds.map(k=>[k,prepare(k,fit,w,levels)]));
 const roots=Array.from({length:192},(_,i)=>tree(1470001+i,regime)),rows=[],paired=[],changes=Object.fromEntries(kinds.map(k=>[k,{states:0,topChanged:0,retainedChanged:0}]));
 let testEpisodes=0,checkedCalls=0;
 for(const [cap,budget] of [[4,24],[16,48]]){
  const all={};
  for(const k of kinds){
   const results=roots.map(root=>{
    const d=k==="depth"&&cap===4?bank=>{
     const rank=(p,entries)=>{
      const F=forecasts(p,root.depth);
      return entries.map(e=>{
       let h=initial(p.kind,fit);for(const x of root.nodes[e.id].word)h=step(p,h,x);
       return {id:e.id,s:priority(p,h,e.d,e.id,root,F)}
      }).sort((a,b)=>b.s-a.s||b.id-a.id).slice(0,cap).map(x=>x.id);
     };
     const ref=rank(policies.depth,bank);
     for(const name of kinds){const ids=rank(policies[name],bank),s=changes[name];s.states++;s.topChanged+=Number(ids[0]!==ref[0]);s.retainedChanged+=Number(ids.slice().sort().join(",")!==ref.slice().sort().join(","))}
    }:null;
    const r=runTree(root,policies[k],cap,budget,d);testEpisodes++;checkedCalls+=r.calls;return r;
   });
   all[k]=results;const s=key=>sum(results.map(x=>x[key]));
   rows.push({regime,kind:k,cap,budget,roots:results.length,solved:results.filter(x=>x.success).length,meanCalls:s("calls")/192,prefix:s("prefix"),probes:s("probes"),scoreReads:s("scoreReads"),updates:s("updates"),peakNumericSlots:Math.max(...results.map(x=>x.peak)),peakBank:Math.max(...results.map(x=>x.peakBank)),transient:Math.max(...results.map(x=>x.transient))});
  }
  for(const ref of kinds.filter(k=>k!=="structured"))paired.push({regime,cap,budget,kind:"structured",ref,...exactPaired(all.structured,all[ref])});
 }
 return {rows,paired,changes,testEpisodes,checkedCalls,falseAccepts:0};
}
function coupling(){
 let same=0,diverse=0,total=0;for(const a of [0,1])for(const b of [0,1]){
  const w=(a?6:4)*5;total+=w;same+=w*a;diverse+=w*Number(a||b);
 }
 ok(total===100&&same===60&&diverse===80,"coupling enumeration");
 return {worlds:4,marginals:[.6,.6,.5],independentPredictions:{same:.84,diverse:.8},actual:{same:same/total,diverse:diverse/total}};
}
function experiment08(){
 const start=Date.now(),groupPairs=groupAudit(),gradientError=gradCheck(),data=trainData(),fit=identify(data),structure=structureAudit(fit);
 const val=Array.from({length:1024},(_,i)=>seq(1450001+i,5,7,"in")),rnn=trainR(data.rows,val),w=rnn.best.weights;
 const sequence={},search={},kinds=["exact","structured","stochastic","raw","hard","rnn","uniform"];
 for(const regime of ["in","shift"]){
  const levels=regime==="shift"?[.25,.35]:[0,.15],ps=Object.fromEntries(kinds.map(k=>[k,prepare(k,fit,w,levels)]));
  const test=Array.from({length:2048},(_,i)=>seq(1460001+i,8,14,regime));
  sequence[regime]=["true","scrambled"].flatMap(view=>kinds.map(kind=>({view,kind,...metrics(test,ps[kind],ps.exact,view)})));
  search[regime]=searchEval(regime,fit,w);
 }
 const operatorErrors={};
 for(const kind of ["structured","stochastic","raw"])operatorErrors[kind]=[0,.15,.25,.35].map(c=>({c,perToken:[0,1].map(a=>fnorm(sub(op(kind,fit,a,c),exactOp(a,c))))}));
 return {status:"PASS",scope:"synthetic terminal-label identification and adaptive tree; no factoring result",groupPairs,gradientError,training:{rows:data.rows.length,validation:1024,testPerRegime:2048,rnn},fit,structure,operatorErrors,sequence,search,coupling:coupling(),elapsedMs:Date.now()-start};
}
console.log(JSON.stringify(experiment08(),null,2));
