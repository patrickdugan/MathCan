// CRD-06: compositional observation filter. Node >=18.
import {verify,upperRoot} from "./audit.mjs";
import {rng,shuffle} from "./search.mjs";
import {ok,sigmoid,exactPaired} from "./learned_frontier.mjs";
function seq06(seed,min,max){
 const rand=rng(seed),L=min+Math.floor(rand()*(max-min+1)),obs=[],hidden=[];let z=1;
 for(let t=0;t<L;t++){const x=rand()<.5?-1:1,r=rand()<.5?.90:.98,y=rand()<(1+r)/2?x:-x;hidden.push(x);obs.push([y,r>.94?1:-1]);z*=x}
 return {seed,L,obs,hidden,y:Number(z===1)};
}

function reliability(x){return .94+.04*x[1]}

function exact06(){
 let patterns=0,latentPairs=0,singleChecks=0;
 for(let L=2;L<=8;L++){
  const size=1<<L;
  for(let t=0;t<L;t++)for(const sign of [-1,1]){
   let plus=0,minus=0;
   for(let x=0;x<size;x++){let z=1,xt=0;for(let j=0;j<L;j++){const v=(x>>j)&1?1:-1;z*=v;if(j===t)xt=v}if(xt===sign){if(z===1)plus++;else minus++}}
   ok(plus===minus&&plus===size/4,"single-symbol independence");singleChecks++;
  }
  let denom=100n**BigInt(L);
  for(let y=0;y<size;y++){
   let target=1n,plus=0n,total=0n;
   for(let j=0;j<L;j++)target*=BigInt(((y>>j)&1?1:-1)*(j%2?98:90));
   for(let x=0;x<size;x++){
    let w=1n,z=1;for(let j=0;j<L;j++){let xt=(x>>j)&1?1:-1,yt=(y>>j)&1?1:-1;z*=xt;const q=j%2?99:95;w*=BigInt(xt===yt?q:100-q)}
    total+=w;if(z===1)plus+=w;latentPairs++;
   }
   ok(total===denom&&2n*plus-denom===target,"Bayes product enumeration");patterns++;
  }
 }
 return {patterns,latentPairs,singleChecks,reliabilityPattern:"alternating .90/.98; all observed/latent sign vectors"};
}

function init06(kind){
 if(kind==="mult")return [0,.8,0,.1];
 const n={rnn:33,window:31,full:85}[kind],rand=rng({rnn:502,window:503,full:504}[kind]);
 return Array.from({length:n},()=>.4*rand()-.2);
}

function stepR06(w,h,x){
 const out=[];
 for(let i=0;i<4;i++){let z=w[24+i]+w[2*i]*x[0]+w[2*i+1]*x[1];for(let j=0;j<4;j++)z+=w[8+4*i+j]*h[j];out.push(Math.tanh(z))}
 return out;
}

function multFactor06(w,x){return Math.tanh(w[0]+w[1]*x[0]+w[2]*x[1]+w[3]*x[0]*x[1])}

function mlp06(w,h,kind){
 const n=kind==="window"?8:40,k=kind==="window"?3:2,hidden=[];
 for(let i=0;i<k;i++){let z=w[n*k+i];for(let j=0;j<n;j++)z+=w[i*n+j]*h[j];hidden.push(Math.tanh(z))}
 let z=w[n*k+2*k];for(let i=0;i<k;i++)z+=w[n*k+k+i]*hidden[i];
 return {p:sigmoid(z),hidden};
}

function start06(kind){
 if(kind==="rnn")return Array(4).fill(0);
 if(kind==="window")return Array(8).fill(0);
 if(kind==="full")return Array(40).fill(0);
 if(kind==="count")return [0,0];
 if(kind==="random")return [];
 return [kind==="bayes"||kind==="parity"||kind==="mult"?1:0];
}

function step06(kind,w,h,x){
 if(kind==="rnn")return stepR06(w,h,x);
 if(kind==="window"||kind==="full")return h.slice(2).concat(x);
 if(kind==="mult")return [h[0]*multFactor06(w,x)];
 if(kind==="bayes")return [h[0]*x[0]*reliability(x)];
 if(kind==="parity")return [h[0]*x[0]];
 if(kind==="last")return [x[0]];
 if(kind==="count")return [h[0]+x[0],h[1]+1];
 return h;
}

function read06(kind,w,h,key=.5){
 if(kind==="rnn"){let z=w[32];for(let i=0;i<4;i++)z+=w[28+i]*h[i];return sigmoid(z)}
 if(kind==="window"||kind==="full")return mlp06(w,h,kind).p;
 if(kind==="random")return key;
 if(kind==="count")return (1+h[0]/Math.max(1,h[1]))/2;
 return (1+h[0])/2;
}

function pred06(kind,w,obs,key=.5){let h=start06(kind);for(const x of obs)h=step06(kind,w,h,x);return read06(kind,w,h,key)}

function bce06(p,y){const q=Math.min(1-1e-12,Math.max(1e-12,p));return -(y*Math.log(q)+(1-y)*Math.log(1-q))}

function grad06(kind,w,row,g){
 const {obs,y}=row;
 if(kind==="rnn"){
  const hs=[start06(kind)];for(const x of obs)hs.push(stepR06(w,hs[hs.length-1],x));
  const last=hs[hs.length-1],d=read06(kind,w,last)-y;g[32]+=d;let dh=[];
  for(let i=0;i<4;i++){g[28+i]+=d*last[i];dh.push(d*w[28+i])}
  for(let t=obs.length-1;t>=0;t--){const h=hs[t+1],prev=hs[t],x=obs[t],dp=[0,0,0,0];
   for(let i=0;i<4;i++){const a=dh[i]*(1-h[i]**2);g[24+i]+=a;g[2*i]+=a*x[0];g[2*i+1]+=a*x[1];for(let j=0;j<4;j++){g[8+4*i+j]+=a*prev[j];dp[j]+=a*w[8+4*i+j]}}
   dh=dp;
  }return;
 }
 if(kind==="mult"){
  const fs=obs.map(x=>multFactor06(w,x)),prefix=[1],suffix=Array(fs.length+1).fill(1);
  for(const f of fs)prefix.push(prefix[prefix.length-1]*f);
  for(let t=fs.length-1;t>=0;t--)suffix[t]=suffix[t+1]*fs[t];
  const p=Math.min(1-1e-12,Math.max(1e-12,(1+prefix[fs.length])/2)),d=(p-y)/(2*p*(1-p));
  for(let t=0;t<fs.length;t++){const x=obs[t],a=d*prefix[t]*suffix[t+1]*(1-fs[t]**2);g[0]+=a;g[1]+=a*x[0];g[2]+=a*x[1];g[3]+=a*x[0]*x[1]}return;
 }
 let h=start06(kind);for(const x of obs)h=step06(kind,w,h,x);
 const {p,hidden}=mlp06(w,h,kind),d=p-y,n=h.length,k=hidden.length;
 g[n*k+2*k]+=d;
 for(let i=0;i<k;i++){g[n*k+k+i]+=d*hidden[i];const a=d*w[n*k+k+i]*(1-hidden[i]**2);g[n*k+i]+=a;for(let j=0;j<n;j++)g[i*n+j]+=a*h[j]}
}

function gradient06(){
 let max=0;const errors={},row={obs:[[1,1],[-1,-1],[1,-1]],y:0};
 for(const kind of ["rnn","window","full","mult"]){
  const w=init06(kind),g=w.map(()=>0);grad06(kind,w,row,g);let err=0;
  for(let i=0;i<w.length;i++){const old=w[i],eps=1e-5;w[i]=old+eps;const a=bce06(pred06(kind,w,row.obs),row.y);w[i]=old-eps;const b=bce06(pred06(kind,w,row.obs),row.y);w[i]=old;err=Math.max(err,Math.abs(g[i]-(a-b)/(2*eps)))}
  errors[kind]=err;max=Math.max(max,err);
 }
 ok(max<1e-6,"gradient");return errors;
}

function metrics06(rows,kind,w){
 let loss=0,correct=0,brier=0,posteriorMSE=0;
 for(const row of rows){const p=pred06(kind,w,row.obs,rng((row.seed^0xA1B2C3D4)>>>0)()),q=pred06("bayes",null,row.obs);ok(Number.isFinite(p)&&p>=0&&p<=1,"probability");loss+=bce06(p,row.y);correct+=Number(Number(p>=.5)===row.y);brier+=(p-row.y)**2;posteriorMSE+=(p-q)**2}
 return {n:rows.length,correct,accuracy:correct/rows.length,bce:loss/rows.length,brier:brier/rows.length,posteriorMSE:posteriorMSE/rows.length};
}

function train06(train,val){
 const choices={},history=[];
 for(const kind of ["rnn","window","full","mult"]){
  const w=init06(kind),rand=rng(711);let best=null;
  for(let ep=1;ep<=16;ep++){
   for(let b=0;b<64;b++){const g=w.map(()=>0);for(let j=0;j<32;j++)grad06(kind,w,train[Math.floor(rand()*train.length)],g);for(let i=0;i<w.length;i++)w[i]-=.08*g[i]/32}
   if([1,4,8,16].includes(ep)){const m=metrics06(val,kind,w);history.push({kind,epoch:ep,...m});if(!best||m.bce<best.bce)best={epoch:ep,...m,weights:w.slice()}}
  }choices[kind]=best;
 }
 return {choices,history};
}

function cert06(branch,t){
 const pDen=23,pNum=1+((branch+3*t)%22),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=10400,a=Math.floor((c*(rDen-rNum)-1)/rDen);
 return {pNum,pDen,rNum,rDen,a,c};
}

function root06(seed,used){
 const L=13+Math.floor(rng((seed^0xC6EF3720)>>>0)()*8),branches=[];
 // The arithmetic progression is injective over all registered root/branch pairs.
 for(let i=0;i<16;i++){const key=(Math.imul(seed,32)+i+0x1F123BB5)>>>0;ok(!used.has(key),"duplicate branch seed");used.add(key);const row=seq06(key,L,L);branches.push({...row,index:i,certs:Array.from({length:L},(_,t)=>cert06(i,t))})}
 const rand=rng((seed^0x165667B1)>>>0),scrambled=branches.map(b=>b.obs.slice());
 for(let t=0;t<L;t++){const values=shuffle(branches.map(b=>b.obs[t]),rand);for(let i=0;i<16;i++)scrambled[i][t]=values[i];const key=xs=>xs.map(x=>x.join(":")).sort().join(",");ok(key(values)===key(branches.map(b=>b.obs[t])),"scramble histogram")}
 return {seed,L,branches,scrambled};
}

function exactCert06(c){return BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum)}

function terminal06(b){const y=Number(b.hidden.reduce((a,x)=>a*x,1)===1);ok(y===b.y,"latent witness");return y}

function stream06(root,kind,w,view){
 // Each policy sees only the current symbol after certification. Completed scores are
 // replayed through both registered retention capacities; their prefix trace is identical.
 const banks={4:[],16:[]},peak={4:0,16:0},slots=start06(kind).length;
 let prefixCalls=0,updates=0,reads=0;
 for(const b of root.branches){
  let h=start06(kind);
  for(const cap of [4,16])peak[cap]=Math.max(peak[cap],(banks[cap].length+1)*slots);
  for(let t=0;t<root.L;t++){
   const c=b.certs[t];prefixCalls++;ok(verify(c)==="valid"&&exactCert06(c),"arithmetic replay");
   const x=view==="true"?b.obs[t]:root.scrambled[b.index][t];h=step06(kind,w,h,x);updates++;
  }
  const score=read06(kind,w,h,rng((root.seed^Math.imul(b.index+1,0x9E3779B9))>>>0)());reads++;ok(Number.isFinite(score),"score");
  for(const cap of [4,16]){
   banks[cap].push({index:b.index,score,h:h.slice()});banks[cap].sort((a,b)=>b.score-a.score||b.index-a.index);banks[cap].length=Math.min(banks[cap].length,cap);ok(banks[cap].length<=cap,"retention");
  }
 }
 ok(prefixCalls===16*root.L&&reads===16,"prefix budget");
 const out={};
 for(const [cap,probes] of [[4,1],[4,4],[16,4]]){
  let calls=0,success=false,terminalIndices=[];
  for(const e of banks[cap].slice(0,probes)){calls++;terminalIndices.push(e.index);if(terminal06(root.branches[e.index])){success=true;break}}
  ok(calls<=probes&&new Set(terminalIndices).size===terminalIndices.length,"terminal budget");
  if(success)ok(root.branches[terminalIndices[terminalIndices.length-1]].hidden.reduce((a,b)=>a*b,1)===1,"false accept");
  out[cap+":"+probes]={success,terminalCalls:calls,calls:prefixCalls+calls,prefixCalls,updates,reads,peakSlots:peak[cap],terminalIndices};
 }
 ok(JSON.stringify(out["4:4"].terminalIndices)===JSON.stringify(out["16:4"].terminalIndices),"top-k equivalence");
 return out;
}

function experiment06(){
 const start=Date.now(),identities=exact06(),gradient=gradient06();
 const train=Array.from({length:8192},(_,i)=>seq06(1240001+i,2,8)),validation=Array.from({length:1024},(_,i)=>seq06(1250001+i,9,12)),trained=train06(train,validation);
 const test=Array.from({length:2048},(_,i)=>seq06(1260001+i,13,20));
 const kinds=["bayes","parity","last","count","random","rnn","window","full","mult"],weights=k=>trained.choices[k]?.weights??null;
 const sequence=kinds.map(kind=>({kind,...metrics06(test,kind,weights(kind))}));
 const lengths={};for(let L=13;L<=20;L++){const subset=test.filter(x=>x.L===L);lengths[L]=kinds.map(kind=>({kind,...metrics06(subset,kind,weights(kind))}))}
 const used=new Set(),roots=Array.from({length:192},(_,i)=>root06(1270001+i,used)),all={},rows=[],paired=[];
 let executedPrefixCalls=0,terminalCalls=0,eligibleRoots=0;
 for(const root of roots)eligibleRoots+=Number(root.branches.some(b=>terminal06(b)));
 for(const view of ["true","scrambled"])for(const kind of kinds){
  const rs=roots.map(root=>stream06(root,kind,weights(kind),view));executedPrefixCalls+=rs.reduce((s,r)=>s+r["4:1"].prefixCalls,0);
  for(const [cap,probes] of [[4,1],[4,4],[16,4]]){
   const key=cap+":"+probes,vals=rs.map(r=>r[key]);all[view+":"+kind+":"+key]=vals;
   const sum=k=>vals.reduce((s,v)=>s+v[k],0);terminalCalls+=sum("terminalCalls");
   rows.push({view,kind,cap,probes,n:vals.length,solved:vals.filter(v=>v.success).length,meanCalls:sum("calls")/vals.length,meanTerminalCalls:sum("terminalCalls")/vals.length,prefixCalls:sum("prefixCalls"),stateUpdates:sum("updates"),scoreReads:sum("reads"),peakSlots:Math.max(...vals.map(v=>v.peakSlots))});
  }
 }
 for(const [cap,probes] of [[4,1],[4,4],[16,4]])for(const kind of kinds){
  const key=cap+":"+probes,a=all["true:"+kind+":"+key];
  for(const ref of ["bayes","parity","random","window"])if(kind!==ref)paired.push({cap,probes,kind,ref,...exactPaired(a,all["true:"+ref+":"+key])});
  paired.push({cap,probes,kind,ref:"same model scrambled",...exactPaired(a,all["scrambled:"+kind+":"+key])});
 }
 const cost={bayes:{multiplications:2},parity:{multiplications:1},last:{assignments:1},count:{additions:2},random:{},rnn:{affineProducts:24,tanh:4,readProducts:4},window:{historyShiftSlots:8,readProducts:27,tanhRead:3},full:{historyShiftSlots:40,readProducts:82,tanhRead:2},mult:{affineProducts:4,extraProducts:1,tanh:1}};
 return {status:"PASS",scope:"synthetic compositional filter and independent arithmetic checks; no factorization result",identities,gradient,train:8192,validation:1024,test:2048,trained,sequence,lengths,search:{roots:192,eligibleRoots,uniqueBranchSeeds:used.size,executedPrefixCalls,terminalCalls,logicalEpisodes:rows.length*192,rows,paired,falseAccepts:0},cost,elapsedMs:Date.now()-start};
}

console.log(JSON.stringify(experiment06(),null,2));
