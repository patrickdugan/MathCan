import {pathToFileURL} from "node:url";
// CRD-07: noncommutative compositional memory. Node >=18.
import {verify,upperRoot} from "./audit.mjs";
import {rng,shuffle} from "./search.mjs";
import {ok,exactPaired} from "./learned_frontier.mjs";

const K0=[.98,.006,.004,.004,.003,.003], K1=[.88,.025,.015,.045,.025,.01];
const zeros=n=>Array(n).fill(0);
const unit=g=>Array.from({length:6},(_,i)=>Number(i===g));
const sum=a=>a.reduce((s,x)=>s+x,0);
const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
const mod3=k=>(k%3+3)%3;
function mul(a,b){const k=a%3,s=Math.floor(a/3),l=b%3,t=Math.floor(b/3);return 3*(s^t)+mod3(k+(s?-l:l))}
const G=Array.from({length:6},(_,a)=>Array.from({length:6},(_,b)=>mul(a,b)));
const sign=g=>g<3?1:-1;
const R=Array.from({length:6},(_,g)=>{
 const a=2*Math.PI*(g%3)/3,c=Math.cos(a),s=Math.sin(a),z=sign(g);
 return [c,-s*z,s,c*z];
});
function mm(a,b){return [a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]]}
function ft(p){return [dot(p,[1,1,1,-1,-1,-1]),...Array.from({length:4},(_,j)=>sum(p.map((v,g)=>v*R[g][j])))]}
function ift(h){return Array.from({length:6},(_,g)=>(1+sign(g)*h[0]+2*dot(R[g],h.slice(1)))/6)}
function blockmul(a,b){return [a[0]*b[0],...mm(a.slice(1),b.slice(1))]}
function softmax(z){const max=Math.max(...z),v=z.map(x=>Math.exp(x-max)),s=sum(v);return v.map(x=>x/s)}
function mix(k,c){return k[0].map((x,i)=>(1-c)*x+c*k[1][i])}
function stepDist(p,y,k){const q=zeros(6);for(let a=0;a<6;a++)for(let e=0;e<6;e++)q[G[G[a][y]][e]]+=p[a]*k[e];return q}
function kernelFT(y,k){return blockmul(ft(unit(y)),ft(k))}
function near(a,b,tol=1e-10){return a.length===b.length&&a.every((v,i)=>Math.abs(v-b[i])<=tol)}
function validProb(p){ok(p.length===6&&p.every(v=>Number.isFinite(v)&&v>=-1e-10&&v<=1+1e-10)&&Math.abs(sum(p)-1)<1e-9,"invalid posterior")}
function hard(obs){let h=0;for(const [y] of obs)h=G[h][y];return h}
function exactAudit07(){
 let assoc=0,products=0,inverses=0,basis=0,patterns=0,latentPaths=0,noncommuting=0,subsetChecks=0;
 for(let a=0;a<6;a++){
  const inv=G[a].findIndex(b=>b===0);ok(inv>=0&&G[inv][a]===0&&G[a][0]===a&&G[0][a]===a,"identity/inverse");inverses++;
  ok(near(ift(ft(unit(a))),unit(a)),"basis inversion");basis++;
  for(let b=0;b<6;b++){
   ok(near(mm(R[a],R[b]),R[G[a][b]])&&sign(a)*sign(b)===sign(G[a][b]),"representation");products++;
   ok(near(blockmul(ft(unit(a)),ft(unit(b))),ft(unit(G[a][b]))),"basis convolution");
   noncommuting+=Number(G[a][b]!==G[b][a]);
   for(let c=0;c<6;c++){ok(G[G[a][b]][c]===G[a][G[b][c]],"associativity");assoc++}
  }
 }
 // For every insertion position and fixed surrounding factors, one missing uniform
 // group element is a bijection onto all terminal products.
 for(let a=0;a<6;a++)for(let b=0;b<6;b++){ok(new Set(G[a].map(v=>G[v][b])).size===6,"uniform missing increment");subsetChecks++}
 const digits=(n,L)=>Array.from({length:L},(_,j)=>Math.floor(n/6**j)%6);
 const a0=[1960,12,8,8,6,6],a1=[1760,50,30,90,50,20];
 for(let L=1;L<=3;L++){
  const n=6**L,den=2000n**BigInt(L);
  const weights=Array.from({length:L},(_,t)=>a0.map((v,i)=>t%3===0?v:t%3===1?(v+a1[i])/2:a1[i]));
  for(let j=0;j<n;j++){
   const ys=digits(j,L),truth=Array(6).fill(0n);
   for(let k=0;k<n;k++){
    const es=digits(k,L);let h=0,w=1n;
    for(let t=0;t<L;t++){h=G[G[h][ys[t]]][es[t]];w*=BigInt(weights[t][es[t]])}
    truth[h]+=w;latentPaths++;
   }
   ok(truth.reduce((s,v)=>s+v,0n)===den,"exact mass");
   let p=unit(0),f=ft(p);
   for(let t=0;t<L;t++){const k=weights[t].map(v=>v/2000);p=stepDist(p,ys[t],k);f=blockmul(f,kernelFT(ys[t],k))}
   const q=truth.map(v=>Number(v)/Number(den));
   ok(near(p,q)&&near(ift(f),q),"exact posterior");patterns++;
  }
 }
 return {assoc,products,inverses,basis,patterns,latentPaths,noncommuting,subsetChecks};
}
function sampleCat(k,u){let s=0;for(let i=0;i<k.length-1;i++){s+=k[i];if(u<s)return i}return k.length-1}
function seq07(seed,min,max,regime){
 const rand=rng(seed),L=min+Math.floor(rand()*(max-min+1)),obs=[],hidden=[];let label=0;
 for(let t=0;t<L;t++){
  const y=Math.floor(rand()*6),c=(regime==="shift"?.75:0)+(rand()<.5?0:regime==="shift"?.25:.5);
  const e=sampleCat(mix([K0,K1],c),rand()),x=G[y][e];
  obs.push([y,c]);hidden.push(x);label=G[label][x];
 }
 return {seed,L,obs,hidden,label};
}
function enc(x){return [...unit(x[0]),x[1]]}
function init07(kind){
 if(kind==="learned")return [3.5,0,0,0,0,0,3.5,0,0,0,0,0];
 const n={rnn:101,window:111,full:244}[kind],r=rng({rnn:502,window:503,full:504}[kind]);
 return Array.from({length:n},()=>.4*r()-.2);
}
function kernels(w){return [softmax(w.slice(0,6)),softmax(w.slice(6,12))]}
function recurrent07(w,h,x){
 const out=[];
 for(let i=0;i<5;i++){let z=w[60+i]+dot(w.slice(7*i,7*i+7),x)+dot(w.slice(35+5*i,35+5*i+5),h);out.push(Math.tanh(z))}
 return out;
}
function readR07(w,h){return softmax(Array.from({length:6},(_,g)=>w[95+g]+dot(w.slice(65+5*g,65+5*g+5),h)))}
function mlp07(w,h,kind){
 const n=kind==="window"?14:112,k=kind==="window"?5:2,j=n*k,hidden=[];
 for(let i=0;i<k;i++)hidden.push(Math.tanh(w[j+i]+dot(w.slice(n*i,n*i+n),h)));
 const p=softmax(Array.from({length:6},(_,g)=>w[j+7*k+g]+dot(w.slice(j+k+g*k,j+k+g*k+k),hidden)));
 return {p,hidden};
}
function start07(kind){
 if(kind==="direct")return unit(0);
 if(kind==="fourier"||kind==="learned")return ft(unit(0));
 if(kind==="rnn")return zeros(5);
 if(kind==="window")return zeros(14);
 if(kind==="full")return zeros(112);
 if(kind==="uniform")return [];
 return [0];
}
function prep07(kind,w){
 if(kind==="direct"||kind==="fourier"||kind==="learned"){
  const k=kind==="learned"?kernels(w):[K0,K1];
  const lookup=new Map();for(const c of [0,.5,.75,1])for(let y=0;y<6;y++){const q=mix(k,c);lookup.set(y+":"+c,kind==="direct"?q:kernelFT(y,q))}
  return lookup;
 }return null;
}
function step07(kind,w,h,x,table){
 if(kind==="direct")return stepDist(h,x[0],table.get(x.join(":")));
 if(kind==="fourier"||kind==="learned")return blockmul(h,table.get(x.join(":")));
 if(kind==="hard")return [G[h[0]][x[0]]];
 if(kind==="last")return [x[0]];
 if(kind==="uniform")return h;
 if(kind==="rnn")return recurrent07(w,h,enc(x));
 return h.slice(7).concat(enc(x));
}
function read07(kind,w,h){
 if(kind==="direct")return h;
 if(kind==="fourier"||kind==="learned")return ift(h);
 if(kind==="hard"||kind==="last")return unit(h[0]);
 if(kind==="uniform")return Array(6).fill(1/6);
 if(kind==="rnn")return readR07(w,h);
 return mlp07(w,h,kind).p;
}
function predict07(kind,w,obs,table=prep07(kind,w)){
 let h=start07(kind);for(const x of obs)h=step07(kind,w,h,x,table);
 const p=read07(kind,w,h);validProb(p);return p;
}
function grad07(kind,w,row,g){
 const {obs,label}=row;
 if(kind==="learned"){
  const k=kernels(w),states=[unit(0)],ks=obs.map(x=>mix(k,x[1]));
  for(let t=0;t<obs.length;t++)states.push(stepDist(states[t],obs[t][0],ks[t]));
  let dp=zeros(6);dp[label]=-1/states[obs.length][label];
  for(let t=obs.length-1;t>=0;t--){
   const [y,c]=obs[t],prior=states[t],dk=zeros(6),prev=zeros(6);
   for(let a=0;a<6;a++)for(let e=0;e<6;e++){const d=dp[G[G[a][y]][e]];prev[a]+=d*ks[t][e];dk[e]+=d*prior[a]}
   for(let j=0;j<2;j++){const m=dot(dk,k[j]),weight=j?c:1-c;for(let e=0;e<6;e++)g[6*j+e]+=weight*k[j][e]*(dk[e]-m)}
   dp=prev;
  }return;
 }
 if(kind==="rnn"){
  const xs=obs.map(enc),hs=[zeros(5)];
  for(const x of xs)hs.push(recurrent07(w,hs[hs.length-1],x));
  const h=hs[hs.length-1],d=readR07(w,h);d[label]-=1;let dh=zeros(5);
  for(let j=0;j<6;j++){g[95+j]+=d[j];for(let i=0;i<5;i++){g[65+5*j+i]+=d[j]*h[i];dh[i]+=d[j]*w[65+5*j+i]}}
  for(let t=obs.length-1;t>=0;t--){const h=hs[t+1],prev=hs[t],x=xs[t],dp=zeros(5);
   for(let i=0;i<5;i++){const a=dh[i]*(1-h[i]*h[i]);g[60+i]+=a;
    for(let j=0;j<7;j++)g[7*i+j]+=a*x[j];
    for(let j=0;j<5;j++){g[35+5*i+j]+=a*prev[j];dp[j]+=a*w[35+5*i+j]}
   }dh=dp;
  }return;
 }
 let h=start07(kind);for(const x of obs)h=h.slice(7).concat(enc(x));
 const {p,hidden}=mlp07(w,h,kind),n=h.length,k=hidden.length,j=n*k,dh=zeros(k);p[label]-=1;
 for(let a=0;a<6;a++){g[j+7*k+a]+=p[a];for(let i=0;i<k;i++){g[j+k+a*k+i]+=p[a]*hidden[i];dh[i]+=p[a]*w[j+k+a*k+i]}}
 for(let i=0;i<k;i++){const a=dh[i]*(1-hidden[i]**2);g[j+i]+=a;for(let b=0;b<n;b++)g[n*i+b]+=a*h[b]}
}
const ce07=(p,y)=>-Math.log(Math.max(1e-12,p[y]));
function gradient07(){
 const row={obs:[[1,0],[3,.5],[5,.5]],label:4},out={};
 for(const kind of ["learned","rnn","window","full"]){
  const w=init07(kind),g=zeros(w.length);grad07(kind,w,row,g);let err=0;
  for(let i=0;i<w.length;i++){
   const old=w[i],eps=1e-5;w[i]=old+eps;const a=ce07(predict07(kind,w,row.obs),row.label);w[i]=old-eps;const b=ce07(predict07(kind,w,row.obs),row.label);w[i]=old;
   err=Math.max(err,Math.abs(g[i]-(a-b)/(2*eps)));
  }ok(err<1e-6,"gradient "+kind);out[kind]=err;
 }
 return out;
}
const argmax=p=>p.indexOf(Math.max(...p));
function metrics07(rows,kind,w,view="true"){
 const table=prep07(kind,w),reference=prep07("fourier",null);
 let ce=0,correct=0,brier=0,posteriorMSE=0,orderChanges=0,l1=0;
 for(const row of rows){
  const obs=view==="true"?row.obs:shuffle(row.obs,rng((row.seed^0x16E667B1)>>>0)),p=predict07(kind,w,obs,table),q=predict07("fourier",null,row.obs,reference);
  ce+=ce07(p,row.label);correct+=Number(argmax(p)===row.label);brier+=sum(p.map((v,i)=>(v-Number(i===row.label))**2));posteriorMSE+=sum(p.map((v,i)=>(v-q[i])**2));
  if(view==="scrambled"){orderChanges+=Number(hard(obs)!==hard(row.obs));const perm=predict07("fourier",null,obs,reference);l1+=sum(perm.map((v,i)=>Math.abs(v-q[i])))}
 }
 return {n:rows.length,correct,accuracy:correct/rows.length,ce:ce/rows.length,brier:brier/rows.length,posteriorMSE:posteriorMSE/rows.length,orderChanges,meanPosteriorL1Shift:l1/rows.length};
}
function train07(train,val){
 const choices={},history=[];
 for(const kind of ["learned","rnn","window","full"]){
  const w=init07(kind),rand=rng(711);let best=null;
  for(let ep=1;ep<=12;ep++){
   for(let b=0;b<64;b++){const g=zeros(w.length);for(let j=0;j<32;j++)grad07(kind,w,train[Math.floor(rand()*train.length)],g);for(let i=0;i<w.length;i++)w[i]-=.08*g[i]/32}
   if([1,4,8,12].includes(ep)){const m=metrics07(val,kind,w);history.push({kind,epoch:ep,...m});if(!best||m.ce<best.ce)best={epoch:ep,...m,weights:w.slice()}}
  }choices[kind]=best;
 }return {choices,history};
}
function compareFilters07(rows,w){
 const k=kernels(w),exactTable=prep07("fourier",null),learnedTable=prep07("learned",w);let maxExact=0,maxLearned=0,checks=0;
 for(const row of rows)for(const obs of [row.obs,shuffle(row.obs,rng((row.seed^0x16E667B1)>>>0))]){
  const direct=predict07("direct",null,obs),fourier=predict07("fourier",null,obs,exactTable);
  let learnedDirect=unit(0);for(const [y,c] of obs)learnedDirect=stepDist(learnedDirect,y,mix(k,c));
  const learnedBlock=predict07("learned",w,obs,learnedTable);
  maxExact=Math.max(maxExact,...direct.map((v,i)=>Math.abs(v-fourier[i])));
  maxLearned=Math.max(maxLearned,...learnedDirect.map((v,i)=>Math.abs(v-learnedBlock[i])));
  ok(near(direct,fourier)&&near(learnedDirect,learnedBlock),"Fourier equivalence");checks++;
 }return {checks,maxExact,maxLearned};
}
function cert07(branch,t){
 const pDen=23,pNum=1+((branch+3*t)%22),rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=10400,a=Math.floor((c*(rDen-rNum)-1)/rDen);
 return {pNum,pDen,rNum,rDen,a,c};
}
function exactCert07(c){return BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum)}
function root07(seed,regime,used){
 const rand=rng((seed^0xC6EF3720)>>>0),L=11+Math.floor(rand()*6),target=Math.floor(rand()*6),branches=[];
 for(let i=0;i<16;i++){
  const key=(Math.imul(seed,32)+i+0x273AB591)>>>0;ok(!used.has(key),"duplicate branch seed");used.add(key);
  const row=seq07(key,L,L,regime),scrambled=shuffle(row.obs,rng((key^0x16E667B1)>>>0));
  const multiset=a=>a.map(x=>x.join(":")).sort().join(",");
  ok(multiset(scrambled)===multiset(row.obs),"scramble multiset");
  branches.push({...row,index:i,scrambled,certs:Array.from({length:L},(_,t)=>cert07(i,t))});
 }return {seed,L,target,branches};
}
function terminal07(b,target){let v=0;for(const x of b.hidden)v=G[v][x];ok(v===b.label,"terminal witness");return v===target}
function stream07(root,kind,w,view,table){
 const bank=[],slots=start07(kind).length;let peak=0,prefix=0,updates=0,reads=0;
 for(const b of root.branches){
  let h=start07(kind);peak=Math.max(peak,(bank.length+1)*slots);
  const obs=view==="true"?b.obs:b.scrambled;
  for(let t=0;t<root.L;t++){
   const c=b.certs[t];prefix++;ok(verify(c)==="valid"&&exactCert07(c),"arithmetic replay");
   h=step07(kind,w,h,obs[t],table);updates++;
  }
  const p=read07(kind,w,h);validProb(p);reads++;
  // Exact direct/Fourier may differ at rounding precision; quantize only their
  // (and other nonuniform) scheduler scores to 1e-12 for a shared tie convention.
  const score=kind==="uniform"?rng((root.seed^Math.imul(b.index+1,0x9E3779B9))>>>0)():Math.round(p[root.target]*1e12)/1e12;
  bank.push({index:b.index,score,h:h.slice()});bank.sort((a,b)=>b.score-a.score||b.index-a.index);bank.length=Math.min(bank.length,4);ok(bank.length<=4,"retention");
 }
 ok(prefix===16*root.L&&reads===16,"prefix budget");
 const results={};
 for(const k of [1,4]){
  let calls=0,success=false,probed=[];
  for(const e of bank.slice(0,k)){calls++;probed.push(e.index);if(terminal07(root.branches[e.index],root.target)){success=true;break}}
  ok(calls<=k&&new Set(probed).size===probed.length,"probe budget");
  if(success)ok(terminal07(root.branches[probed[probed.length-1]],root.target),"false accept");
  results[k]={success,calls:prefix+calls,prefix,terminal:calls,updates,reads,peak,probed};
 }return results;
}
function evalSearch07(regime,kinds,weights){
 const used=new Set(),roots=Array.from({length:192},(_,i)=>root07(1370001+i,regime,used)),all={},rows=[],paired=[];
 let prefixExecuted=0,terminal=0,eligible=0;
 for(const r of roots)eligible+=Number(r.branches.some(b=>terminal07(b,r.target)));
 for(const view of ["true","scrambled"])for(const kind of kinds){
  const w=weights(kind),table=prep07(kind,w),rs=roots.map(root=>stream07(root,kind,w,view,table));prefixExecuted+=sum(rs.map(r=>r[1].prefix));
  for(const k of [1,4]){
   const a=rs.map(r=>r[k]);all[view+":"+kind+":"+k]=a;const s=key=>sum(a.map(v=>v[key]));
   terminal+=s("terminal");rows.push({regime,view,kind,cap:4,probes:k,n:a.length,solved:a.filter(x=>x.success).length,meanCalls:s("calls")/a.length,meanTerminal:s("terminal")/a.length,prefixCalls:s("prefix"),updates:s("updates"),reads:s("reads"),peakSlots:Math.max(...a.map(x=>x.peak))});
  }
 }
 for(const view of ["true","scrambled"])for(const k of [1,4]){
  const a=all[view+":direct:"+k],b=all[view+":fourier:"+k];
  ok(a.every((v,i)=>JSON.stringify(v.probed)===JSON.stringify(b[i].probed)),"exact scheduler disagreement");
 }
 for(const k of [1,4])for(const kind of kinds){
  const a=all["true:"+kind+":"+k];
  for(const ref of ["fourier","hard","rnn","uniform"])if(kind!==ref)paired.push({regime,probes:k,kind,ref,...exactPaired(a,all["true:"+ref+":"+k])});
  paired.push({regime,probes:k,kind,ref:"same model order-scrambled",...exactPaired(a,all["scrambled:"+kind+":"+k])});
 }
 return {roots:roots.length,eligible,uniqueBranchSeeds:used.size,prefixExecuted,terminal,logicalEpisodes:rows.length*roots.length,rows,paired,falseAccepts:0};
}
function experiment07(){
 const begin=Date.now(),audit=exactAudit07(),gradients=gradient07();
 const train=Array.from({length:8192},(_,i)=>seq07(1340001+i,2,7,"in")),val=Array.from({length:1024},(_,i)=>seq07(1350001+i,8,10,"in")),trained=train07(train,val);
 const kinds=["direct","fourier","hard","last","uniform","learned","rnn","window","full"],weights=k=>trained.choices[k]?.weights??null,sequence={},byLength={},equivalence={},search={};
 const learnedK=kernels(weights("learned")),channel={true:[K0,K1],learned:learnedK,l1:[K0,K1].map((p,j)=>sum(p.map((v,i)=>Math.abs(v-learnedK[j][i]))))};
 for(const regime of ["in","shift"]){
  const test=Array.from({length:2048},(_,i)=>seq07(1360001+i,11,16,regime));
  sequence[regime]=["true","scrambled"].flatMap(view=>kinds.map(kind=>({view,kind,...metrics07(test,kind,weights(kind),view)})));
  byLength[regime]=Object.fromEntries(Array.from({length:6},(_,i)=>i+11).map(L=>[L,kinds.map(kind=>({kind,...metrics07(test.filter(r=>r.L===L),kind,weights(kind))}))]));
  equivalence[regime]=compareFilters07(test,weights("learned"));
  search[regime]=evalSearch07(regime,kinds,weights);
 }
 const cost={direct:{transitionProducts:36,adds:36},fourier:{transitionProducts:9,adds:4},learned:{transitionProducts:9,adds:4},hard:{groupTableLookups:1},last:{assignments:1},uniform:{},rnn:{transitionProducts:60,tanh:5,readProducts:30},window:{shiftSlots:14,readProducts:100,tanhRead:5},full:{shiftSlots:112,readProducts:236,tanhRead:2}};
 return {status:"PASS",scope:"synthetic S3 latent process and exact arithmetic certificates; no factoring theorem",audit,gradients,training:{train:8192,validation:1024,testPerRegime:2048,epochs:12,batchesPerEpoch:64,batchSize:32,lr:.08,...trained},channel,sequence,byLength,equivalence,search,cost,elapsedMs:Date.now()-begin};
}
export {K0,K1,sum,ft,mix,kernels,prep07,predict07,root07,terminal07,experiment07};
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(experiment07(),null,2));
