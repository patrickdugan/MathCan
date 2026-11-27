// CRD-13A: exact BigInt grouped sensor likelihoods and certified prefix pruning.
import {rng,shuffle} from "./search.mjs";
const ok=(x,m)=>{if(!x)throw Error(m)};
const sum=a=>a.reduce((s,v)=>s+v,0n),sumN=a=>a.reduce((s,v)=>s+v,0);
const top=(w,k)=>sum(w.slice().sort((a,b)=>a>b?-1:a<b?1:0).slice(0,k));
const bit=(mask,i)=>(mask>>i)&1;
function gcd(a,b){while(b){[a,b]=[b,a%b]}return a}
function canon(s){
 let {mask,a,d}=s;ok(Number.isSafeInteger(mask)&&mask>=0&&mask<8&&Number.isSafeInteger(a)&&Number.isSafeInteger(d)&&d>0&&a*2>=d&&a<=d,"sensor");
 if(mask===0||mask===7||a*2===d)return null;
 mask=Math.min(mask,7^mask);const g=gcd(a,d);return {mask,a:a/g,d:d/g};
}
function binom(n,h){
 let c=1n;for(let j=1;j<=h;j++)c=c*BigInt(n-j+1)/BigInt(j);return c;
}
function compile(sensors){
 const map=new Map();let discarded=0;
 for(const s of sensors){const x=canon(s);if(!x){discarded++;continue}
  const key=[x.mask,x.a,x.d].join(":");if(!map.has(key))map.set(key,{...x,n:0});map.get(key).n++;
 }
 const groups=[...map.values()].sort((a,b)=>b.n-a.n||b.a*a.d-a.a*b.d||a.mask-b.mask||a.d-b.d||a.a-b.a);
 let cardinality=1n;for(const g of groups){
  const a=BigInt(g.a),q=BigInt(g.d-g.a),n=BigInt(g.n);g.den=BigInt(g.d)**n;g.low=q**n;g.high=a**n;
  g.terms=Array.from({length:g.n+1},(_,h)=>{
   const c=binom(g.n,h),t=BigInt(h),f0=c*q**t*a**(n-t),f1=c*a**t*q**(n-t);
   return [f0,f1];
  });
  for(const i of [0,1])ok(sum(g.terms.map(t=>t[i]))===g.den,"binomial normalization");
  cardinality*=BigInt(g.terms.length);
 }
 const G=groups.length,den=Array(G+1).fill(1n),lo=Array.from({length:G+1},()=>Array(9).fill(1n)),hi=Array.from({length:G+1},()=>Array(9).fill(1n));
 for(let t=G-1;t>=0;t--){
  const g=groups[t];den[t]=den[t+1]*g.den;
  for(let i=0;i<3;i++)for(let j=0;j<3;j++){
   const z=3*i+j,distinct=bit(g.mask,i)!==bit(g.mask,j);
   lo[t][z]=lo[t+1][z]*(distinct?g.low:1n);
   hi[t][z]=hi[t+1][z]*(distinct?g.high:1n);
  }
 }
 return {groups,den,lo,hi,cardinality,discarded,retained:sensors.length-discarded};
}
function massNext(w,g,term){return w.map((x,i)=>x*term[bit(g.mask,i)])}
function rankStable(C,t,w,k){
 const order=[0,1,2].sort((i,j)=>w[i]>w[j]?-1:w[i]<w[j]?1:i-j);
 for(const i of order.slice(0,k))for(const j of order.slice(k)){
  const z=3*i+j;if(w[i]*C.lo[t][z]<w[j]*C.hi[t][z])return false;
 }return true;
}
function envelope(C,t,w,k){
 const L=top(w,k)*C.den[t],U=sum(w)*C.den[t];
 if(t===C.groups.length)return {L,U:L,reason:"leaf"};
 if(L===U)return {L,U:L,reason:"trivial"};
 if(rankStable(C,t,w,k))return {L,U:L,reason:"rank"};
 return {L,U,reason:"open"};
}
function stats(){return {visited:0,expanded:0,leaves:0,rankCertificates:0,trivialCertificates:0}}
function exactGrouped(C,w,k,prune){
 const s=stats();
 function rec(t,w){
  s.visited++;
  if(t===C.groups.length){s.leaves++;return top(w,k)}
  if(prune){
   const e=envelope(C,t,w,k);
   if(e.reason!=="open"){s[e.reason==="rank"?"rankCertificates":"trivialCertificates"]++;return e.L}
  }
  s.expanded++;const g=C.groups[t];let v=0n;
  for(const term of g.terms)v+=rec(t+1,massNext(w,g,term));
  return v;
 }
 const numerator=rec(0,w);return {numerator,...s};
}
// Independent raw enumeration: no group canonicalization, no binomial weights,
// no pruning; advance each bit separately using original integer likelihoods.
function rawBits(sensors,prior,k){
 let visited=0,leaves=0;
 function rec(t,w){
  visited++;if(t===sensors.length){leaves++;return top(w,k)}
  const {mask,a,d}=sensors[t];let v=0n;
  for(let u=0;u<2;u++)v+=rec(t+1,w.map((p,j)=>p*BigInt(bit(mask,j)===u?a:d-a)));
  return v;
 }
 const numerator=rec(0,prior.slice(0,3)),denominator=sum(prior)*sensors.reduce((p,s)=>p*BigInt(s.d),1n);
 return {numerator,denominator,visited,leaves};
}
class Heap{
 constructor(){this.a=[]}
 higher(x,y){return x.gap>y.gap||(x.gap===y.gap&&x.serial<y.serial)}
 push(x){const a=this.a;a.push(x);let i=a.length-1;
  while(i>0){const p=(i-1)>>1;if(!this.higher(a[i],a[p]))break;[a[i],a[p]]=[a[p],a[i]];i=p}
 }
 pop(){const a=this.a;if(!a.length)return null;const top=a[0],last=a.pop();if(a.length){a[0]=last;let i=0;
  for(;;){let p=i,l=2*i+1,r=l+1;if(l<a.length&&this.higher(a[l],a[p]))p=l;if(r<a.length&&this.higher(a[r],a[p]))p=r;if(p===i)break;[a[p],a[i]]=[a[i],a[p]];i=p}
 }return top}
}
function bounded(C,w,k,denominator,truth){
 const h=new Heap(),s=stats();let lower=0n,upper=0n,serial=0,peak=0,peakWeightBits=0;
 const countBits=x=>x===0n?0:x.toString(2).length;
 function add(t,w){
  s.visited++;const e=envelope(C,t,w,k);lower+=e.L;upper+=e.U;
  peakWeightBits=Math.max(peakWeightBits,...w.map(countBits));
  if(e.reason==="open"){h.push({t,w,...e,gap:e.U-e.L,serial:serial++});peak=Math.max(peak,h.a.length)}
  else if(e.reason==="leaf")s.leaves++;
  else s[e.reason==="rank"?"rankCertificates":"trivialCertificates"]++;
 }
 add(0,w);
 function check(){
  ok(0n<=lower&&lower<=upper&&upper<=sum(w)*C.den[0],"interval range");
  if(truth!==null)ok(lower<=truth&&truth<=upper,"interval containment");
  if(!h.a.length)ok(lower===upper,"empty frontier");
 }
 check();const out=[];
 for(const budget of [0,32,128,512]){
  while(s.expanded<budget&&h.a.length){
   const n=h.pop(),lastL=lower,lastU=upper;
   lower-=n.L;upper-=n.U;s.expanded++;
   const g=C.groups[n.t];for(const term of g.terms)add(n.t+1,massNext(n.w,g,term));
   ok(lower>=lastL&&upper<=lastU,"interval nestedness");check();
  }
  out.push({budget,...s,heap:h.a.length,peakHeap:peak,peakWeightBits,lower:lower.toString(),upper:upper.toString(),denominator:denominator.toString(),low:Number(lower)/Number(denominator),high:Number(upper)/Number(denominator),width:Number(upper-lower)/Number(denominator),exact:lower===upper});
 }
 return out;
}
function fixture13(regime,seed,m=null){
 const r=rng(seed),prior=Array.from({length:6},()=>1+Math.floor(r()*12));const sensors=[];
 if(regime==="small"){
  m=4+Math.floor(r()*9);
  const choices=[[1,2],[3,5],[4,5],[9,10],[1,1]];
  for(let t=0;t<m;t++){const mask=Math.floor(r()*8),[a,d]=choices[Math.floor(r()*choices.length)];sensors.push({mask,a,d})}
 }else if(regime==="repeated"){
  const mask=[1,2,3][Math.floor(r()*3)];
  for(let t=0;t<m;t++){const u=r(),flip=r()<.5;
   if(u<.125)sensors.push({mask:flip?0:7,a:4,d:5});
   else if(u<.25)sensors.push({mask:flip?mask:7^mask,a:1,d:2});
   else sensors.push({mask:flip?mask:7^mask,a:4,d:5});
  }
 }else if(regime==="mixed"){
  for(let t=0;t<m;t++){const j=t%6,mask=1+(j%3);sensors.push({mask:r()<.5?mask:7^mask,a:j<3?3:4,d:5})}
  const ordered=shuffle(sensors,r);sensors.splice(0,sensors.length,...ordered);
 }else{
  for(let t=0;t<m;t++){const d=t+3,mask=1+t%3;sensors.push({mask:r()<.5?mask:7^mask,a:d-1,d})}
 }
 return {regime,seed,m,prior:prior.map(BigInt),sensors,k:1+(seed%2)};
}
function evaluate13(root,doRaw,doExact,doBound){
 const {regime,seed,m,prior,sensors,k}=root,C=compile(sensors),w=prior.slice(0,3),denominator=sum(prior)*C.den[0];
 let exact=null,pruned=null,raw=null,truth=null,monotonic=false;
 if(doExact){
  exact=exactGrouped(C,w,k,false);pruned=exactGrouped(C,w,k,true);truth=exact.numerator;
  ok(exact.leaves===Number(C.cardinality),"group outcome count");ok(truth===pruned.numerator,"exact pruning");
  const alternate=exactGrouped(C,w,3-k,true).numerator;
  ok(k===1?truth<=alternate:alternate<=truth,"k monotonic");
  ok(truth>=top(w,k)*C.den[0]&&truth<=sum(w)*C.den[0],"exact bounds");monotonic=true;
 }
 if(doRaw){
  raw=rawBits(sensors,prior,k);
  ok(truth!==null&&raw.numerator*denominator===truth*raw.denominator,"raw/group rational equality");
 }
 const conv=obj=>obj?Object.fromEntries(Object.entries(obj).map(([k,v])=>[k,typeof v==="bigint"?v.toString():v])):null;
 const intervals=doBound?bounded(C,w,k,denominator,truth):[];
 return {regime,seed,m,k,prior:prior.map(Number),retained:C.retained,discarded:C.discarded,groups:C.groups.map(({mask,a,d,n})=>({mask,a,d,n})),rawCardinality:(2n**BigInt(m)).toString(),groupCardinality:C.cardinality.toString(),denominator:denominator.toString(),exactValue:truth===null?null:Number(truth)/Number(denominator),exact:conv(exact),pruned:conv(pruned),raw:conv(raw),monotonic,intervals};
}
function aggregate13(rows){
 const buckets=new Map();
 for(const r of rows){const key=r.regime+":"+(r.regime==="small"?"all":r.m);if(!buckets.has(key))buckets.set(key,[]);buckets.get(key).push(r)}
 const mean=a=>sumN(a)/a.length,median=a=>a.slice().sort((x,y)=>x-y)[Math.floor(a.length/2)];
 return [...buckets].map(([key,rs])=>{
  const ex=rs.filter(r=>r.exact),agg={key,roots:rs.length,exactRoots:ex.length,meanDiscarded:mean(rs.map(r=>r.discarded)),maxGroups:Math.max(...rs.map(r=>r.groups.length)),maxGroupCardinality:rs.reduce((m,r)=>BigInt(r.groupCardinality)>m?BigInt(r.groupCardinality):m,0n).toString(),log10RawOverGroupedMedian:median(rs.map(r=>r.m*Math.log10(2)-Math.log10(Number(r.groupCardinality))))};
  if(ex.length){
   agg.exact={unprunedVisited:sumN(ex.map(r=>r.exact.visited)),prunedVisited:sumN(ex.map(r=>r.pruned.visited)),unprunedLeaves:sumN(ex.map(r=>r.exact.leaves)),prunedLeaves:sumN(ex.map(r=>r.pruned.leaves)),rankCertificates:sumN(ex.map(r=>r.pruned.rankCertificates)),trivialCertificates:sumN(ex.map(r=>r.pruned.trivialCertificates))};
  }
  if(rs[0].intervals.length)agg.bounded=[0,32,128,512].map((budget,i)=>{
   const a=rs.map(r=>r.intervals[i]);return {budget,exactRoots:a.filter(r=>r.exact).length,meanWidth:mean(a.map(r=>r.width)),maxWidth:Math.max(...a.map(r=>r.width)),meanGenerated:mean(a.map(r=>r.visited)),maxHeap:Math.max(...a.map(r=>r.peakHeap)),meanExpanded:mean(a.map(r=>r.expanded)),maxWeightBits:Math.max(...a.map(r=>r.peakWeightBits))};
  });
  return agg;
 });
}
function experiment13(){
 const start=Date.now(),rows=[];
 for(let i=0;i<64;i++)rows.push(evaluate13(fixture13("small",1940001+i),true,true,false));
 for(const [j,m] of [32,64,128].entries())for(let i=0;i<12;i++)rows.push(evaluate13(fixture13("repeated",1950001+12*j+i,m),false,true,true));
 for(const [j,m] of [24,36].entries())for(let i=0;i<8;i++)rows.push(evaluate13(fixture13("mixed",1960001+8*j+i,m),false,true,true));
 for(const [j,m] of [16,32,64].entries())for(let i=0;i<8;i++)rows.push(evaluate13(fixture13("unique",1970001+8*j+i,m),j===0&&i<2,j===0,true));
 return {status:"PASS",scope:"exact rational independent mandatory-sensor utility, not a real proof-search result",roots:rows.length,rawChecks:rows.filter(r=>r.raw).length,exactChecks:rows.filter(r=>r.exact).length,boundedRoots:rows.filter(r=>r.intervals.length).length,monotonicChecks:rows.filter(r=>r.monotonic).length,summary:aggregate13(rows),rows,elapsedMs:Date.now()-start};
}
console.log(JSON.stringify(experiment13(),null,2));
