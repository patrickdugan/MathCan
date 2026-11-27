import {pathToFileURL} from "node:url";
// CRD-13C: pairwise likelihood-overlap lower envelope.
import {rng} from "./search.mjs";
import {ok,sum,sumN,bit,compile,massNext,stats,exactGrouped,rawBits,Heap,bounded} from "./grouped_likelihoods.mjs";
import {sqrtCeil,prepareTV,tvEnvelope,solveTV,fixtureB} from "./likelihood_tv_stress.mjs";
function prepareOverlap(C){
 const G=C.groups.length,rad=Array.from({length:G+1},()=>Array(3).fill(1n)),pairs=[[0,1],[0,2],[1,2]];
 for(let t=G-1;t>=0;t--){
  const g=C.groups[t],a=BigInt(g.a),q=BigInt(g.d-g.a),d=BigInt(g.d),n=BigInt(g.n);
  for(let j=0;j<3;j++){
   const [x,y]=pairs[j],factor=bit(g.mask,x)===bit(g.mask,y)?d*d:4n*a*q;
   rad[t][j]=rad[t+1][j]*factor**n;
  }
 }return {rad,pairs};
}
function combinedEnvelope(C,T,O,t,w,k){
 const e=tvEnvelope(C,T,t,w,k);if(e.reason!=="open")return e;
 const errors=O.pairs.map(([i,j],z)=>sqrtCeil(w[i]*w[j]*O.rad[t][z]));
 const error=k===1?sum(errors):errors.reduce((a,b)=>a<b?a:b);
 const candidate=sum(w)*C.den[t]-error,L=candidate>e.L?candidate:e.L;
 ok(L<=e.U,"overlap envelope");
 return {L,U:e.U,reason:L===e.U?"overlap":"open"};
}
function solveOverlap(C,w,k,den,truth){
 const T=prepareTV(C),O=prepareOverlap(C),H=new Heap(),s=stats();let serial=0,lower=0n,upper=0n,peak=0,extraCertificates=0;
 function add(t,w){
  s.visited++;const e=combinedEnvelope(C,T,O,t,w,k);lower+=e.L;upper+=e.U;
  if(e.reason==="open"){H.push({t,w,...e,gap:e.U-e.L,serial:serial++});peak=Math.max(peak,H.a.length)}
  else if(e.reason==="leaf")s.leaves++;
  else if(e.reason==="overlap"||e.reason==="tv")extraCertificates++;
  else s[e.reason==="rank"?"rankCertificates":"trivialCertificates"]++;
 }
 add(0,w);let L=lower,U=upper;
 function check(){
  L=lower>L?lower:L;U=upper<U?upper:U;
  ok(0n<=L&&L<=U&&U<=sum(w)*C.den[0],"combined interval");
  if(truth!==null)ok(L<=truth&&truth<=U,"combined containment");
  if(!H.a.length)ok(L===U,"empty heap");
 }
 check();const out=[];
 for(const budget of [0,32,128,512]){
  while(s.expanded<budget&&H.a.length&&L<U){
   const n=H.pop();lower-=n.L;upper-=n.U;s.expanded++;
   const g=C.groups[n.t];for(const term of g.terms)add(n.t+1,massNext(n.w,g,term));check();
  }
  out.push({budget,...s,extraCertificates,heap:H.a.length,peakHeap:peak,lower:L.toString(),upper:U.toString(),denominator:den.toString(),width:Number(U-L)/Number(den),exact:L===U});
 }return out;
}
function fixtureC(regime,seed,m){
 if(regime!=="high")return fixtureB(regime,seed,m);
 const r=rng(seed),prior=Array.from({length:6},(_,i)=>(i<3?8:1)+Math.floor(r()*(i<3?5:12))).map(BigInt),sensors=[];
 for(let t=0;t<m;t++){const d=t+3,mask=1+t%3;sensors.push({a:d-1,d,mask:r()<.5?mask:7^mask})}
 return {regime,seed,m,prior,sensors,k:1+seed%2};
}
function stressC(){
 const start=Date.now(),rows=[],regimes=["weak","moderate","high"];
 for(const [j,regime] of regimes.entries())for(const [z,m] of [12,32,64].entries())for(let i=0;i<8;i++){
  const root=fixtureC(regime,2000001+j*10000+8*z+i,m),C=compile(root.sensors),w=root.prior.slice(0,3),den=sum(root.prior)*C.den[0];
  let truth=null;
  if(m===12){
   truth=exactGrouped(C,w,root.k,false).numerator;const raw=rawBits(root.sensors,root.prior,root.k);
   ok(truth*raw.denominator===raw.numerator*den,"raw exact reference");
  }
  rows.push({regime,seed:root.seed,m,k:root.k,prior:root.prior.map(Number),exactNumerator:truth===null?null:truth.toString(),denominator:den.toString(),original:bounded(C,w,root.k,den,truth),tv:solveTV(C,w,root.k,den,truth),combined:solveOverlap(C,w,root.k,den,truth)});
 }
 const summary=[],mean=a=>sumN(a)/a.length;
 for(const regime of regimes)for(const m of [12,32,64]){
  const rs=rows.filter(r=>r.regime===regime&&r.m===m);
  summary.push({regime,m,roots:rs.length,exactRoots:rs.filter(r=>r.exactNumerator!==null).length,budgets:[0,32,128,512].map((budget,j)=>({budget,...Object.fromEntries(["original","tv","combined"].map(k=>{const a=rs.map(r=>r[k][j]);return [k,{meanWidth:mean(a.map(r=>r.width)),maxWidth:Math.max(...a.map(r=>r.width)),meanGenerated:mean(a.map(r=>r.visited)),maxHeap:Math.max(...a.map(r=>r.peakHeap)),zeroWidths:a.filter(r=>r.exact).length}]})),combinedNarrower:rs.filter(r=>r.combined[j].width<r.tv[j].width).length,combinedWider:rs.filter(r=>r.combined[j].width>r.tv[j].width).length}))});
 }
 return {status:"PASS",scope:"exact rational overlap+TV envelopes, fresh stress roots",roots:rows.length,rawChecks:rows.filter(r=>r.exactNumerator!==null).length,summary,rows,elapsedMs:Date.now()-start};
}
export {prepareOverlap,combinedEnvelope,solveOverlap,fixtureC,stressC};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(stressC(),null,2));
