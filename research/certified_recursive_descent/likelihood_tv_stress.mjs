import {pathToFileURL} from "node:url";
// CRD-13B: certified total-variation envelopes on fresh weak/moderate fixtures.
import {rng} from "./search.mjs";
import {ok,sum,sumN,top,bit,compile,massNext,envelope,stats,exactGrouped,rawBits,Heap,bounded} from "./grouped_likelihoods.mjs";
function ceilDiv(a,b){ok(a>=0n&&b>0n,"ceilDiv");return (a+b-1n)/b}
function sqrtCeil(n){
 ok(n>=0n,"sqrt");if(n<=1n)return n;
 let x=1n<<BigInt(Math.ceil(n.toString(2).length/2));
 for(;;){const y=(x+n/x)>>1n;if(y>=x)break;x=y}
 const r=x*x===n?x:x+1n;ok((r-1n)*(r-1n)<n&&r*r>=n,"ceil square root");return r;
}
const min=(a,b)=>a<b?a:b;
function tvBound(D,num,den){
 if(den===0n)return D;
 ok(num>=den&&den>0n,"chi square");
 return min(D,ceilDiv(sqrtCeil(ceilDiv(D*D*(num-den),den)),2n));
}
function prepareTV(C){
 const G=C.groups.length,pair=Array.from({length:G+1},()=>Array(9).fill(0n)),unif=Array(G+1).fill(0n);
 let pn=Array(9).fill(1n),pd=Array(9).fill(1n),u=1n;
 for(let t=G-1;t>=0;t--){
  const g=C.groups[t],a=BigInt(g.a),q=BigInt(g.d-g.a),n=BigInt(g.n),D=C.den[t];
  u*=(2n*(a*a+q*q))**n;
  unif[t]=tvBound(D,u,D*D);
  for(let i=0;i<3;i++)for(let j=0;j<3;j++){
   const z=3*i+j;
   if(bit(g.mask,i)!==bit(g.mask,j)){pn[z]*=(a*q+(a-q)**2n)**n;pd[z]*=(a*q)**n}
   pair[t][z]=tvBound(D,pn[z],pd[z]);
  }
 }
 return {pair,unif};
}
function tvEnvelope(C,T,t,w,k){
 const e=envelope(C,t,w,k);if(e.reason!=="open")return e;
 const ids=[0,1,2].sort((i,j)=>w[i]>w[j]?-1:w[i]<w[j]?1:i-j);
 let extra=0n;
 for(const i of ids.slice(0,k))for(const j of ids.slice(k))extra+=w[j]*T.pair[t][3*i+j];
 const U=min(e.U,e.L+min(extra,sum(w)*T.unif[t]));
 return {L:e.L,U,reason:U===e.L?"tv":"open"};
}
function solveTV(C,w,k,den,truth){
 const T=prepareTV(C),H=new Heap(),s=stats();let serial=0,lower=0n,upper=0n,peak=0,tvCert=0;
 function add(t,w){
  s.visited++;const e=tvEnvelope(C,T,t,w,k);lower+=e.L;upper+=e.U;
  if(e.reason==="open"){H.push({t,w,...e,gap:e.U-e.L,serial:serial++});peak=Math.max(peak,H.a.length)}
  else if(e.reason==="leaf")s.leaves++;
  else if(e.reason==="tv")tvCert++;
  else s[e.reason==="rank"?"rankCertificates":"trivialCertificates"]++;
 }
 add(0,w);let L=lower,U=upper;
 function check(){
  L=lower>L?lower:L;U=upper<U?upper:U;
  ok(0n<=L&&L<=U&&U<=sum(w)*C.den[0],"TV interval");
  if(truth!==null)ok(L<=truth&&truth<=U,"TV containment");
  if(!H.a.length)ok(L===U,"empty heap");
 }
 check();const out=[];
 for(const budget of [0,32,128,512]){
  while(s.expanded<budget&&H.a.length&&L<U){
   const n=H.pop();lower-=n.L;upper-=n.U;s.expanded++;
   const g=C.groups[n.t];for(const term of g.terms)add(n.t+1,massNext(n.w,g,term));
   check();
  }
  out.push({budget,...s,tvCertificates:tvCert,heap:H.a.length,peakHeap:peak,lower:L.toString(),upper:U.toString(),denominator:den.toString(),width:Number(U-L)/Number(den),exact:L===U});
 }
 return out;
}
function fixtureB(regime,seed,m){
 const r=rng(seed),prior=Array.from({length:6},(_,i)=>(i<3?8:1)+Math.floor(r()*(i<3?5:12))).map(BigInt),sensors=[];
 for(let t=0;t<m;t++){
  const d=regime==="weak"?21+2*t:10+3*t,a=regime==="weak"?(d+1)/2:(2*d+1)/3,mask=1+t%3;
  ok(Number.isInteger(a),"integral reliability");sensors.push({a,d,mask:r()<.5?mask:7^mask});
 }
 return {regime,seed,m,prior,sensors,k:1+seed%2};
}
function stress13(){
 const start=Date.now(),rows=[];
 for(const regime of ["weak","moderate"])for(const [j,m] of [12,32,64].entries())for(let i=0;i<8;i++){
  const root=fixtureB(regime,(regime==="weak"?1980001:1990001)+8*j+i,m),C=compile(root.sensors),w=root.prior.slice(0,3),den=sum(root.prior)*C.den[0];
  let truth=null;
  if(m===12){
   const ex=exactGrouped(C,w,root.k,false),raw=rawBits(root.sensors,root.prior,root.k);
   truth=ex.numerator;ok(truth*raw.denominator===raw.numerator*den,"raw exact reference");
  }
  const original=bounded(C,w,root.k,den,truth),tv=solveTV(C,w,root.k,den,truth);
  rows.push({regime,seed:root.seed,m,k:root.k,prior:root.prior.map(Number),exactNumerator:truth===null?null:truth.toString(),denominator:den.toString(),original,tv});
 }
 const summary=[];
 for(const regime of ["weak","moderate"])for(const m of [12,32,64]){
  const rs=rows.filter(r=>r.regime===regime&&r.m===m),mean=a=>sumN(a)/a.length;
  summary.push({regime,m,roots:rs.length,exactRoots:rs.filter(r=>r.exactNumerator!==null).length,budgets:[0,32,128,512].map((budget,j)=>({budget,...Object.fromEntries(["original","tv"].map(k=>{const a=rs.map(r=>r[k][j]);return [k,{meanWidth:mean(a.map(r=>r.width)),maxWidth:Math.max(...a.map(r=>r.width)),exactRoots:a.filter(r=>r.exact).length,meanGenerated:mean(a.map(r=>r.visited)),maxHeap:Math.max(...a.map(r=>r.peakHeap))}]})),tvNarrower:rs.filter(r=>r.tv[j].width<r.original[j].width).length}))});
 }
 return {status:"PASS",scope:"fresh weak/moderate stress, exact rational enclosures",roots:rows.length,rawChecks:rows.filter(r=>r.exactNumerator!==null).length,summary,rows,elapsedMs:Date.now()-start};
}
export {ceilDiv,sqrtCeil,min,prepareTV,tvEnvelope,solveTV,fixtureB,stress13};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(stress13(),null,2));
