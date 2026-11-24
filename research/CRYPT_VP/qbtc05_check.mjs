// QBTC-05: exact latent-label resampling with fresh conditional encodings.
function qbtc05(){
 const ck=(v,m)=>{if(!v)throw Error(m)};
 const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
 const frac=(a,b)=>{const g=gcd(a,b);return [String(a/g),String(b/g)]};
 const decode=(x,n,radix)=>Array.from({length:n},()=>{const d=x%radix;x=Math.floor(x/radix);return d});
 // Encoded row z=(label,noise), p(z|label) proportional to [3,1] or [1,3].
 // Fresh marginal masses /8: [3,1,1,3]. Initial rows independent.
 const w=[3n,1n,1n,3n],lab=z=>z>>1;
 const D=(z,v)=>lab(z)===v?w[z]:0n;
 const choose=(n,k)=>{const a=[];for(let mask=0;mask<(1<<n);mask++){const x=Array.from({length:n},(_,i)=>i).filter(i=>mask&(1<<i));if(x.length===k)a.push(x)}return a};
 const observers=[
  ["or-noise",z=>z.some(v=>v&1)?1:0],
  ["parity-label",z=>z.reduce((a,v)=>a^lab(v),0)],
  ["all-label-equal",z=>z.every(v=>lab(v)===lab(z[0]))?1:0],
  ["weighted-euclidean",z=>z.reduce((a,v,i)=>a+v*(i+1),0)]
 ];
 const res={schema:"qbtc-05-v1",cases:[],contexts:0,conditionalOutcomes:0,checks:0,negative:[]};
 for(const N of [3,4,5])for(const k of [1,2]){
   const dests=choose(N,k),sourceN=N-k,sourceDen=4n*BigInt(sourceN),newDen=8n**BigInt(k),copyDen=sourceDen**BigInt(k);
   const thresholds=[[1n,4n],[1n,2n],[1n,1n]];
   let ctx=0,outcomes=0,initial=0n;
   let ag=thresholds.map(([a,b])=>({a,b,bad:0n,ind:Array(4).fill(0n),copy:Array(4).fill(0n),goodInd:Array(4).fill(0n),goodCopy:Array(4).fill(0n)}));
   let sumInd=Array(4).fill(0n),sumCopy=Array(4).fill(0n);
   for(let xi=0;xi<4**N;xi++){
     const x=decode(xi,N,4),mass=x.reduce((a,z)=>a*w[z],1n),fx=observers.map(([,f])=>f(x));
     for(const dest of dests){
       ctx++;initial+=mass;
       const sources=x.filter((_,i)=>!dest.includes(i)),counts=[sources.filter(v=>lab(v)===0).length,sources.filter(v=>lab(v)===1).length];
       const cw=w.map((v,z)=>v*BigInt(counts[lab(z)]));
       ck(cw.reduce((a,b)=>a+b,0n)===sourceDen,"copy normalized");
       const good=ag.map(({a,b})=>BigInt(Math.max(...counts))*2n*b<=BigInt(sourceN)*(a+b));
       const condInd=Array(4).fill(0n),condCopy=Array(4).fill(0n);
       let normI=0n,normC=0n;
       for(let yi=0;yi<4**k;yi++){
         outcomes++;const yy=decode(yi,k,4),y=x.slice();dest.forEach((v,j)=>{y[v]=yy[j]});
         const pi=yy.reduce((a,z)=>a*w[z],1n),pc=yy.reduce((a,z)=>a*cw[z],1n);
         normI+=pi;normC+=pc;
         // Independent source labels vs independent index sampling from source rows.
         // Direct count of all source-index tuples times conditional encoding mass.
         let direct=0n;
         for(let j=0;j<sourceN**k;j++){
           const ix=decode(j,k,sourceN);
           direct+=yy.reduce((a,z,l)=>a*D(z,lab(sources[ix[l]])),1n);
         }
         ck(pc===direct,"explicit source indices");
         for(let q=0;q<ag.length;q++)if(good[q]){
           const {a,b}=ag[q];ck(pc*newDen*b**BigInt(k)<=pi*copyDen*(a+b)**BigInt(k),"pointwise product domination")
         }
         for(let j=0;j<4;j++){
           const v=BigInt((observers[j][1](y)-fx[j])**2);
           condInd[j]+=pi*v;condCopy[j]+=pc*v;
         }
       }
       ck(normI===newDen&&normC===copyDen,"replacement normalized");
       for(let j=0;j<4;j++){
         sumInd[j]+=mass*condInd[j];sumCopy[j]+=mass*condCopy[j];
       }
       for(let q=0;q<ag.length;q++){
         const a=ag[q];if(!good[q])a.bad+=mass;
         for(let j=0;j<4;j++){
           a.ind[j]+=mass*condInd[j];a.copy[j]+=mass*condCopy[j];
           if(good[q]){a.goodInd[j]+=mass*condInd[j];a.goodCopy[j]+=mass*condCopy[j]}
         }
       }
     }
   }
   ck(initial===8n**BigInt(N)*BigInt(dests.length),"initial mass");
   for(const a of ag)for(let j=0;j<4;j++){
     const ap=(a.a+a.b)**BigInt(k),bp=a.b**BigInt(k);
     const bound=j===3?BigInt((3*N*(N+1)/2)**2):1n;
     ck(a.goodCopy[j]*newDen*bp<=a.goodInd[j]*copyDen*ap,"good cost transfer");
     ck(a.copy[j]*newDen*bp<=a.ind[j]*copyDen*ap+a.bad*bound*copyDen*newDen*bp,"unconditional bound");
     res.checks++;
   }
   res.contexts+=ctx;res.conditionalOutcomes+=outcomes;
   res.cases.push({N,k,contexts:ctx,outcomes,costs:observers.map(([name],j)=>({name,ind:frac(sumInd[j],initial*newDen),copy:frac(sumCopy[j],initial*copyDen)})),thresholds:ag.map(a=>({delta:frac(a.a,a.b),bad:frac(a.bad,initial)}))});
 }
 ck(res.cases.length===6&&res.checks===72,"case count");
 // independent k-row replacement cost subadditivity for these Boolean AND Euclidean observers.
 for(const c of res.cases.filter(c=>c.k===2)){
   const s=res.cases.find(x=>x.N===c.N&&x.k===1);
   for(let j=0;j<4;j++){
     const [a,b]=c.costs[j].ind.map(BigInt),[d,e]=s.costs[j].ind.map(BigInt);
     ck(a*e<=2n*d*b,"independent k-row energy subadditivity");
   }
 }
 // Balanced untouched population: adaptive J selects label 1, fresh label uniform.
 // Shared source forces equal replacement labels; independent source indices do not.
 // Copying physical encoding from one fixed source vs fresh D on 8 equiprobable encodings.
 const balanced=[0,1], physical=Array.from({length:8},(_,v)=>v);
 const prob=(xs,p)=>frac(BigInt(xs.filter(p).length),BigInt(xs.length));
 const experiments=[
   ["adaptive-source",balanced,[Math.max(...balanced)],v=>v===1],
   ["shared-source-k2",balanced.flatMap(x=>balanced.map(y=>[x,y])),balanced.map(x=>[x,x]),([x,y])=>x===y],
   ["physical-copy",physical,[physical[3]],v=>v===3]
 ];
 const negative=experiments.map(([name,xs,ys,p])=>{
   const ind=prob(xs,p),correlated=prob(ys,p);
   const [a,b]=ind.map(BigInt),[c,d]=correlated.map(BigInt);
   return {name,ind,correlated,maxRatio:frac(c*b,d*a)};
 });
 ck(JSON.stringify(negative.map(x=>x.maxRatio))===JSON.stringify([["2","1"],["2","1"],["8","1"]]),"negative ratios");
 res.negative=negative;
 return res
}
console.log(JSON.stringify(qbtc05(),null,2));
