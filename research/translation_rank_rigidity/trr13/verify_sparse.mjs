function sparseAudit(){
 const ck=(x,m)=>{if(!x)throw Error(m)}, mod=(x,p)=>(x%p+p)%p;
 function inv(x,p){for(let i=1;i<p;i++)if(mod(x*i,p)===1)return i;throw Error("unit")}
 function trim(a){while(a.length&&a[a.length-1]===0)a.pop();return a}
 function gcdDegree(a,b,p){
   a=trim(a.slice());b=trim(b.slice());
   while(b.length){let r=a.slice(),d=inv(b[b.length-1],p);
     while(r.length>=b.length){const j=r.length-b.length,c=mod(r[r.length-1]*d,p);for(let i=0;i<b.length;i++)r[i+j]=mod(r[i+j]-c*b[i],p);trim(r)}
     a=b;b=r;
   }return a.length-1;
 }
 function xN(n,p){const a=Array(n+1).fill(0);a[0]=p-1;a[n]=1;return a}
 function polys(n,p,E){
   const h=Array(n).fill(0),g=Array.from({length:n},(_,i)=>i%p);h[0]=n%p;
   for(const [i,c] of E){g[i]=mod(g[i]+c,p);h[i]=mod(h[i]-c,p);h[(i+1)%n]=mod(h[(i+1)%n]+c,p)}
   ck(mod(h.reduce((a,b)=>a+b,0),p)===n%p,"augmentation");return {h,g};
 }
 function checkRank(n,p,E){
   const {h,g}=polys(n,p,E),v=xN(n,p),m=gcdDegree(v,h,p),r=n-gcdDegree(v,g,p);
   const expected=n-1-m+(mod(g.reduce((a,b)=>a+b,0),p)!==0?1:0);
   ck(r===expected,"Fourier rank and nontrivial roots");
   if(E.length===1)ck(m*(m-1)<=n-1,"single edit Sidon bound");
   return {h,m,r};
 }
 let one=0,maxSingle=0;const oneRows=[];
 for(const p of [2,3,5,7,11])for(let n=3;n<=31;n++)if(n%p!==0){
   let max=0,checks=0;
   for(let i=0;i<n;i++)for(let c=1;c<p;c++){
     const {m}=checkRank(n,p,[[i,c]]);max=Math.max(max,m);
     if(i===0||i===n-1)ck(m<=1,"endpoint edit");
     one++;checks++;
   }
   maxSingle=Math.max(maxSingle,max);oneRows.push({p,n,checks,maxMissing:max});
 }
 let seed=246813579;
 function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
 let dilation=0,nontrivial=0,largestN=0;const dilationRows=[];
 for(const n of [17,31,53,101,127,257])for(const p of [2,3,5,7,11])for(let k=1;k<=4;k++){
   let B=1;while((B+1)**(k+1)<n)B++;
   const L=Math.ceil(n/B)-1;let maxMissing=0,maxSpan=0;
   for(let trial=0;trial<8;trial++){
     const ix=new Set();while(ix.size<k)ix.add(rand(n));
     const E=[...ix].map(i=>[i,1+rand(p-1)]);
     const {h,m}=checkRank(n,p,E);
     const exps=[1,...ix],seen=new Map();let a,b,mu;
     for(let j=0;j<n;j++){
       const v=exps.map(i=>(j*i)%n),key=v.map(r=>Math.floor(r/(L+1))).join(",");
       if(seen.has(key)){const [old,oldv]=seen.get(key);mu=mod(j-old,n);const dif=v.map((r,i)=>r-oldv[i]);[a,...b]=dif;break}
       seen.set(key,[j,v]);
     }
     ck(mu!==undefined&&mu!==0&&Math.abs(a)<=L&&b.every(x=>Math.abs(x)<=L),"pigeonhole dilation");
     const exponentList=[0,...b,...b.map(x=>x+a)],span=Math.max(...exponentList)-Math.min(...exponentList);
     ck(span<=3*L,"Laurent span");
     const dilated=Array(n).fill(0),sparse=Array(n).fill(0);sparse[0]=n%p;
     for(let i=0;i<n;i++)dilated[mu*i%n]=h[i];
     for(let j=0;j<k;j++){const c=E[j][1],u=mod(b[j],n),v=mod(b[j]+a,n);sparse[u]=mod(sparse[u]-c,p);sparse[v]=mod(sparse[v]+c,p)}
     ck(sparse.every((x,i)=>x===dilated[i]),"dilated polynomial");
     ck(gcdDegree(xN(n,p),dilated,p)===m&&m<=span,"root bound and invariance");
     if(3*L<n-1)nontrivial++;
     maxMissing=Math.max(maxMissing,m);maxSpan=Math.max(maxSpan,span);largestN=Math.max(largestN,n);dilation++;
   }dilationRows.push({n,p,k,B,L,maxMissing,maxSpan,checks:8});
 }
 function pow(x,e,p){let y=1;while(e){if(e%2)y=mod(y*x,p);x=mod(x*x,p);e=Math.floor(e/2)}return y}
 let splitChecks=0,ratioPairs=0,splitMax=0;
 for(const [p,n] of [[11,5],[23,11],[29,7],[31,5],[43,7],[67,11],[79,13],[103,17],[191,19],[233,29],[311,31]]){
   const roots=Array.from({length:p-1},(_,i)=>i+1).filter(x=>pow(x,n,p)===1);
   ck(roots.length===n,"split roots");
   for(let i=0;i<n;i++)for(let c=1;c<p;c++){
     const zeros=roots.filter(z=>mod(n+c*pow(z,i,p)*(z-1),p)===0);
     const ratios=new Set();
     for(const z of zeros)for(const w of zeros)if(z!==w){const t=mod(z*inv(w,p),p);ck(!ratios.has(t),"ratio collision");ratios.add(t);ratioPairs++}
     ck(zeros.length*(zeros.length-1)<=n-1,"split Sidon");
     splitMax=Math.max(splitMax,zeros.length);splitChecks++;
   }
 }
 return {schema:"trr13-sparse-rank-v1",status:"passed",totals:{exhaustiveSingleEdits:one,maximumMissingModesSingleEdit:maxSingle,dilationChecks:dilation,nontrivialDilationBounds:nontrivial,largestDilationOrder:largestN,splitFieldSingleEdits:splitChecks,splitFieldRatioPairs:ratioPairs,maximumSplitMissingModes:splitMax},oneRows,dilationRows,scope:"Synthetic cyclic sequences; no scalar-recovery computation."};
}
console.log(JSON.stringify(sparseAudit(),null,2));
