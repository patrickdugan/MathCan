// QBTC-06: exact matched-label likelihood and posterior extraction controls.
function qbtc06(){
 const assert=(x,m)=>{if(!x)throw Error(m)};
 const gcd=(a,b)=>b?gcd(b,a%b):a;
 const frac=(a,b)=>{const g=gcd(a,b);return [a/g,b/g]};
 const fall=(n,k)=>{let v=1;for(let i=0;i<k;i++)v*=n-i;return v};
 const choose=(n,k)=>k<0||k>n?0:fall(n,k)/fall(k,k);
 const decode=(i,n,m)=>Array.from({length:n},()=>{const v=i%m;i=Math.floor(i/m);return v});
 const indices=(n,k)=>{const out=[];function go(xs){if(xs.length===k){out.push(xs);return}for(let i=0;i<n;i++)if(!xs.includes(i))go([...xs,i])}go([]);return out};
 const edges=n=>Array.from({length:n},(_,i)=>Array.from({length:n-i-1},(_,j)=>[i,i+j+1])).flat();
 const matching=(es,k)=>{const out=[];function go(s,used,i){if(s.length===k){out.push(s);return}for(let j=i;j<es.length;j++){const [u,v]=es[j];if(!(used&(1<<u|1<<v)))go([...s,j],used|1<<u|1<<v,j+1)}}go([],0,0);return out};
 const result={schema:"qbtc-06-v1",cases:[],refresh:[],matchedTables:0,conditionalContexts:0,conditionalLabelOutcomes:0};
 for(const N of [4,6,8])for(const M of [2,3]){
  const es=edges(N),K=es.length,tableCount=M**N;
  for(let k=1;k<=N/2;k++){
   const L=N-k,tuples=indices(L,k),d=fall(L,k),wr=L**k;
   assert(tuples.length===d,"source tuple count");
   let contexts=0,outcomes=0;
   for(let h=0;h<M**L;h++){
    const x=decode(h,L,M),c=Array(M).fill(0);x.forEach(v=>c[v]++);
    const counts=Array(M**k).fill(0);
    for(const s of tuples){let j=0;for(let i=k-1;i>=0;i--)j=j*M+x[s[i]];counts[j]++}
    assert(counts.reduce((a,b)=>a+b,0)===d,"matched normalized");
    for(let j=0;j<M**k;j++){
     const y=decode(j,k,M),u=Array(M).fill(0);y.forEach(v=>u[v]++);
     const without=u.reduce((a,b,v)=>a*fall(c[v],b),1);
     const withrep=y.reduce((a,v)=>a*c[v],1);
     assert(counts[j]===without&&without<=withrep,"falling factorial and domination");
     for(const [a,b] of [[1,4],[1,2],[1,1]])if(M*Math.max(...c)*b<=(a+b)*L){
      assert(without*M**k*b**k<=wr*(a+b)**k,"uniform domination");
     }
     outcomes++;
    }
    contexts++;
   }
   // Plant a uniformly random k-matching, then draw a uniform table
   // conditioned on the equality of its endpoints.
   const ms=matching(es,k),expected=fall(N,2*k)/(2**k*fall(k,k));
   assert(ms.length===expected,"matching count");
   const total=ms.length*M**(N-k);
   let mass=0,best=0,first=0;const bad=[0,0,0],goodBest=[0,0,0];
   for(let h=0;h<tableCount;h++){
    const x=decode(h,N,M),c=Array(M).fill(0);x.forEach(v=>c[v]++);
    const eq=es.map(([i,j])=>x[i]===x[j]);
    const edgeMass=Array(K).fill(0);let W=0;
    for(const s of ms)if(s.every(e=>eq[e])){W++;for(const e of s)edgeMass[e]++}
    // Independent occupancy-polynomial count of compatible matchings.
    let poly=[1,...Array(k).fill(0)];
    for(const v of c){
     const next=Array(k+1).fill(0);
     for(let i=0;i<=k;i++)for(let j=0;j<=k-i&&2*j<=v;j++)next[i+j]+=poly[i]*fall(v,2*j)/(2**j*fall(j,j));
     poly=next;
    }
    assert(W===poly[k],"occupancy polynomial");
    assert(edgeMass.reduce((a,b)=>a+b,0)===k*W,"edge incidence");
    for(let e=0;e<K;e++)if(eq[e]){
     const v=c[x[es[e][0]]],a=edgeMass[e];
     assert(a*(v-1)<=W,"posterior matching bound");
     assert(a*choose(v,2)<=k*W,"posterior sparse bound");
    }
    const b=Math.max(...edgeMass),f=eq.indexOf(true);
    mass+=W;best+=b;if(f>=0)first+=edgeMass[f];
    for(let t=2;t<=4;t++)if(Math.min(...c)<t)bad[t-2]+=W;else goodBest[t-2]+=b;
   }
   assert(mass===total,"planted mass");
   for(let t=2;t<=4;t++){
    assert(goodBest[t-2]*(t-1)<=total-bad[t-2],"good min occupancy bound");
    assert(goodBest[t-2]*choose(t,2)<=k*(total-bad[t-2]),"good sparse bound");
   }
   assert(first<=best&&best<=total,"selector optimum");
   if(k===1)assert(first===best,"single planted pair uniform posterior");
   result.cases.push({N,M,k,L,contexts,outcomes,matchings:ms.length,tables:tableCount,total,best:frac(best,total),first:frac(first,total),bad:[2,3,4].map((t,i)=>({t,mass:frac(bad[i],total),goodBest:frac(goodBest[i],total)}))});
   result.conditionalContexts+=contexts;result.conditionalLabelOutcomes+=outcomes;result.matchedTables+=tableCount;
  }
  // Exact refresh witness invalidation and lower bound on output change.
  for(let k=1;k<=2;k++){
   const ds=Array.from({length:1<<N},(_,m)=>Array.from({length:N},(_,i)=>i).filter(i=>m&(1<<i))).filter(s=>s.length===k);
   const select=x=>es.findIndex(([i,j])=>x[i]===x[j]);
   let valid=0,invalidated=0,changed=0;
   for(let h=0;h<tableCount;h++){
    const x=decode(h,N,M),e=select(x);if(e<0)continue;valid++;
    const [a,b]=es[e];
    for(const s of ds)for(let v=0;v<M**k;v++){
     const y=x.slice(),z=decode(v,k,M);s.forEach((i,j)=>y[i]=z[j]);
     if(y[a]!==y[b])invalidated++;
     if(select(y)!==e)changed++;
    }
   }
   const hit=ds.length-choose(N-2,k),den=tableCount*ds.length*M**k;
   assert(invalidated===valid*hit*M**(k-1)*(M-1),"exact refresh invalidation");
   assert(changed>=invalidated,"selector disagreement lower bound");
   result.refresh.push({N,M,k,validTables:valid,invalidated:frac(invalidated,den),changedOnValid:frac(changed,den)});
  }
 }
 assert(result.cases.length===18&&result.refresh.length===12&&result.matchedTables===29841,"frozen census");
 return result;
}
console.log(JSON.stringify(qbtc06(),null,2));
