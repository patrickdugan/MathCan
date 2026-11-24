// QBTC-04: exact random-table planting and raw ledger reference controls.
function qbtc04(){
 const ck=(x,m)=>{if(!x)throw Error(m)};
 const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
 const frac=(a,b)=>{const g=gcd(a,b);return [String(a/g),String(b/g)]};
 const result={schema:"qbtc-04-v1",tables:0,cases:[],ledger:[]};
 for(const N of [4,6,8])for(const M of [2,3,4]){
  const T=BigInt(M)**BigInt(N),K=BigInt(N*(N-1)/2),m=BigInt(M);
  let sum=0n,sum2=0n,abs=0n,nonempty=0n,selectedDestroyed=0n,plantedMass=0n;
  const hist=Array(Number(K)+1).fill(0n);
  for(let a=0;a<Number(T);a++){
   let z=a,C=0n;const vals=Array(N);
   for(let i=0;i<N;i++){vals[i]=z%M;z=Math.floor(z/M)}
   const counts=Array(M).fill(0);
   for(const v of vals){C+=BigInt(counts[v]);counts[v]++}
   let pairs=0n,first=null;
   for(let i=0;i<N;i++)for(let j=i+1;j<N;j++)if(vals[i]===vals[j]){pairs++;if(!first)first=[i,j]}
   ck(C===pairs,"collision count");
   hist[Number(C)]++;sum+=C;sum2+=C*C;plantedMass+=m*C;
   const diff=m*C-K;abs+=diff<0n?-diff:diff;
   if(first){nonempty++;
     let destroyed=0;
     for(let i=0;i<N;i++)for(let v=0;v<M;v++){
       const [j,k]=first;const a=i===j?v:vals[j],b=i===k?v:vals[k];if(a!==b)destroyed++;
     }
     ck(destroyed===2*(M-1),"single-row survival");selectedDestroyed+=BigInt(destroyed)
   }
  }
  ck(sum*m===T*K,"mean");
  ck((T*sum2-sum*sum)*m*m===T*T*K*(m-1n),"variance");
  ck(plantedMass===T*K,"plant normalization");
  let plantFirstSuccess=m*nonempty,plantDen=T*K;
  ck(plantFirstSuccess<=plantDen,"plant recovery");
  if(N>M)ck(nonempty===T&&plantFirstSuccess*K===plantDen*m,"compressing full selector");
  ck(abs*abs<=T*T*K*(m-1n),"TV bound");
  ck(selectedDestroyed===nonempty*2n*(m-1n),"destroy rate");
  let injective=1n;for(let i=0;i<N;i++)injective*=BigInt(Math.max(0,M-i));
  ck(nonempty===T-injective,"nonempty count");
  result.tables+=Number(T);
  result.cases.push({N,M,tables:Number(T),hist:hist.map(String),mean:frac(K,m),variance:frac(K*(m-1n),m*m),tv:frac(abs,2n*T*K),recoverPlant:frac(plantFirstSuccess,plantDen),destroyChosen:frac(2n*(m-1n),BigInt(N)*m),realCollisionSuccess:frac(nonempty,T)});
 }
 ck(result.cases.length===9&&result.tables===77595,"frozen enumeration");
 const prefixA=[["genesis","network-A"],["block",1,[["tx",0,"owner-A",7]]]];
 const prefixB=[["genesis","network-A"],["block",1,[["tx",0,"owner-A",9]]]];
 const ref=(prefix,h,t,o)=>JSON.stringify(["QBTC-04/ref",prefix,h,t,o]);
 const coord=(h,t,o)=>JSON.stringify([h,t,o]);
 const txA=ref(prefixA,1,0,0),txB=ref(prefixB,1,0,0);
 const tests=[["coordinate aliases across forks",coord(1,0,0)===coord(1,0,0)],["full prefix binds fork",txA!==txB],["output index bound",txA!==ref(prefixA,1,0,1)],["genesis context bound",txA!==ref([["genesis","network-B"],prefixA[1]],1,0,0)],["unchanged common prefix permits replay",txA===ref(JSON.parse(JSON.stringify(prefixA)),1,0,0)]];
 for(const [name,ok] of tests){ck(ok,name);result.ledger.push(name)}
 return result
}
console.log(JSON.stringify(qbtc04(),null,2));
