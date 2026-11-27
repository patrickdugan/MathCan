function detfact07(){
 const ck=(x,s)=>{if(!x)throw Error(s)};
 const abs=x=>x<0n?-x:x,mod=(x,n)=>((x%n)+n)%n,bits=x=>x===0n?0:x.toString(2).length;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 const lcm=(a,b)=>a/gcd(a,b)*b;
 function twos(x){ck(x>0n,"positive integer");let s=0;while(x%2n===0n){x/=2n;s++}return {s,u:x}}
 function pwr(p,K){let q=p;while(q<=K/p)q*=p;return q}
 function stats(){return {calls:0,modular_multiplications:0,prime_trial_divisions:0,prime_powers:0,exponentiations:0,max_exponent_operand_bits:0,max_two_factor_product_bound_bits:0,chain_squarings:0,chain_gcds:0}}
 function pow(a,e,N,T){
  ck(e>=1n&&N>=2n,"power domain");T.exponentiations++;T.max_exponent_operand_bits=Math.max(T.max_exponent_operand_bits,bits(e));
  a=mod(a,N);let x=a,s=e.toString(2);
  for(let i=1;i<s.length;i++){x=x*x%N;T.modular_multiplications++;if(s[i]==="1"){x=x*a%N;T.modular_multiplications++}}
  return x
 }
 function oddPrime(p,T){ck(p>=3n&&p%2n===1n,"odd candidate");for(let d=3n;d<=p/d;d+=2n){T.prime_trial_divisions++;if(p%d===0n)return false}return true}
 function* factors(K,T){for(let p=3n;p<=K;p+=2n)if(oddPrime(p,T)){T.prime_powers++;yield pwr(p,K)}}
 function explicit(Mstar,K){ck(Mstar>0n&&K>=1n,"domain");let S=1n;for(let j=2n;j<=K;j++)S=lcm(S,j);return twos(2n*Mstar*S)}
 function streamingPlan(Mstar,K){ck(Mstar>0n&&K>=1n,"domain");let {s,u}=twos(Mstar);return {s:1+s+bits(K)-1,u,K}}
 function direct(a,N,plan,T){T.calls++;return pow(a,plan.u,N,T)}
 function stream(a,N,plan,T,budget){
  ck(Number.isSafeInteger(budget)&&budget>=1,"chunk budget");
  T.calls++;
  // Mstar is a supplied explicit input; do not promise that its odd part fits the chunk cap.
  let x=mod(a,N);
  if(plan.u!==1n)x=pow(x,plan.u,N,T);
  let chunk=1n;
  function flush(){if(chunk!==1n){x=pow(x,chunk,N,T);chunk=1n}}
  for(const q of factors(plan.K,T)){
   // The sum of bit lengths is a safe upper bound, so never allocate a too-wide product.
   if(bits(q)>budget){flush();x=pow(x,q,N,T);continue}
   if(chunk!==1n&&bits(chunk)+bits(q)>budget)flush();
   if(chunk===1n)chunk=q;
   else {T.max_two_factor_product_bound_bits=Math.max(T.max_two_factor_product_bound_bits,bits(chunk)+bits(q));chunk*=q}
   ck(bits(chunk)<=budget,"chunk invariant");
  }
  flush();return x
 }
 function split(N,s,get,T,limit=64n){
  for(let a=2n;a<N&&a<=limit;a++){
   let d=gcd(a,N);if(d>1n&&d<N)return {d,a,j:-1};if(d!==1n)continue;
   let x=get(a);
   for(let j=0;j<=s;j++){d=gcd(x-1n,N);T.chain_gcds++;if(d>1n&&d<N)return {d,a,j};if(j<s){x=x*x%N;T.chain_squarings++}}
  }return null
 }
 function binom(n,k){let c=1n;for(let j=1n;j<=k;j++)c=c*(n-k+j)/j;return c}
 function cap(N,B,r){let K=0n;for(let k=0n,x=1n;x<=N-1n;k++,x*=B){let a=x*B-1n;if(a>N-1n)a=N-1n;let q=a/binom(r+k,k);if(q>K)K=q}return K}
 function plainpow(a,e,N){let x=1n;for(a=mod(a,N);e;e>>=1n,a=a*a%N)if(e&1n)x=x*a%N;return x}
 const cache=new Map();function signedOrder(N,a){let k=N+":"+a;if(cache.has(k))return cache.get(k);let x=a%N,t=1n;while(x!==1n&&x!==N-1n){x=x*a%N;t++;ck(t<N,"oracle")}cache.set(k,t);return t}
 const variants=[["individual",1],["chunk64",64],["chunk256",256]];
 function suite(){return Object.fromEntries(["explicit",...variants.map(([x])=>x)].map(k=>[k,stats()]))}
 const R={schema:"MATHCAN-DETFACT-AUDIT-07",measurement:"exact operation counts and integer width proxies; not wall time or RSS",pipeline_fixtures:0,matching_split_results:0,matching_modular_outputs:0,group_order_coverage_checks:0,edge_fixtures:0,edge_outputs:0,negative_controls:0,pipeline_stats:suite(),edge_stats:suite(),stress:[]};
 const families=[[211,251],[223,257],[239,277],[263,293],[307,311],[331,359],[373,401],[419,431],[37,41,43],[43,47,53],[41,41,43],[47,47,53]];
 function trial(N,Mstar,K,T,bases,doSplit=false){
  let E=explicit(Mstar,K),P=streamingPlan(Mstar,K);ck(E.s===P.s,"two-adic valuation");
  // Independent reference power uses right-to-left binary evaluation.
  let checked=0;for(const a of bases){let x=direct(a,N,E,T.explicit);ck(x===plainpow(a,E.u,N),"reference");
   for(const [name,b] of variants){let y=stream(a,N,P,T[name],b);ck(x===y,"residue mismatch");checked++}
  }
  if(doSplit){
   const x=split(N,E.s,a=>direct(a,N,E,T.explicit),T.explicit);
   ck(x&&x.d>1n&&x.d<N&&N%x.d===0n,"explicit proper factor");
   for(const [name,b] of variants){const y=split(N,P.s,a=>stream(a,N,P,T[name],b),T[name]);ck(y&&x.d===y.d&&x.a===y.a&&x.j===y.j,"split mismatch")}
  }
  return {checked,oddBits:bits(E.u),fullBits:bits(E.u)+E.s,s:E.s}
 }
 for(const fam of families){
  const ps=fam.map(BigInt),N=ps.reduce((a,b)=>a*b,1n);
  for(const B of [19n,23n,31n]){
   let labels=[5n,7n,11n,13n,17n,19n,23n,29n,31n].filter(p=>p<=B);
   for(const set of [labels,labels.slice(0,4)]){
    // Recreate DETFACT-06's target exponents at the saturation interface:
    // primitive target multiplier t or 7t depending on the pivot variant.
    const es=set.map((p,i)=>2n*signedOrder(N,p)*(i%2?7n:1n));
    ck(set.every((p,i)=>plainpow(p,es[i],N)===1n),"supplied annihilator");
    const Mstar=es.reduce(lcm,1n),K=cap(N,B,BigInt(set.length));
    const ref=explicit(Mstar,K);for(const p of new Set(ps)){ck(((1n<<BigInt(ref.s))*ref.u)%(p-1n)===0n,"oracle group coverage");R.group_order_coverage_checks++}
    const r=trial(N,Mstar,K,R.pipeline_stats,[2n,3n,5n,7n,11n,13n,17n,19n],true);R.matching_modular_outputs+=r.checked;R.pipeline_fixtures++;R.matching_split_results+=variants.length;
   }
  }
 }
 for(const N of [15n,45n,77n,143n])for(const Mstar of [1n,2n,15n,96n,257n])for(const K of [1n,2n,3n,7n,8n,9n,15n,16n,17n,31n,32n,33n]){
  const r=trial(N,Mstar,K,R.edge_stats,[0n,1n,2n,3n,5n,N-1n,N]);R.edge_fixtures++;R.edge_outputs+=r.checked
 }
 for(const K of [1024n,4096n,16384n,32768n,65536n]){
  const T=suite(),N=1009n*1013n,Mstar=2n**9n*3n**5n*5n*7n*11n;
  const r=trial(N,Mstar,K,T,[2n,3n,5n]);
  R.stress.push({K:Number(K),N_bits:bits(N),Mstar_bits:bits(Mstar),odd_exponent_bits:r.oddBits,full_exponent_bits:r.fullBits,two_adic_valuation:r.s,stats:T,matching_outputs:r.checked});
 }
 function rejects(fn,reason){try{fn()}catch(e){ck(e.message===reason,"wrong rejection");R.negative_controls++;return}throw Error("bad accepted")}
 rejects(()=>streamingPlan(0n,8n),"domain");rejects(()=>streamingPlan(1n,0n),"domain");
 rejects(()=>stream(2n,15n,streamingPlan(1n,8n),stats(),0),"chunk budget");
 // Omitting a prime-power exponent silently changes the evaluation.
 const e=explicit(1n,9n);ck(e.u===315n&&plainpow(2n,e.u,23n)!==plainpow(2n,e.u/3n,23n),"prime-power omission");R.negative_controls++;
 // Product saturation cannot in general be replaced by lcm(Mstar,S_K).
 ck(4n*12n%16n===0n&&lcm(4n,12n)%16n!==0n,"lcm substitution");R.negative_controls++;
 return R
}

console.log(JSON.stringify(detfact07(),null,2));
