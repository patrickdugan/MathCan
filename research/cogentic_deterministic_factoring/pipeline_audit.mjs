function detfact06(){
 const ck=(v,s)=>{if(!v)throw Error(s)};
 const abs=x=>x<0n?-x:x,mod=(x,n)=>((x%n)+n)%n;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 const lcm=(a,b)=>a/gcd(a,b)*b;
 function inv(a,n){let b=n,x=0n,y=1n;a=mod(a,n);while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}ck(b===1n,"inverse");return mod(x,n)}
 function pow(a,e,n){if(e<0n){a=inv(a,n);e=-e}let x=1n;for(a=mod(a,n);e;e>>=1n,a=a*a%n)if(e&1n)x=x*a%n;return x}
 function prime(n){if(n<2n)return false;for(let d=2n;d*d<=n;d++)if(n%d===0n)return false;return true}
 const sign=(x,N)=>x===1n||x===N-1n;
 const trim=a=>{a=a.slice();while(a.length>1&&a.at(-1)===0n)a.pop();return a};
 const add=(a,b)=>trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||0n)+(b[i]||0n)));
 const sub=(a,b)=>add(a,b.map(x=>-x));
 function mul(a,b){let c=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];return trim(c)}
 const eq=(a,b)=>trim(a).join(",")===trim(b).join(",");
 function ev(a,x,N=0n){let y=0n;for(let i=a.length-1;i>=0;i--){y=y*x+a[i];if(N)y=mod(y,N)}return y}
 const result=(status,stage,reason)=>({status,stage,reason});
 function factorResult(N,d,stage){ck(d>1n&&d<N&&N%d===0n,"improper factor");return {status:"factor",stage,d}}
 function unit(N,a,stage){let g=gcd(N,a);return g===1n?null:g<N?factorResult(N,g,stage):result("unresolved",stage,"zero modular denominator")}
 function crt(xs){let x=0n,M=1n;for(const [r,p] of xs){x+=M*mod((r-x)*inv(M,p),p);M*=p}return x}
 function rootCount(f,p){let n=0;for(let x=0n;x<p;x++)if(ev(f,x,p)===0n)n++;return n}
 function makePair(N,ell){
  let m=1n;while(m**4n<N)m++;const Q=6n*ell,c=4n*Q+3n;
  const b=[1n,1n,0n,0n,1n];let s=[1n],j=0;
  for(let x=0n;x<ell&&j<4;x++)if(x!==m%ell){s=mul(s,[-x,1n]);j++}ck(j===4,"split roots");
  let z=1n;while(rootCount([-z,0n,1n],ell))z++;
  const t=mul([-z,0n,1n],[-z,0n,1n]);
  const fs=[s,t].map(f=>{
   let R=Array.from({length:4},(_,i)=>crt([[b[i],2n],[i===0?1n:0n,3n],[mod(c*f[i],ell),ell]]));R.push(c);
   const v=ev(R,m),lo=(v+N-1n)/N,k=lo+mod(v*inv(N,Q)-lo,Q),H=(k*N-v)/Q;ck(H>=0n&&H<N,"lift");
   let h=H;for(let i=0;i<4;i++){R[i]+=Q*(h%m);h/=m}ck(h===0n,"digit overflow");return {f:R,k};
  });return {m,fs}
 }
 function irreducible4(f){
  let b=f.reduce((v,a,i)=>v|(mod(a,2n)<<BigInt(i)),0n);
  function deg(x){let d=-1;while(x){x>>=1n;d++}return d}
  function rem(x,y){while(x&&deg(x)>=deg(y))x^=y<<BigInt(deg(x)-deg(y));return x}
  return deg(b)===4&&[2n,3n,4n,5n,6n,7n].every(q=>rem(b,q)!==0n)
 }
 function verifyPair(N,ell,P){
  const {m,fs}=P,Q=6n*ell,c=4n*Q+3n;
  if(m<16n||(m-1n)**4n>=N||m**4n<=N||fs.length!==2)return false;
  for(let i=0;i<2;i++){
   const {f,k}=fs[i];
   if(f.length!==5||f[4]!==c||f.slice(0,4).some(x=>x<0n||x>=Q*m)||k<1n||k>=2n*c||gcd(k,Q)!==1n||ev(f,m)!==k*N||!irreducible4(f))return false;
   for(const p of [2n,3n])for(let x=0n;x<p;x++)if(ev(f,x,p)!==1n)return false;
   if(rootCount(f,ell)!==(i===0?4:0))return false;
   if(i===0){const df=f.slice(1).map((x,j)=>x*BigInt(j+1));for(let x=0n;x<ell;x++)if(ev(f,x,ell)===0n&&ev(df,x,ell)===0n)return false}
  }return true
 }
 function makeIdentity(f,N,P,i){
  const d=[1n,N],c=d.map(x=>P*x),k=[1n,2n*N],h=[1n,3n*N],R=[BigInt(i+1),-1n],S=[-2n,1n];
  return {a:add(mul(k,c),mul(f,R)),b:add(mul(k,d),mul(f,S)),c,d,h,q:mul(h,sub(mul(R,d),mul(S,c)))}
 }
 function transport(N,m,f,T){
  if(ev(f,m,N)!==0n||[T.b,T.d,T.h].some(a=>eq(a,[0n]))||!eq(mul(T.h,sub(mul(T.a,T.d),mul(T.b,T.c))),mul(f,T.q)))return result("invalid","transport","polynomial identity");
  for(const a of [T.b,T.d,T.h]){const u=unit(N,ev(a,m,N),"transport");if(u)return u}
  const x=ev(T.a,m,N)*inv(ev(T.b,m,N),N)%N,y=ev(T.c,m,N)*inv(ev(T.d,m,N),N)%N;
  if(x!==y)return result("invalid","transport","evaluation");
  return {status:"verified",x}
 }
 function product(N,ell,v){return pow(ell,v[0],N)*pow(2n,v[1],N)%N}
 function certifyColumn(N,C,j){
  const {ell,pair,A,columns}=C,{m,fs}=pair,t=columns[j],v=[A[0][j],A[1][j]];
  if(![1n,-1n].includes(t.s1)||![1n,-1n].includes(t.s2))return result("invalid","transport","sign domain");
  const a=transport(N,m,fs[0].f,t.t1);if(a.status!=="verified")return a;
  const b=transport(N,m,fs[1].f,t.t2);if(b.status!=="verified")return b;
  if(product(N,ell,v)*a.x%N!==mod(t.s1,N)||b.x!==mod(t.s2,N))return result("invalid","transport","signed column");
  if(a.x!==b.x)return result("invalid","transport","common image");
  return {status:"verified"}
 }
 function isolate(N,C){
  const {A,ell}=C;
  if(A.length!==2||A.some(r=>r.length!==2)||C.columns.length!==2)return result("invalid","lattice","shape");
  for(let j=0;j<2;j++){const r=certifyColumn(N,C,j);if(r.status!=="verified")return r}
  const [[a,b],[c,d]]=A,D=a*d-b*c;if(D===0n)return result("unresolved","lattice","singular pivot");
  const g=gcd(gcd(D,d),c),t=abs(D)/g,s=D<0n?-1n:1n,w=[s*d/g,-s*c/g];
  if(a*w[0]+b*w[1]!==t||c*w[0]+d*w[1]!==0n||pow(ell,2n*t,N)!==1n)return result("invalid","lattice","target witness");
  return {status:"verified",e:2n*t,detExponent:2n*abs(D)}
 }
 function binom(n,k){let v=1n;for(let i=1n;i<=k;i++)v=v*(n-k+i)/i;return v}
 function cap(N,B,r){let K=0n;for(let k=0n,x=1n;x<=N-1n;k++,x*=B){let top=x*B-1n;if(top>N-1n)top=N-1n;let z=top/binom(r+k,k);if(z>K)K=z}return K}
 function split(N,M,limit){
  if(M<=0n||M%2n)return result("invalid","split","exponent domain");
  let s=0,u=M;while(u%2n===0n){s++;u/=2n}
  for(let a=2n;a<N&&a<=limit;a++){let g=gcd(a,N);if(g>1n&&g<N)return {...factorResult(N,g,"split"),method:"base gcd",a};if(g!==1n)continue;
   let x=pow(a,u,N);for(let j=0;j<=s;j++){g=gcd(x-1n,N);if(g>1n&&g<N)return {...factorResult(N,g,"split"),method:"signed order",a};x=x*x%N}
  }return result("unresolved","split","scan budget");
 }
 // Only this function consumes certificates. It never calls the fixture order oracle.
 function pipeline(N,B,C,{minRelations=4,maxIndex=12000n,scanLimit=64n}={}){
  if(N<9n||N%2n===0n||B<5n||minRelations<1||maxIndex<1n)return result("invalid","input","domain");
  const u=unit(N,6n,"preconditioning");if(u)return u;
  const seen=new Set(),exponents=[],dets=[];
  for(const c of C){
   const ell=c.ell;
   if(ell<=4n||ell>B||!prime(ell)||seen.has(ell))return result("invalid","coverage","prime label");
   seen.add(ell);const v=unit(N,ell,"preconditioning");if(v)return v;
   if(!verifyPair(N,ell,c.pair))return result("invalid","preconditioning","pair");
   const r=isolate(N,c);if(r.status!=="verified")return r;
   exponents.push(r.e);dets.push(r.detExponent)
  }
  if(seen.size<minRelations)return result("unresolved","coverage","insufficient labels");
  let K=cap(N,B,BigInt(seen.size));if(K<1n||K>maxIndex)return result("unresolved","saturation","index budget");
  let S=1n;for(let i=2n;i<=K;i++)S=lcm(S,i);
  const Mstar=exponents.reduce(lcm,1n),M=2n*Mstar*S;
  if([...seen].some((p,i)=>pow(p,exponents[i],N)!==1n||pow(p,M,N)!==1n))return result("invalid","saturation","annihilator");
  return {...split(N,M,scanLimit),K,M,Mstar,relations:seen.size,strictReductions:exponents.filter((e,i)=>e<dets[i]).length}
 }
 // Fixture-only oracle: signed order by exhaustive enumeration.
 const orderCache=new Map();
 function order(N,a){let key=N+":"+a;if(orderCache.has(key))return orderCache.get(key);let e=1n,x=mod(a,N);while(!sign(x,N)){x=x*a%N;e++;ck(e<N,"order oracle")}orderCache.set(key,e);return e}
 function makeCert(N,ell,variant){
  const pair=makePair(N,ell),t=order(N,ell),s=order(N,2n);
  const A=variant?[[2n*t,-3n*t],[s,2n*s]]:[[2n*t,3n*t],[s,2n*s]];
  const columns=[0,1].map(j=>{let p=product(N,ell,[A[0][j],A[1][j]]);ck(sign(p,N),"oracle sign");const P=j? -1n:1n;return {s1:mod(p*P,N)===1n?1n:-1n,s2:P,t1:makeIdentity(pair.fs[0].f,N,P,j),t2:makeIdentity(pair.fs[1].f,N,P,j+2)}});
  return {ell,pair,A,columns}
 }
 const R={schema:"MATHCAN-DETFACT-AUDIT-06",fixture_model:"oracle-signed-order relations; conditional verifier only",composite_moduli:0,squarefree_moduli:0,repeated_factor_moduli:0,positive_pipelines:0,verified_factors:0,signed_order_splits:0,base_gcd_splits:0,polynomial_pairs:0,transported_column_pairs:0,lattice_exponents:0,strict_lattice_reductions:0,prime_factor_order_checks:0,max_N_bits:0,max_M_bits:0,max_index_cap:0,control_cases:[]};
 const families=[[211,251],[223,257],[239,277],[263,293],[307,311],[331,359],[373,401],[419,431],[37,41,43],[43,47,53],[41,41,43],[47,47,53]];
 let fixture;
 for(const fs of families){
  const ps=fs.map(BigInt),N=ps.reduce((a,b)=>a*b,1n);ck(ps.every(prime),"oracle primes");R.composite_moduli++;if(new Set(ps).size===ps.length)R.squarefree_moduli++;else R.repeated_factor_moduli++;
  R.max_N_bits=Math.max(R.max_N_bits,N.toString(2).length);
  for(const B of [19n,23n,31n]){
   const labels=[];for(let p=5n;p<=B;p++)if(prime(p))labels.push(p);
   const all=labels.map((ell,i)=>makeCert(N,ell,i%2));
   for(const C of [all,all.slice(0,4)]){
    const out=pipeline(N,B,C);ck(out.status==="factor"&&N%out.d===0n&&out.d>1n&&out.d<N,"positive pipeline "+N+":"+out.status+":"+out.stage);
    R.positive_pipelines++;R.verified_factors++;if(out.method==="signed order")R.signed_order_splits++;else R.base_gcd_splits++;
    R.polynomial_pairs+=C.length;R.transported_column_pairs+=2*C.length;R.lattice_exponents+=C.length;R.strict_lattice_reductions+=out.strictReductions;R.max_M_bits=Math.max(R.max_M_bits,out.M.toString(2).length);R.max_index_cap=Math.max(R.max_index_cap,Number(out.K));
    for(const p of new Set(ps)){ck(out.M%(p-1n)===0n,"oracle order coverage");R.prime_factor_order_checks++}
   }fixture={N,B,C:all,ps}
  }
 }
 const {N,B,C,ps}=fixture,c=C[0],t=c.columns[0];
 function control(name,cs,expected,stage,opts={},n=N,b=B){
  const r=pipeline(n,b,cs,opts);ck(r.status===expected&&r.stage===stage,name+": "+r.status+" "+r.stage);
  if(r.status==="factor")ck(r.d>1n&&r.d<n&&n%r.d===0n,"control divisor");
  R.control_cases.push({name,status:r.status,stage:r.stage,...(r.reason?{reason:r.reason}:{})})
 }
 const replace=c0=>[c0,...C.slice(1)];
 const editCol=t0=>replace({...c,columns:[t0,c.columns[1]]});
 control("short list",C.slice(0,3),"unresolved","coverage");
 control("duplicate prime",[c,...C],"invalid","coverage");
 control("composite target",replace({...c,ell:9n}),"invalid","coverage");
 control("prime beyond B",replace({...c,ell:37n}),"invalid","coverage");
 const pair={...c.pair,fs:[{...c.pair.fs[0],f:add(c.pair.fs[0].f,[1n])},c.pair.fs[1]]};
 control("bad polynomial root",replace({...c,pair}),"invalid","preconditioning");
 control("forged quotient",editCol({...t,t1:{...t.t1,q:add(t.t1.q,[1n])}}),"invalid","transport");
 control("wrong signed relation",editCol({...t,s1:-t.s1}),"invalid","transport");
 control("incompatible modular nuisance",editCol({...t,s2:-t.s2,t2:makeIdentity(c.pair.fs[1].f,N,-t.s2,0)}),"invalid","transport");
 control("valid singular matrix",replace({...c,A:c.A.map(r=>[r[0],r[0]]),columns:[t,t]}),"unresolved","lattice");
 control("saturation limit",C,"unresolved","saturation",{maxIndex:1n});
 control("split limit",C,"unresolved","split",{scanLimit:0n});
 function denomIdentity(d){return {a:[d*t.s2],b:[d],c:[t.s2],d:[1n],h:[1n],q:[0n]}}
 control("nonunit denominator exposes divisor",editCol({...t,t1:denomIdentity(ps[0])}),"factor","transport");
 control("zero evaluated denominator",editCol({...t,t1:denomIdentity(N)}),"unresolved","transport");
 control("target prime exposes divisor",replace({...c,ell:ps[0]}),"factor","preconditioning",{},N,ps[0]);
 return R
}

console.log(JSON.stringify(detfact06(),null,2));
