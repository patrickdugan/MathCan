function audit() {
 const ck=(x,s)=>{if(!x)throw Error(s)};
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
 const lcm=(a,b)=>a/gcd(a,b)*b;
 const pow=(a,e,n)=>{let x=1n;for(a%=n;e>0n;e>>=1n,a=a*a%n)if(e&1n)x=x*a%n;return x};
 const factor=n=>{let f=[];for(let d=2n;d*d<=n;d++)if(n%d===0n){let e=0;while(n%d===0n){n/=d;e++}f.push([d,e])}if(n>1n)f.push([n,1]);return f};
 const prime=p=>p>=2n&&factor(p)[0][0]===p;
 const order=(a,n)=>{ck(gcd(a,n)===1n,"unit");let x=a%n,e=1n;while(x!==1n){x=x*a%n;e++;ck(e<n,"order")}return e};
 const binom=(n,k)=>{let c=1n;for(let j=1n;j<=k;j++)c=c*(n-k+j)/j;return c};
 const lg=(x,b)=>{let k=0n;while(x>=b){x/=b;k++}return k};
 const min=(a,b)=>a<b?a:b;
 const ceil=(a,b)=>(a+b-1n)/b;
 function bounds(n,B,r){let h=lg(n-1n,B),t=0n;for(let k=0n;k<=h;k++){let x=min(n-1n,B**(k+1n)-1n)/binom(r+k,k);if(x>t)t=x}return [t,min(n-1n,h===0n?B:B*ceil(B*h,r)**h)]}
 function monomials(b,k,p){let ints=new Set(),res=new Set(),total=0;function walk(i,left,a){total++;ints.add(a);res.add(a%p);if(left)for(let j=i;j<b.length;j++)walk(j,left-1n,a*b[j])}walk(0,k,1n);return {ints,res,total}}
 const R={schema:"MATHCAN-DETFACT-AUDIT-02",composite_bound:511,prime_bound:251,base_bounds:[3,5,7,11,13,17,19,23],composites:0,repeated_prime_factor_inputs:0,composite_fixtures:0,prime_fixtures:0,local_prime_checks:0,monomial_witnesses:0,strict_cap_improvements:0,negative_controls:0};
 const primes=Array.from({length:22},(_,i)=>BigInt(i+2)).filter(prime);
 function one(n,B,b,ps,composite){
  ck(b.length>0&&new Set(b).size===b.length&&b.every(a=>a<=B&&prime(a)&&gcd(a,n)===1n),"labels");
  const r=BigInt(b.length),e=b.map(a=>order(a,n)),m=e.reduce(lcm,1n),[K,C]=bounds(n,B,r);
  ck(K>=1n&&K<=C&&b.every((a,i)=>pow(a,e[i],n)===1n&&m%e[i]===0n),"caps and certs");
  if(K<C)R.strict_cap_improvements++;
  let sat=1n;for(let i=2n;i<=K;i++)sat=lcm(sat,i);
  for(const p of ps){
   let k=lg(p-1n,B),w=monomials(b,k,p),c=binom(r+k,k);
   ck(BigInt(w.total)===c&&w.ints.size===w.total&&w.res.size===w.total&&[...w.ints].every(a=>a>=1n&&a<p),"injection");
   let H=new Set([1n]);for(const a of b){const old=new Set(H);for(let x=a%p;!old.has(x);x=x*a%p)for(const y of old)H.add(x*y%p)}
   const z=BigInt(H.size);ck([...w.res].every(x=>H.has(x))&&z>=c&&(p-1n)%z===0n&&m%z===0n,"subgroup");
   const I=(p-1n)/z;ck(I<=K&&I<=C&&sat%I===0n&&(2n*m*sat)%(p-1n)===0n,"saturation");
   R.local_prime_checks++;R.monomial_witnesses+=w.total
  }
  if(composite)R.composite_fixtures++;else R.prime_fixtures++;
 }
 for(let n=9n;n<=511n;n+=2n){const f=factor(n);if(f.length<2)continue;R.composites++;if(f.some(([,e])=>e>1))R.repeated_prime_factor_inputs++;
  for(const B of R.base_bounds.map(BigInt)){const b=primes.filter(a=>a<=B&&gcd(a,n)===1n),seen=new Set();if(!b.length)continue;for(const s of [b,b.filter((_,i)=>i%2===0),b.slice(0,1)]){const key=s.join(",");if(!seen.has(key)){seen.add(key);one(n,B,s,f.map(([p])=>p),true)}}}
 }
 for(let p=3n;p<=251n;p+=2n)if(prime(p))for(const B of R.base_bounds.map(BigInt)){let b=primes.filter(a=>a<=B&&a!==p);if(b.length)one(p,B,b,[p],false)}
 const bad=monomials([2n,4n],2n,31n);ck(bad.total===6&&bad.res.size===5&&order(2n,31n)===5n,"composite base");R.negative_controls++;
 const dup=monomials([2n,2n],2n,31n);ck(dup.res.size<dup.total,"duplicate");R.negative_controls++;
 ck(pow(2n,2n,15n)!==1n,"wrong exponent");R.negative_controls++;
 ck(pow(4n,2n,15n)===1n&&2n%4n!==0n,"insufficient bases");R.negative_controls++;
 return R
}

console.log(JSON.stringify(audit(),null,2));
