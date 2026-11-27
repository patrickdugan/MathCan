function run() {
 const ck=(x,s)=>{if(!x)throw Error(s)};
 const mod=(a,p)=>((a%p)+p)%p;
 const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a<0n?-a:a};
 function inv(a,p){let x=0n,y=1n,b=p;a=mod(a,p);while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}ck(b===1n,"inverse");return mod(x,p)}
 function prime(p){if(p<2n)return false;for(let i=2n;i*i<=p;i++)if(p%i===0n)return false;return true}
 function evalp(a,x,p=0n){let y=0n;for(let i=a.length-1;i>=0;i--){y=y*x+a[i];if(p)y=mod(y,p)}return y}
 function mul(a,b,p){let r=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)r[i+j]=mod(r[i+j]+a[i]*b[j],p);return r}
 function rootcount(a,p){let t=0;for(let x=0n;x<p;x++)if(evalp(a,x,p)===0n)t++;return t}
 function degree(a){let d=-1;while(a){a>>=1n;d++}return d}
 function rem2(a,b){let d=degree(b);while(a&&degree(a)>=d)a^=b<<BigInt(degree(a)-d);return a}
 function irred2(a,d){if(degree(a)!==d)return false;for(let k=1;k<=Math.floor(d/2);k++)for(let b=(1n<<BigInt(k));b<(2n<<BigInt(k));b++)if(rem2(a,b)===0n)return false;return true}
 function binaryIrred(d){for(let a=(1n<<BigInt(d))+1n;a<(2n<<BigInt(d));a+=2n)if(irred2(a,d))return Array.from({length:d+1},(_,i)=>(a>>BigInt(i))&1n);throw Error("binary irreducible")}
 function rootfreeLow(p,d){if(d===2){for(let a=1n;a<p;a++){let f=[mod(-a,p),0n,1n];if(rootcount(f,p)===0)return f}}else{for(let a=0n;a<p;a++)for(let b=0n;b<p;b++)for(let c=1n;c<p;c++){let f=[c,b,a,1n];if(rootcount(f,p)===0)return f}}throw Error("rootfree")}
 function targetPolys(d,m,ell,c){
  let a=[1n],b=[1n],count=0;
  for(let x=0n;x<ell&&count<d;x++)if(x!==m%ell){a=mul(a,[mod(-x,ell),1n],ell);count++}
  ck(count===d,"roots available");
  let j=d;if(j%2){b=mul(b,rootfreeLow(ell,3),ell);j-=3}
  const q=rootfreeLow(ell,2);for(;j>0;j-=2)b=mul(b,q,ell);
  return [a,b].map(f=>f.map(x=>mod(x*c,ell)))
 }
 function crt(items){let x=0n,M=1n;for(const [r,p] of items){x+=M*mod((r-x)*inv(M,p),p);M*=p}return x}
 function construct(n,m,d,z,ell) {
  const ps=Array.from({length:z-1},(_,i)=>BigInt(i+2)).filter(prime);
  const P=ps.reduce((a,b)=>a*b,1n),Q=P*ell,c=4n*Q+P/2n;
  ck(d>=4&&m>=BigInt(4*d)&&ell>BigInt(Math.max(z,d))&&prime(ell)&&gcd(n,Q)===1n&&(m-1n)**BigInt(d)<n&&n<m**BigInt(d),"domain");
  const b=binaryIrred(d);
  const [s,t]=targetPolys(d,m,ell,c);
  const out=[s,t].map(a=>{
   const R=Array.from({length:d},(_,i)=>crt([...ps.map(p=>[p===2n?b[i]:(i===0?1n:0n),p]),[a[i],ell]]));R.push(c);
   const value=evalp(R,m), lower=(value+n-1n)/n, k=lower+mod(value*inv(n,Q)-lower,Q), h=(k*n-value)/Q;
   ck((k*n-value)%Q===0n&&h>=0n&&h<n,"lift interval");
   let H=h;const f=R.slice();for(let i=0;i<d;i++){f[i]+=Q*(H%m);H/=m}ck(H===0n,"base m expansion");
   return {f,k}
  });
  return {ps,P,Q,c,out}
 }
 function validate(n,m,d,z,ell,cx,checkWidth=true) {
  const {ps,P,Q,c,out}=cx;
  ck(out.length===2&&c>=4n*Q&&c%2n===1n&&c%(P/2n)===0n&&c%ell!==0n,"leading domain");
  for(let i=0;i<2;i++){
   const {f,k}=out[i];ck(f.length===d+1&&f[d]===c,"leading");
   ck(evalp(f,m)===k*n&&k>=1n&&k<2n*c&&gcd(k,Q)===1n,"evaluation");
   if(checkWidth)ck(f.slice(0,d).every(a=>a>=0n&&a<Q*m),"width");
   const bits=f.reduce((a,v,j)=>a|(mod(v,2n)<<BigInt(j)),0n);ck(irred2(bits,d),"binary");
   for(const p of ps)for(let x=0n;x<p;x++)ck(evalp(f,x,p)===1n,"small-prime values");
   ck(rootcount(f,ell)===(i===0?d:0),"target roots");
   if(i===0){const df=f.slice(1).map((v,j)=>v*BigInt(j+1));for(let x=0n;x<ell;x++)if(evalp(f,x,ell)===0n)ck(evalp(df,x,ell)!==0n,"simple root")}
  }
 }
 function perturb(f,Q,m,g){const a=f.slice();for(let i=0;i<g.length;i++){a[i]-=Q*m*g[i];a[i+1]+=Q*g[i]}return a}
 const R={schema:"MATHCAN-DETFACT-AUDIT-03",degree_range:[4,10],z_values:[3,5,7],pair_fixtures:0,polynomial_checks:0,perturbed_pair_fixtures:0,perturbation_injectivity_checks:0,negative_controls:0,largest_N_bits:0};
 let fixture;
 for(let d=4;d<=10;d++)for(const m of [BigInt(4*d),BigInt(4*d+1),BigInt(5*d)])for(const z of R.z_values){
  const es=[11n,13n,17n,19n,23n,29n].filter(p=>p>BigInt(Math.max(z,d))).slice(0,3);
  for(const ell of es)for(const off of [0n,17n]){
   const P=[2n,3n,5n,7n].filter(p=>p<=BigInt(z)).reduce((a,b)=>a*b,1n),Q=P*ell,lo=(m-1n)**BigInt(d),hi=m**BigInt(d);
   let q=lo/31n+1n+off;while(q%2n===0n||gcd(q,Q)!==1n)q++;let n=31n*q;ck(n>lo&&n<hi&&n%31n===0n&&n>31n,"fixture bracket");
   const cx=construct(n,m,d,z,ell);validate(n,m,d,z,ell,cx);R.pair_fixtures++;R.polynomial_checks+=2;R.largest_N_bits=Math.max(R.largest_N_bits,n.toString(2).length);
   const g1=Array.from({length:d-1},(_,j)=>BigInt((j%3)-1)),g2=Array.from({length:d-1},(_,j)=>BigInt((j%5)-2));
   const out=cx.out.map(({f,k},i)=>({f:perturb(f,Q,m,i?g2:g1),k}));validate(n,m,d,z,ell,{...cx,out},false);R.perturbed_pair_fixtures++;R.polynomial_checks+=2;
   let seen=new Set();for(const a of [-1n,0n,1n])for(const b of [-1n,0n,1n]){const key=perturb(cx.out[0].f,Q,m,[a,b]).join(",");ck(!seen.has(key),"perturb injection");seen.add(key);R.perturbation_injectivity_checks++}
   fixture={n,m,d,z,ell,cx}
  }
 }
 const {n,m,d,z,ell,cx}=fixture;
 function reject(changed,reason){try{validate(n,m,d,z,ell,changed,false)}catch(e){ck(e.message===reason,"wrong reject: "+e.message);R.negative_controls++;return}throw Error("accepted mutation")}
 const broken=cx.out.map(x=>({f:x.f.slice(),k:x.k}));broken[0].f[0]+=1n;reject({...cx,out:broken},"evaluation");
 reject({...cx,out:[cx.out[0],cx.out[0]]},"target roots");
 const wrong=cx.out.map(x=>({f:x.f.slice(),k:x.k}));wrong[1].k+=1n;reject({...cx,out:wrong},"evaluation");
 return R
}

console.log(JSON.stringify(run(),null,2));
