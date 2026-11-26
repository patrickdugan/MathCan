function independent(){
 const fail=(s)=>{throw Error(s)}, ok=(b,s)=>{if(!b)fail(s)};
 function prime(n){if(n<2n)return false;for(let t=2n;t*t<=n;t++)if(n%t===0n)return false;return true}
 function gcd(a,b){while(b){[a,b]=[b,a%b]}return a<0n?-a:a}
 function pow(a,e,n){let r=1n;while(e>0n){if(e&1n)r=r*a%n;a=a*a%n;e>>=1n}return r}
 function degree(x){return x===0n?-1:x.toString(2).length-1}
 function bgcd(a,b){while(b){let r=a;while(r&&degree(r)>=degree(b))r^=b<<BigInt(degree(r)-degree(b));[a,b]=[b,r]}return a}
 function bitpoly(exps){return exps.reduce((a,e)=>a^(1n<<BigInt(e)),0n)}
 const diffs=new Set();
 for(const a of [1,2,4])for(const b of [1,2,4])if(a!==b)diffs.add((a-b+7)%7);
 ok(diffs.size===6,"Gaussian periods difference set");
 // alpha^3=alpha+1 in F8; independently check absolute traces.
 function fm(a,b){let r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&8)a^=11}return r}
 let z=1;const traceZero=[];
 for(let j=0;j<7;j++){const z2=fm(z,z),z4=fm(z2,z2);if((z^z2^z4)===0)traceZero.push(j);z=fm(z,2)}
 ok(traceZero.join(",")==="1,2,4","base trace");
 function V(e){let a=2n,b=-1n;for(let j=0;j<e;j++)[a,b]=[b,-b-2n*a];return a}
 function cofactor(e){const q=1n<<BigInt(e),u=q*q+q+1n,v=q+1n+3n*(e%2?1n:-1n)*V(e);ok(u%7n===0n&&v%7n===0n,"integer counts");return {q,U:u/7n,m:v/7n}}
 const small=[];
 for(const e of [1,2,4,5,7,8]){
   const {q,U,m}=cofactor(e);const g=bgcd(bitpoly([0,Number(q),Number(q)+1]),bitpoly([0,Number(U)]));
   ok(BigInt(degree(g))===m,"cofactor gcd");
   small.push({e,U:String(U),m:String(m)})
 }
 const rows=[];
 for(const [e,witness,fac] of [[11,6,[[2,1],[3,1],[11,1],[31,1],[293,1]]],[23,6,[[2,1],[3,1],[11,1],[23,1],[89,1],[683,1],[108943,1]]],[31,21,[[2,1],[3,2],[11,1],[31,1],[83,1],[151,1],[331,1],[1277,1],[20261,1]]]]){
   const {U,m}=cofactor(e),w=BigInt(witness);let prod=1n;
   for(const [p,a] of fac){ok(prime(BigInt(p)),"prime factor");prod*=BigInt(p)**BigInt(a)}
   ok(prod===U-1n&&pow(w,U-1n,U)===1n,"Lucas product and power");
   for(const [p] of fac)ok(gcd(pow(w,(U-1n)/BigInt(p),U)-1n,U)===1n,"Lucas witness");
   ok(pow(2n,BigInt(3*e),U)===1n,"order");
   for(let p=2;p<=3*e;p++)if(3*e%p===0&&prime(BigInt(p)))ok(pow(2n,BigInt(3*e/p),U)!==1n,"exact order");
   rows.push({e,N:String(U),m:String(m),witness,factors:fac,order:3*e})
 }
 const equality=[];
 for(const e of [0,1,2,3,4,5]){
   const q=2**e,N=q*q+q+1,one=bgcd(bitpoly([0,q,q+1]),bitpoly([0,N])),other=bgcd(bitpoly([0,q*q,q*q+1]),bitpoly([0,N]));
   ok(one===bitpoly([0,q,q+1])&&other===bitpoly([0,1,q+1]),"sharp polynomials");
   equality.push({e,N,m:degree(one)})
 }
 const k2=[];
 for(const [n,i,j,m] of [[5,1,3,4],[17,6,10,8],[31,2,24,10],[73,0,9,9],[89,3,72,11],[127,1,56,14],[151,5,50,15]]){
   const h=bitpoly([0,i,i+1,j,j+1]),g=bgcd(h,bitpoly([0,n]));
   ok(degree(g)===m,"two-edit gcd");
   k2.push({N:n,i,j,m})
 }
 function cap(n){let m=2;for(;m<n-1;m++){let t=BigInt(m+1),a=t*(t-1n),N=BigInt(n-1);if(a*(t-2n)>2n*N*BigInt(n-2)||a>=2n*N&&(a-N)*(a-2n*N)>(t-2n)*N*N)break}return m}
 const caps=[5,7,11,13,17,19,31,43,73,89,127,151,257].map(N=>({N,cap:cap(N)}));
 ok(caps[0].cap===4&&caps[4].cap===8&&caps.at(-1).cap===46,"integer caps");
 return {schema:"trr13c-independent-v1",status:"passed",baseTraceZero:traceZero,cofactorGcds:small,largePrimeCertificates:rows,equalityGcds:equality,k2Gcds:k2,integerCaps:caps};
}
console.log(JSON.stringify(independent(),null,2));
