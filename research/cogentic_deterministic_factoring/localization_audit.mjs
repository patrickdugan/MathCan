function audit(){
 const ck=(v,s)=>{if(!v)throw Error(s)};
 const abs=a=>a<0n?-a:a;
 const mod=(a,n)=>((a%n)+n)%n;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 function inv(a,n){let b=n,x=0n,y=1n;a=mod(a,n);while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}ck(b===1n,"inverse");return mod(x,n)}
 function pow(a,e,n){ck(e>=0n,"exponent");let x=1n;for(a=mod(a,n);e;e>>=1n,a=a*a%n)if(e&1n)x=x*a%n;return x}
 const sign=(a,n)=>a===1n||a===n-1n;
 function signedOrder(a,n){let e=1n,x=mod(a,n);while(!sign(x,n)){x=x*a%n;e++;ck(e<n,"order")}return e}
 function trim(a){a=a.slice();while(a.length>1&&a[a.length-1]===0n)a.pop();return a.length?a:[0n]}
 function add(a,b){return trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||0n)+(b[i]||0n)))}
 function neg(a){return a.map(x=>-x)}
 function sub(a,b){return add(a,neg(b))}
 function mul(a,b){let c=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];return trim(c)}
 function eq(a,b){return trim(a).join(",")===trim(b).join(",")}
 function evalp(a,m,N=0n){let x=0n;for(let i=a.length-1;i>=0;i--){x=x*m+a[i];if(N)x=mod(x,N)}return x}
 const invalid=reason=>({status:"invalid",reason});
 function unit(x,N,role){const g=gcd(x,N);return g===1n?null:g<N?{status:"factor",factor:g,role}:{status:"unresolved",reason:"zero modular denominator",role}}
 function transport(N,m,t){
  if(N<=2n)return invalid("modulus");
  if(trim(t.f).length<2||evalp(t.f,m,N)!==0n)return invalid("root");
  if(eq(t.h,[0n])||eq(t.b,[0n])||eq(t.d,[0n]))return invalid("zero polynomial denominator");
  if(!eq(mul(t.h,sub(mul(t.a,t.d),mul(t.b,t.c))),mul(t.f,t.q)))return invalid("integer identity");
  for(const name of ["b","d","h"]){const fail=unit(evalp(t[name],m,N),N,name);if(fail)return fail}
  const x=evalp(t.a,m,N)*inv(evalp(t.b,m,N),N)%N,y=evalp(t.c,m,N)*inv(evalp(t.d,m,N),N)%N;
  if(x!==y)return invalid("transport mismatch");
  return {status:"verified",value:x}
 }
 function verifyPair(N,m,ell,E,s1,s2,t1,t2){
  if(N<=2n||ell<=1n||E<=0n||![1n,-1n].includes(s1)||![1n,-1n].includes(s2))return invalid("pair domain");
  const u=unit(ell,N,"ell");if(u)return u;
  const p1=transport(N,m,t1);if(p1.status!=="verified")return p1;
  const p2=transport(N,m,t2);if(p2.status!=="verified")return p2;
  if(pow(ell,E,N)*p1.value%N!==mod(s1,N)||p2.value!==mod(s2,N))return invalid("signed relations");
  if(p1.value!==p2.value)return invalid("common evaluation");
  if(pow(ell,2n*E,N)!==1n)return invalid("final congruence");
  return {status:"verified",exponent:2n*E,value:p1.value}
 }
 function makeUnitPolynomial(N,m,a,b){let p=[a,b];while(gcd(evalp(p,m,N),N)!==1n)p[0]++;return trim(p)}
 function lift(f,c,d,k,R,S,h){
  return {f,c,d,h,a:add(mul(k,c),mul(f,R)),b:add(mul(k,d),mul(f,S)),q:mul(h,sub(mul(R,d),mul(S,c)))}
 }
 function quadratic(N,m,a,b,offset){
  let v=a*m*m+b*m, k=(v+abs(b)*abs(b)+a+N)/N+1n+offset;
  const f=[k*N-v,b,a];ck(f[0]>0n&&b*b-4n*a*f[0]<0n&&evalp(f,m,N)===0n,"quadratic fixture");return f
 }
 const R={schema:"MATHCAN-DETFACT-AUDIT-05",moduli:[15,21,33,35,45,55,65,77,91,105,143,221],generic_transport_fixtures:0,two_field_pairs:0,verified_field_identities:0,annihilation_checks:0,nonmonic_field_checks:0,bezout_inverse_checks:0,negative_controls:0,recovered_factor_controls:0,unresolved_controls:0,largest_explicit_exponent_bits:0};
 let fixture;
 for(const nn of R.moduli){
  const N=BigInt(nn),us=Array.from({length:nn-2},(_,i)=>BigInt(i+2)).filter(a=>gcd(a,N)===1n);
  for(const m of [0n,1n,2n,4n,8n,13n]){
   for(const a of [1n,2n,3n,5n]){
    const f=quadratic(N,m,a,1n,0n),g=quadratic(N,m,a+1n,-1n,1n);
    const k=makeUnitPolynomial(N,m,2n,a),h=makeUnitPolynomial(N,m,3n,-1n),h2=makeUnitPolynomial(N,m,4n,2n),d=makeUnitPolynomial(N,m,7n,3n),c=[m-3n,2n,-1n],r=[-2n,1n],s=[3n,-1n,2n];
    const t=lift(f,c,d,k,r,s,h);
    const v=transport(N,m,t);
    ck(v.status==="verified"&&v.value===evalp(c,m,N)*inv(evalp(d,m,N),N)%N,"generic");
    R.generic_transport_fixtures++;R.verified_field_identities++;if(a!==1n)R.nonmonic_field_checks++;
    const ell=us[(Number(m)+Number(a))%us.length];
    const E=signedOrder(ell,N),L=ell**E,sg=mod(L,N)===1n?1n:-1n;
    const p1=lift(f,[sg],[L],k,r,s,h),p2=lift(g,[1n],[1n],k,s,r,h2);
    const p=verifyPair(N,m,ell,E,sg,1n,p1,p2);
    ck(p.status==="verified"&&p.exponent===2n*E&&pow(ell,p.exponent,N)===1n,"pair");
    R.two_field_pairs++;R.verified_field_identities+=2;R.annihilation_checks++;R.nonmonic_field_checks+=a===1n?1:2;
    R.largest_explicit_exponent_bits=Math.max(R.largest_explicit_exponent_bits,L.toString(2).length);
    fixture={N,m,ell,E,sg,p1,p2,f,k,r,s,h};
    // An explicit Bezout witness: X*(aX+b)-f = -f(0).
    // This checks both the polynomial certificate and the modular inverse when f(0) is a unit.
    const b0=f[1],c0=f[0],A=[b0,a],B=[-1n],X=[0n,1n];
    ck(eq(add(mul(A,X),mul(B,f)),[-c0]),"Bezout identity");
    if(gcd(c0,N)===1n){ck(mod(m*evalp(A,m,N)*inv(-c0,N),N)===1n,"Bezout inverse");R.bezout_inverse_checks++}
   }
  }
 }
 function expect(result,status,reason){ck(result.status===status,"wanted "+status+" got "+JSON.stringify(result,(_,x)=>typeof x==="bigint"?x.toString():x));if(reason)ck(result.reason===reason,"wrong reason");R.negative_controls++;if(status==="factor"){ck(result.factor>1n,"factor lower");R.recovered_factor_controls++}if(status==="unresolved")R.unresolved_controls++}
 const {N,m,ell,E,sg,p1,p2,f,k,r,s,h}=fixture;
 expect(transport(N,m,{...p1,q:add(p1.q,[1n])}),"invalid","integer identity");
 expect(transport(N,m,{...p1,f:add(p1.f,[1n])}),"invalid","root");
 expect(transport(N,m,{...p1,h:[0n]}),"invalid","zero polynomial denominator");
 expect(verifyPair(N,m,ell,E,2n,1n,p1,p2),"invalid","pair domain");
 expect(verifyPair(N,m,ell,E+1n,sg,1n,p1,p2),"invalid","signed relations");
 // Both field identities can be valid but their common nuisance values differ.
 const wrong=lift(p2.f,[-1n],[1n],k,r,s,h);
 ck(transport(N,m,wrong).status==="verified","wrong independent identity valid");
 expect(verifyPair(N,m,ell,E,sg,-1n,p1,wrong),"invalid","common evaluation");
 for(const d0 of [3n,15n]){
  const T={f:[14n,1n],a:[d0],b:[d0],c:[1n],d:[1n],h:[1n],q:[0n]};
  const u=transport(15n,1n,T);expect(u,d0===3n?"factor":"unresolved");if(d0===3n)ck(u.factor===3n,"factor exact")
 }
 // A nonunit clearing multiplier can mask a false modular equality.
 const masked={f:[12n,3n],a:[4n,1n],b:[1n],c:[0n],d:[1n],h:[3n],q:[1n]};
 const v=transport(15n,1n,masked);expect(v,"factor");ck(v.factor===3n&&evalp(masked.a,1n,15n)===5n,"masked");
 expect(verifyPair(15n,1n,3n,1n,1n,1n,masked,masked),"factor");
 // A norm -1 algebraic unit need not map to a global sign or order-two element.
 const unitPoly=[-1n,-1n,1n];
 ck(eq(sub(mul([0n,1n],[-1n,1n]),[1n]),unitPoly)&&evalp(unitPoly,8n,55n)===0n&&gcd(8n,55n)===1n&&pow(8n,2n,55n)===9n,"norm unit control");
 R.negative_controls++;
 return R
}

console.log(JSON.stringify(audit(),null,2));
