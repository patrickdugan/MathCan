function audit(){
 const ck=(v,s)=>{if(!v)throw Error(s)};
 const abs=x=>x<0n?-x:x;
 const mod=(a,n)=>((a%n)+n)%n;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 function inv(a,n){let b=n,x=0n,y=1n;a=mod(a,n);while(a){let q=b/a;[b,a]=[a,b%a];[x,y]=[y,x-q*y]}ck(b===1n,"nonunit");return mod(x,n)}
 function pow(a,e,n){if(e<0n){a=inv(a,n);e=-e}let r=1n;for(a=mod(a,n);e;e>>=1n,a=a*a%n)if(e&1n)r=r*a%n;return r}
 function sign(a,n){return a===1n||a===n-1n}
 function sorder(a,n){ck(gcd(a,n)===1n,"unit");let e=1n,x=mod(a,n);while(!sign(x,n)){x=x*a%n;e++;ck(e<n,"order")}return e}
 const minor=(A,i,j)=>A.filter((_,k)=>k!==i).map(r=>r.filter((_,k)=>k!==j));
 function det(A){const n=A.length;if(n===0)return 1n;if(n===1)return A[0][0];let s=0n;for(let j=0;j<n;j++)s+=(j%2?-1n:1n)*A[0][j]*det(minor(A,0,j));return s}
 function bareiss(A){const n=A.length;if(!n)return 1n;const M=A.map(r=>r.slice());let d=1n,sgn=1n;for(let k=0;k<n-1;k++){let i=k;while(i<n&&M[i][k]===0n)i++;if(i===n)return 0n;if(i!==k){[M[i],M[k]]=[M[k],M[i]];sgn=-sgn}const p=M[k][k];for(let r=k+1;r<n;r++){for(let c=k+1;c<n;c++){let x=p*M[r][c]-M[r][k]*M[k][c];ck(x%d===0n,"Bareiss exact division");M[r][c]=x/d}M[r][k]=0n}d=p}return sgn*M[n-1][n-1]}
 function adj(A){return A.map((r,i)=>r.map((_,j)=>((i+j)%2?-1n:1n)*bareiss(minor(A,j,i))))}
 const mv=(A,x)=>A.map(r=>r.reduce((s,a,i)=>s+a*x[i],0n));
 const prod=(us,x,N)=>us.reduce((v,a,i)=>v*pow(a,x[i],N)%N,1n);
 function validate(A,us,N){ck(N>2n&&us.every(a=>gcd(a,N)===1n),"nonunit");ck(A.length===us.length&&A.every(r=>r.length===A.length),"shape");for(let j=0;j<A.length;j++)ck(sign(prod(us,A.map(r=>r[j]),N),N),"false relation")}
 function multcert(A,i){let D=bareiss(A);ck(D!==0n,"singular");let col=adj(A).map(r=>r[i]);let g=col.reduce(gcd,abs(D)),m=abs(D)/g,x=col.map(a=>a/g*(D<0n?-1n:1n));ck(mv(A,x).every((a,j)=>a===(i===j?m:0n)),"bad certificate");return {m,x,D}}
 function inLatticeCramer(A,i,m,D){return A.every((_,j)=>det(A.map((r,k)=>r.map((a,l)=>l===j?(i===k?m:0n):a)))%D===0n)}
 function primeFactors(a){let f=[];for(let q=2n;q*q<=a;q++)if(a%q===0n){f.push(q);while(a%q===0n)a/=q}if(a>1n)f.push(a);return f}
 let state=42;function rand(n){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%n}
 const R={schema:"MATHCAN-DETFACT-AUDIT-04",moduli:[15,21,33,35,45,55,65,77,91,105,143,221],dimension_range:[2,4],matrix_fixtures:0,determinant_replays:0,adjugate_identity_checks:0,target_certificates:0,cramer_membership_checks:0,prime_divisor_minimality_checks:0,strict_target_reductions:0,global_annihilation_checks:0,paired_bordered_checks:0,strict_bordered_reductions:0,zero_bordered_determinants:0,negative_controls:0,gcd_aggregation_checks:0,strict_gcd_reductions:0,max_determinant_bits:0};
 function inspect(A,us,N){
  validate(A,us,N);let D=bareiss(A);ck(D!==0n&&D===det(A),"determinant comparison");R.determinant_replays++;R.matrix_fixtures++;R.max_determinant_bits=Math.max(R.max_determinant_bits,abs(D).toString(2).length);
  let J=adj(A),n=A.length;
  for(let i=0;i<n;i++){ck(mv(A,J.map(r=>r[i])).every((a,j)=>a===(i===j?D:0n)),"adjugate");R.adjugate_identity_checks++}
  let ms=[];
  for(let i=0;i<n;i++){
   let {m,x}=multcert(A,i);ck(sign(prod(us,mv(A,x),N),N)&&pow(us[i],2n*m,N)===1n,"target annihilation");R.target_certificates++;R.global_annihilation_checks++;
   ck(inLatticeCramer(A,i,m,D),"Cramer membership");R.cramer_membership_checks++;
   for(const q of primeFactors(m)){ck(!inLatticeCramer(A,i,m/q,D),"not minimal");R.prime_divisor_minimality_checks++}
   if(m<abs(D))R.strict_target_reductions++;ms.push(m)
  }
  const k=n-1,B=A.slice(0,k).map(r=>r.slice(0,k)),u=A.slice(0,k).map(r=>r[k]),d=bareiss(B);
  if(d!==0n){
   let w=mv(adj(B),u).map(x=>-x);w.push(d);
   let z=mv(A,w);ck(z.slice(0,k).every(x=>x===0n)&&z[k]===D,"border identity");ck(pow(us[k],2n*abs(D),N)===1n,"border certificate");
   let g=w.reduce(gcd,0n);ck(g>0n&&abs(D)%g===0n,"border content");
   ck(ms[k]===abs(D)/g,"border primitive comparison");if(g>1n)R.strict_bordered_reductions++;
   R.paired_bordered_checks++;
  }
  return ms
 }
 for(const nn of R.moduli){
  const N=BigInt(nn),units=Array.from({length:nn-2},(_,i)=>BigInt(i+2)).filter(a=>gcd(a,N)===1n);
  for(let n=2;n<=4;n++)for(let s=0;s<16;s++){
   let us=Array.from({length:n},()=>units[rand(units.length)]),orders=us.map(a=>sorder(a,N));
   function gen(){
    let C=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?BigInt(1+rand(3)):i<j?BigInt(rand(7)-3):0n));
    for(let h=0;h<n;h++){let j=rand(n),k=(j+1+rand(n-1))%n,t=BigInt(rand(5)-2);for(let i=0;i<n;i++)C[i][j]+=t*C[i][k]}
    return C.map((r,i)=>r.map(a=>a*orders[i]))
   }
   const A=gen(),B=gen(),m1=inspect(A,us,N),m2=inspect(B,us,N);
   for(let i=0;i<n;i++){let m=gcd(m1[i],m2[i]);ck(sign(pow(us[i],m,N),N),"gcd aggregation");R.gcd_aggregation_checks++;if(m<m1[i]&&m<m2[i])R.strict_gcd_reductions++}
  }
 }
 // Border with nonsingular nuisance pivot but zero Schur complement.
 const singular=[[4n,8n],[0n,0n]];validate(singular,[2n,7n],15n);const w=[-8n,4n];ck(mv(singular,w).every(a=>a===0n),"zero border");R.zero_bordered_determinants++;
 // Rank deficiency permits an isolated target in the span.
 ck(mv(singular,[1n,0n]).join(",")==="4,0"&&pow(2n,4n,15n)===1n,"rank deficient target");R.negative_controls++;
 function rejects(fn,s){try{fn()}catch(e){ck(e.message===s,"wrong rejection "+e.message);R.negative_controls++;return}throw Error("bad accepted")}
 rejects(()=>validate([[1n,0n],[0n,1n]],[2n,7n],15n),"false relation");
 rejects(()=>validate([[4n,0n],[0n,4n]],[3n,7n],15n),"nonunit");
 rejects(()=>multcert(singular,1),"singular");
 ck(pow(4n,1n,15n)===4n&&pow(4n,2n,15n)===1n&&!sign(4n,15n),"local roots versus global signs");R.negative_controls++;
 // Proper gcd target order can be much smaller than a supplied lattice index.
 const big=[[24n,0n],[0n,24n]];validate(big,[2n,7n],15n);ck(multcert(big,0).m===24n&&sorder(2n,15n)===4n,"index not exact unit order");R.negative_controls++;
 return R
}

console.log(JSON.stringify(audit(),null,2));
