function audit() {
  const check = (condition, detail) => { if (!condition) throw new Error(detail); };
  const gcd = (a,b) => { if(a<0n) a=-a; while(b!==0n) [a,b]=[b,a%b]; return a; };
  const lcm = (a,b) => a/gcd(a,b)*b;
  const pow = (a,e,n) => { let r=1n; for(a%=n;e>0n;e>>=1n,a=a*a%n) if(e&1n) r=r*a%n; return r; };
  const v2 = a => { check(a>0n,"v2 domain"); let k=0; while(!(a&1n)){a>>=1n;k++;}return k; };
  function primesOf(n) {
    const out=[];
    for(let d=2n;d*d<=n;d++) if(n%d===0n){let e=0;while(n%d===0n){n/=d;e++;}out.push([d,e]);}
    if(n>1n) out.push([n,1]); return out;
  }
  function generators(n) {
    // Toy oracle: enumerate units and greedily enlarge the generated subgroup.
    // This costs at least linear work in n and supplies no asymptotic claim.
    const g=[], group=new Set([1n]); let units=0;
    for(let a=1n;a<n;a++){
      if(gcd(a,n)!==1n) continue; units++;
      if(group.has(a)) continue;
      g.push(a);
      const old=new Set(group);
      for(let b=a;!old.has(b);b=b*a%n)
        for(const x of old) group.add(x*b%n);
    }
    check(group.size===units,"generator closure");
    return g;
  }
  function signature(a,p) {
    let t=p-1n, s=v2(t), x=pow(a,t>>BigInt(s),p), j=0;
    while(x!==1n){x=x*x%p;j++;check(j<=s,"signature bound");}
    return j;
  }
  function split(n,m,gs) {
    check(n>1n&&m>=2n&&m%2n===0n,"split domain");
    const s=v2(m), u=m>>BigInt(s);
    for(const a of gs){
      const h=gcd(a,n); if(h>1n&&h<n)return h;
      if(h!==1n)continue;
      let x=pow(a,u,n);
      for(let j=0;j<=s;j++){
        const d=gcd(x-1n,n);
        if(d>1n&&d<n)return d;
        x=x*x%n;
      }
    }
    return null;
  }
  const r={schema:"MATHCAN-DETFACT-AUDIT-01",bound_inclusive:511,composites_with_distinct_primes:0,with_repeated_prime_factor:0,prime_pairs:0,equal_two_adic_ranks:0,unequal_two_adic_ranks:0,split_trials:0,prime_qnr_trials:0,negative_controls:0};
  for(let n=3n;n<=511n;n+=2n){
    const f=primesOf(n);
    if(f.length===1&&f[0][1]===1){
      const gs=generators(n);
      check(gs.some(a=>pow(a,(n-1n)/2n,n)===n-1n),"QNR generator lemma");
      r.prime_qnr_trials++;continue;
    }
    if(f.length<2)continue;
    r.composites_with_distinct_primes++;
    if(f.some(x=>x[1]>1))r.with_repeated_prime_factor++;
    const gs=generators(n), ps=f.map(x=>x[0]);
    let m=2n;
    for(const p of ps)m=lcm(m,p-1n);
    for(let i=0;i<ps.length;i++)for(let j=i+1;j<ps.length;j++){
      r.prime_pairs++;
      if(v2(ps[i]-1n)===v2(ps[j]-1n))r.equal_two_adic_ranks++;
      else r.unequal_two_adic_ranks++;
      check(gs.some(a=>signature(a,ps[i])!==signature(a,ps[j])),"pair separation");
    }
    for(const k of [1n,2n,3n,8n,15n]){
      const d=split(n,m*k,gs);
      check(d!==null&&d>1n&&d<n&&n%d===0n,"split failed");
      r.split_trials++;
    }
  }
  check(pow(4n,2n,15n)===1n && 2n%4n!==0n,"single-base false certificate");
  r.negative_controls++;
  check(split(15n,4n,[1n,14n])===null,"insufficient generator control");
  r.negative_controls++;
  check(split(15n,4n,[3n])===3n,"nonunit direct factor control");
  r.negative_controls++;
  return r;
}

console.log(JSON.stringify(audit(), null, 2));
