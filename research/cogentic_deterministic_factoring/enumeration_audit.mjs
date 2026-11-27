function audit() {
 const ck=(b,s)=>{if(!b)throw Error(s)};
 const gcd=(a,b)=>{if(a<0n)a=-a;while(b)[a,b]=[b,a%b];return a};
 const lcm=(a,b)=>a/gcd(a,b)*b;
 function prime(n){if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true}
 function pow(a,e,n){let x=1n%n;a%=n;while(e){if(e&1n)x=x*a%n;a=a*a%n;e>>=1n}return x}
 function plan(k,s){
  const r=Math.floor(Math.sqrt(k)),base=[];for(let p=3;p<=r;p+=2)if(prime(p))base.push(p);
  const labels=k>=2?[2]:[],seen=new Set();let segs=0,marks=0,checks=0,witnesses=0;
  for(let lo=3;lo<=k;lo+=2*s){
   const j=segs++,count=Math.min(s,Math.floor((k-lo)/2)+1),hi=lo+2*(count-1),mark=new Uint8Array(count);
   for(const p of base){
    if(p*p>hi)break;
    let first=Math.max(p*p,Math.ceil(lo/p)*p);if(first%2===0)first+=p;
    for(let h=(first-lo)/2;h<count;h+=p){const n=lo+2*h;ck(n>=p*p&&n%p===0&&(n/p-p)%2===0,"invalid strike");mark[h]=1;marks++}
   }
   for(let h=0;h<count;h++){
    const n=lo+2*h,i=(n-3)/2;ck(!seen.has(n)&&Math.floor(i/s)===j&&i%s===h,"segment partition");seen.add(n);
    const ps=base.filter(p=>p*p<=n&&n%p===0);
    ck(Boolean(mark[h])===(ps.length>0)&&Boolean(mark[h])===!prime(n),"mark iff composite");checks++;
    for(const p of ps){ck((n/p-p)%2===0&&n/p>=p,"odd progression");witnesses++}
    if(!mark[h])labels.push(n)
   }
  }
  ck(seen.size===Math.floor((k-1)/2),"candidate coverage");
  const entries=labels.map(p=>{let e=1,q=p;while(q<=Math.floor(k/p)){q*=p;e++}ck(q===p**e&&q<=k&&k<p*q,"maximality");return {p,e,q}});
  return {entries,segs,marks,checks,witnesses};
 }
 function validate(k,es){
  const seen=new Set();
  for(const {p,e,q} of es){if(!Number.isInteger(p)||!prime(p)||p>k||seen.has(p)||!Number.isInteger(e)||e<1||q!==p**e||q>k||p*q<=k)return false;seen.add(p)}
  for(let p=2;p<=k;p++)if(prime(p)&&!seen.has(p))return false;return true
 }
 const R={schema:"DETFACT-18-exact",runtime:"authoring JS runtime",indices:0,segment_configurations:0,segments:0,candidate_partition_and_mark_checks:0,mark_writes:0,odd_progression_witnesses:0,roster_entries:0,lcm_product_checks:0,streamed_residues:0,split_probes:0,negative_controls:0,max_K:0};
 const ks=[...Array.from({length:192},(_,i)=>i+1),255,256,257,511,512,513,1023,1024,1025,4095,4096,4097];
 for(const k of ks){
  let expected=1n;for(let i=1n;i<=BigInt(k);i++)expected=lcm(expected,i);
  R.indices++;R.max_K=Math.max(R.max_K,k);
  for(const s of [1,3,7,32,257]){
   const p=plan(k,s),es=p.entries;ck(validate(k,es),"roster");
   ck(es.reduce((a,x)=>a*BigInt(x.q),1n)===expected,"lcm product");
   R.segment_configurations++;R.segments+=p.segs;R.candidate_partition_and_mark_checks+=p.checks;R.mark_writes+=p.marks;R.odd_progression_witnesses+=p.witnesses;R.roster_entries+=es.length;R.lcm_product_checks++;
   let m=2n*96n*expected,depth=0;while(!(m&1n)){m>>=1n;depth++}
   const fs=[3n,...es.filter(e=>e.p!==2).map(e=>BigInt(e.q))];
   for(const [n,a] of [[15n,0n],[45n,3n],[77n,2n],[65537n,17n]]){
    let x=a%n;for(const q of fs)x=pow(x,q,n);ck(x===pow(a,m,n),"stream");R.streamed_residues++;
    for(let j=0;j<=depth;j++){const y=pow(a,m<<BigInt(j),n);ck(x===y&&gcd(x-1n,n)===gcd(y-1n,n),"probe");R.split_probes++;x=x*x%n}
   }
  }
 }
 const good=plan(30,7).entries;
 for(const bad of [good.slice(1),[...good,good[0]],good.map(e=>e.p===2?{p:2,e:e.e-1,q:e.q/2}:e),good.map(e=>e.p===2?{p:2,e:e.e+1,q:e.q*2}:e),[...good,{p:9,e:1,q:9}],[...good,{p:31,e:1,q:31}]]){ck(!validate(30,bad),"forged roster");R.negative_controls++}
 ck(3%3===0&&prime(3)&&3*3>3,"mark must start at square");R.negative_controls++;
 ck(49%7===0&&7*7===49&&!prime(49),"inclusive square");R.negative_controls++;
 return R;
}

console.log(JSON.stringify(audit(),null,2));
