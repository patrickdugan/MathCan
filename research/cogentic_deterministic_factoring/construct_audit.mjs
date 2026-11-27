function audit(){
 const ck=(x,s)=>{if(!x)throw Error(s)};
 function prime(n){if(n<2)return false;for(let d=2;d*d<=n;d++)if(n%d===0)return false;return true}
 function dense(R,n){for(let d=2;d<=R&&d*d<=n;d++)if(n%d===0)return true;return false}
 function bases(K){const R=Math.floor(Math.sqrt(K));let out=[];for(let n=3;n<=R;n+=2)if(!dense(R,n))out.push(n);return out}
 function native(p,lo){let f=Math.max(p*p,Math.floor((lo+p-1)/p)*p);if(f%2===0)f+=p;return f}
 function first(p,lo){let q=Math.max(p,Math.floor((lo+p-1)/p));q+=Number(q%2===0);return p*q}
 function maxExp(p,k){let e=0;while(p<=k){k=Math.floor(k/p);e++}return e}
 function grow(p,K){let e=1,q=p;while(q<=Math.floor(K/p)){q*=p;e++}return {e,q}}
 function gcd(a,b){while(b)[a,b]=[b,a%b];return a}
 const R={schema:"DETFACT-19-exact",execution:"authoring JS runtime",indices:0,base_candidates:0,base_rosters:0,first_strike_checks:0,offset_membership_checks:0,segment_configurations:0,maximal_power_checks:0,lcm_checks:0,negative_controls:0,max_K:0};
 const ks=[...Array.from({length:128},(_,i)=>i+1),255,256,257,511,512,513,1023,1024,1025,4095,4096,4097,65535,65536,65537];
 for(const K of ks){
  const r=Math.floor(Math.sqrt(K)),ps=bases(K),want=[];for(let p=3;p<=r;p+=2){if(prime(p))want.push(p);R.base_candidates++}
  ck(ps.join(",")===want.join(","),"base correctness");R.base_rosters++;R.indices++;R.max_K=Math.max(R.max_K,K);
  let M=1n;for(let i=1n;i<=BigInt(K);i++)M=M/gcd(M,i)*i;
  for(const S of K>4097?[32,257,8192]:[1,7,32,257]){
   const labels=K>=2?[2]:[];
   for(let lo=3;lo<=K;lo+=2*S){
    const count=Math.min(S,Math.floor((K-lo)/2)+1),hi=lo+2*(count-1),mark=new Uint8Array(count);
    for(const p of ps){
     if(p*p>hi)break;
     const f=native(p,lo),f2=first(p,lo),j=(f-lo)/2;
     ck(f===f2&&f>=lo&&f>=p*p&&f%p===0&&f%2===1,"first strike");ck(j>=0&&Number.isInteger(j),"offset");R.first_strike_checks++;
     for(let h=j;h<count;h+=p)mark[h]=1;
     // Check membership independently at all segment offsets on small inputs,
     // and at endpoints / strike boundaries on larger inputs.
     const offsets=K<=4097?Array.from({length:count},(_,i)=>i):[0,count-1,Math.max(0,j-1),j,j+p].filter(h=>h>=0&&h<count);
     for(const h of offsets){const n=lo+2*h,progress=h>=j&&(h-j)%p===0;ck(progress===(n>=p*p&&n%p===0),"offset iff");R.offset_membership_checks++}
    }
    for(let h=0;h<count;h++)if(!mark[h])labels.push(lo+2*h);
   }
   const expected=[];for(let p=2;p<=K;p++)if(prime(p))expected.push(p);ck(labels.join(",")===expected.join(","),"labels");
   let product=1n;
   for(const p of labels){const e=maxExp(p,K),q=BigInt(p)**BigInt(e),g=grow(p,K);ck(e===g.e&&q===BigInt(g.q)&&q<=BigInt(K)&&BigInt(K)<q*BigInt(p),"maximal power");R.maximal_power_checks++;product*=q}
   ck(product===M,"LCM");R.lcm_checks++;R.segment_configurations++
  }
 }
 ck(native(7,3)===49&&first(7,3)===49,"square guard");R.negative_controls++;
 ck(native(7,51)===63&&first(7,51)===63,"parity correction");R.negative_controls++;
 ck(native(7,63)===63&&first(7,63)===63,"inclusive lower edge");R.negative_controls++;
 ck(maxExp(2,65535)===15&&maxExp(2,65536)===16&&maxExp(2,65537)===16,"power edge");R.negative_controls++;
 ck(bases(48).includes(7)===false&&bases(49).includes(7)===true,"root boundary");R.negative_controls++;
 ck(maxExp(7,1)===0,"empty roster power domain");R.negative_controls++;
 return R
}

console.log(JSON.stringify(audit(),null,2));
