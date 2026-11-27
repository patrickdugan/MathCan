function audit(){
 const ck=(v,s)=>{if(!v)throw Error(s)},abs=x=>x<0n?-x:x;
 function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
 const lcm=(a,b)=>a/gcd(a,b)*b;
 function pow(a,e,N){let x=1n%N;a%=N;for(;e>0n;e>>=1n,a=a*a%N)if(e&1n)x=x*a%N;return x}
 function prime(p){if(p<2n)return false;for(let d=2n;d*d<=p;d++)if(p%d===0n)return false;return true}
 function roster(K){const es=[];for(let p=2n;p<=K;p++)if(prime(p)){let q=p,e=1;while(q<=K/p){q*=p;e++}es.push({p,e,q})}return es}
 function verify(K,es){
  const seen=new Set();for(const {p,e,q} of es){if(p>K||!prime(p)||!Number.isSafeInteger(e)||e<1||e>K.toString(2).length||q!==p**BigInt(e)||q>K||p*q<=K||seen.has(p))return false;seen.add(p)}
  for(let p=2n;p<=K;p++)if(prime(p)&&!seen.has(p))return false;return true
 }
 function split2(m){ck(m>0n,"positive exponent");let s=0;while(!(m&1n)){s++;m>>=1n}return {s,u:m}}
 function compose(K,m,es){ck(verify(K,es),"invalid roster");const {s,u}=split2(m);const e=es.find(r=>r.p===2n)?.e||0;const fs=[u,...es.filter(r=>r.p!==2n).map(r=>r.q)];return {s:1+s+e,fs,e}}
 function execute(a,N,fs){let x=a%N;for(const q of fs)x=pow(x,q,N);return x}
 function refLCM(K){let l=1n;for(let i=1n;i<=K;i++)l=lcm(l,i);return l}
 const Ks=[...Array.from({length:64},(_,i)=>i+1),127,128,129,255,256,257,1023,1024,1025,4095,4096,4097];
 const R={schema:"DETFACT-17-exact",execution:"authoring JS runtime",intervals:0,rosters:0,roster_entries:0,exponent_decompositions:0,valuation_checks:0,residue_checks:0,split_probe_checks:0,nonunit_base_cases:0,first_split_checks:0,negative_controls:0,max_K:0};
 for(const k of Ks){const K=BigInt(k),S=refLCM(K),es=roster(K);R.intervals++;R.max_K=Math.max(R.max_K,k);
  const variants=[es,es.slice().reverse(),es.filter((_,i)=>i%2===1).concat(es.filter((_,i)=>i%2===0))];
  for(const v of variants){ck(verify(K,v),"valid roster");R.rosters++;R.roster_entries+=v.length;
   for(const m of [1n,2n,15n,96n,(1n<<64n)+7n]){
    const C=compose(K,m,v),E=2n*m*S,ref=split2(E),u=C.fs.reduce((a,b)=>a*b,1n);
    ck(C.fs.every(q=>q>0n&&(q&1n)===1n),"odd stream");
    ck((1n<<BigInt(C.s))*u===E&&u===ref.u&&C.s===ref.s,"decomposition");R.exponent_decompositions++;
    ck((1n<<BigInt(C.e))<=K&&K<(1n<<BigInt(C.e+1)),"maximal two exponent");R.valuation_checks++;
    for(const N of [15n,45n,77n,65537n]){
     for(const a of [0n,1n,2n,3n,7n,N-1n,N]){
      let x=execute(a,N,C.fs);ck(x===pow(a,ref.u,N),"residue");R.residue_checks++;if(gcd(a,N)!==1n)R.nonunit_base_cases++;
      let first=null,firstRef=null;
      for(let j=0;j<=C.s;j++){
       const y=pow(a,ref.u<<BigInt(j),N),d=gcd(x-1n,N),d2=gcd(y-1n,N);
       ck(x===y&&d===d2,"split probe");R.split_probe_checks++;
       if(first===null&&d>1n&&d<N)first=j+":"+d;
       if(firstRef===null&&d2>1n&&d2<N)firstRef=j+":"+d2;
       x=x*x%N
      }
      ck(first===firstRef,"first split");R.first_split_checks++
     }
    }
   }
  }
 }
 const es=roster(30n);
 for(const bad of [es.slice(1),[...es,es[0]],es.map(e=>e.p===2n?{p:2n,e:e.e-1,q:e.q/2n}:e),es.map(e=>e.p===2n?{p:2n,e:e.e+1,q:e.q*2n}:e),[...es,{p:9n,e:1,q:9n}]]){ck(!verify(30n,bad),"forged roster");R.negative_controls++}
 try{compose(30n,0n,es);throw Error("zero accepted")}catch(e){ck(e.message==="positive exponent","zero input");R.negative_controls++}
 ck((2n**3n)*15n===(2n**2n)*30n&&(30n&1n)===0n,"oddness essential");R.negative_controls++;
 return R
}

console.log(JSON.stringify(audit(),null,2));
