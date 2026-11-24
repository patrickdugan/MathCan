// QBTC-03: toy one-time authorization and exact amplification budget.
function qbtc03(){
 const ck=(p,m)=>{if(!p)throw Error(m)};
 const n=3,L=4,P=7,mod=1<<(6*n);
 // A tiny public injective fixture. Not a quantum oracle or one-way function.
 const F=(pk,x)=>((pk*313+17*x+29)%mod);
 const bits=x=>Array.from({length:L},(_,i)=>(x>>(L-1-i))&1);
 const sk=Array.from({length:L},(_,i)=>[2*i,2*i+1]);
 const vk=sk.map(pair=>pair.map(x=>F(P,x)));
 const sign=m=>bits(m).map((b,i)=>sk[i][b]);
 const verify=(m,s)=>Number.isInteger(m)&&m>=0&&m<(1<<L)&&Array.isArray(s)&&s.length===L&&s.every(x=>Number.isInteger(x)&&x>=0&&x<(1<<n))&&bits(m).every((b,i)=>F(P,s[i])===vk[i][b]);
 let honest=0,substitutions=0,mutations=0,malformed=0,reuse=0,hybrids=0;
 for(let a=0;a<(1<<L);a++){
  const s=sign(a);ck(verify(a,s),"honest");honest++;
  for(let b=0;b<(1<<L);b++)if(a!==b){ck(!verify(b,s),"substitution");substitutions++}
  for(let i=0;i<L;i++)for(let x=0;x<(1<<n);x++)if(x!==s[i]){
    const v=s.slice();v[i]=x;ck(!verify(a,v),"mutated witness");mutations++;
  }
  for(const v of [s.slice(1),[...s,0],s.map((x,i)=>i===0?-1:x),s.map((x,i)=>i===0?8:x)]){
    ck(!verify(a,v),"malformed");malformed++;
  }
  for(let b=0;b<(1<<L);b++)if(a!==b){
    const t=sign(b),h=bits(a^b).reduce((x,y)=>x+y,0);let count=0;
    for(let c=0;c<(1<<L);c++){
      const bs=bits(c);const w=bs.map((bit,i)=>bits(a)[i]===bit?s[i]:bits(b)[i]===bit?t[i]:null);
      if(w.every(x=>x!==null)){ck(verify(c,w),"reuse hybrid");count++;if(c!==a&&c!==b)hybrids++}
    }
    ck(count===2**h,"hybrid count");reuse++;
  }
 }
 ck(honest===16&&substitutions===240&&mutations===448&&malformed===64&&reuse===240&&hybrids===800,"frozen counts");
 // q_t = Pr[Bin(t,2/3)<=t/2] with strict-majority decoding of the entire output.
 // Exact recurrence q_(t+2)=q_t - C(t,(t-1)/2) (2/3)^((t+1)/2) (1/3)^((t+3)/2)
 // For reliability use direct binomial integer sum to verify minimality for each budget.
 function tail(t){
  let c=1n,sum=0n;
  for(let i=0;i<=(t-1)/2;i++){sum+=c*(2n**BigInt(i));c=c*BigInt(t-i)/BigInt(i+1)}
  return [sum,3n**BigInt(t)]
 }
 const budgets=[];
 for(const width of [256,1024,8192])for(const [validators,checks] of [[1,1],[1000,1000000],[10000,1000000000]])for(const b of [64,128]){
   const factor=BigInt(width)*BigInt(validators)*BigInt(checks)*2n**BigInt(b);
   const passes=t=>{const [u,v]=tail(t);return u*factor<=v};
   let lo=0,hi=1;while(!passes(2*hi+1))hi*=2;
   while(lo<hi){const mid=Math.floor((lo+hi)/2);if(passes(2*mid+1))hi=mid;else lo=mid+1}
   const t=2*lo+1;ck(passes(t)&&(t===1||!passes(t-2)),"minimal exact majority");
   const [u,v]=tail(t);
   budgets.push({width,validators,checks,b,repetitions:t,evalCalls:width*t,tailNum:String(u),tailDen:String(v)})
 }
 ck(budgets.length===18,"budget count");
 const sizes=[];
 for(const lambda of [128,256])for(const width of [256,1024,8192]){
   const pkBits=3*lambda+2*width*6*lambda,sigBits=width*lambda,skBits=2*width*lambda;
   ck(pkBits%8===0&&sigBits%8===0&&skBits%8===0,"byte align");
   sizes.push({n:lambda,messageBits:width,pkBytes:pkBits/8,signatureBytes:sigBits/8,secretBytes:skBits/8})
 }
 return {schema:"qbtc-03-v1",fixture:{honest,substitutions,mutations,malformed,reuse,hybrids},budgetCases:budgets.length,budgets,sizes};
}
console.log(JSON.stringify(qbtc03(),null,2));
