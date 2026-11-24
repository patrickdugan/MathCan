// QBTC-02: finite covering and independent verifier split probabilities.
function qbtc02(){
  const assert=(x,m)=>{if(!x)throw Error(m)};
  const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
  const frac=(a,b)=>{const g=gcd(a,b);return [String(a/g),String(b/g)]};
  const binom=(n,k)=>{let a=1n;for(let i=1;i<=k;i++)a=a*BigInt(n-i+1)/BigInt(i);return a};
  const majority=(u,v,t)=>{let a=0n;for(let i=(t+1)/2;i<=t;i++)a+=binom(t,i)*u**BigInt(i)*(v-u)**BigInt(t-i);return [a,v**BigInt(t)]};
  let low=0,high=0,gap=0,gapYes=0,coverChecks=0;
  // Finite Sipser-Lautemann covering analogue: two shifts on F2^3.
  // If density >=3/4 then E uncovered <=8/16<1; if <=1/4 then union <=4.
  for(let mask=0;mask<256;mask++){
    const S=Array.from({length:8},(_,i)=>i).filter(i=>mask&(1<<i));
    let yes=false;
    for(let a=0;a<8;a++)for(let b=0;b<8;b++){
      const C=new Set([...S.map(s=>s^a),...S.map(s=>s^b)]);
      if(C.size===8)yes=true;coverChecks++;
    }
    if(S.length<=2){low++;assert(!yes,"low cover")}
    else if(S.length>=6){high++;assert(yes,"high cover")}
    else{gap++;if(yes)gapYes++}
  }
  assert(low===37&&high===37&&gap===182&&coverChecks===16384,"cover census");
  const rows=[];let checks=0;
  for(const [u,v] of [[0n,1n],[1n,10n],[1n,3n],[1n,2n],[2n,3n],[9n,10n],[1n,1n]]){
    let last=null;
    for(const t of [1,3,5,9,17,33]){
      const [a,d]=majority(u,v,t);
      assert(0n<=a&&a<=d,"prob range");
      const [b,e]=majority(v-u,v,t);
      assert(a*e+b*d===d*e,"majority complement");
      if(last){
        const [pa,pd]=last;
        assert(2n*u<v?a*pd<=pa*d:2n*u>v?a*pd>=pa*d:a*pd===pa*d,"majority monotonicity");
      }
      if(2n*u===v)assert(2n*a===d,"boundary");
      last=[a,d];
      let prev=null;
      for(const N of [2,5,10]){
        const D=d**BigInt(N),split=D-a**BigInt(N)-(d-a)**BigInt(N);
        assert(0n<=split&&split<=D,"split range");
        if(N===2)assert(split===2n*a*(d-a),"pair formula");
        if(prev)assert(split*prev[1]>=prev[0]*D,"split increases with node count");
        if(2n*u===v)assert(split*2n**BigInt(N)===(2n**BigInt(N)-2n)*D,"boundary exact");
        if(u===0n||u===v)assert(split===0n,"deterministic");
        if(N===10&&t===33&&u===1n&&v===2n)assert(split*512n===511n*D,"boundary ten");
        prev=[split,D];
        rows.push({p:frac(u,v),repetitions:t,nodes:N,accept:frac(a,d),split:frac(split,D),splitDisplay:Number(split)/Number(D)});
        checks++;
      }
    }
  }
  assert(checks===126,"frozen consensus count");
  return {schema:"qbtc-02-v1",cover:{sets:256,shiftPairChecks:coverChecks,low,high,gap,gapYes},consensus:{cases:checks,rows}};
}
console.log(JSON.stringify(qbtc02(),null,2));
