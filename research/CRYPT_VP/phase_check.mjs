// QOBS-02: exact integer phase-state regression. No floating-point comparisons.
function runQobs(){
  const check=(b,m)=>{if(!b)throw Error(m)};
  const parity=x=>{let p=0;while(x){p^=1;x&=x-1}return p};
  function rank(x,n){let span=new Set([0]);for(let j=0;j<n;j++){let row=(x>>(j*n))&((1<<n)-1);for(const v of [...span])span.add(v^row)}return Math.log2(span.size)}
  function xorConv(a,b){const c=new Map();for(const [x,u] of a)for(const [y,v] of b)c.set(x^y,(c.get(x^y)||0n)+u*v);return c}
  const rows=[];let spectralChecks=0,comparisonChecks=0;
  for(let n=1;n<=3;n++){
    const N=1<<(n*n),all=Array.from({length:N},(_,x)=>x),ranks=all.map(x=>rank(x,n)),one=all.filter(x=>ranks[x]===1),full=all.filter(x=>ranks[x]===n);
    check(one.length===(2**n-1)**2,"rank-one count");let count=1;for(let j=0;j<n;j++)count*=2**n-2**j;check(full.length===count,"GL count");
    const sets=[one,full],q=2n**BigInt(n);
    const odd=sets.map(S=>all.map(b=>BigInt(S.filter(a=>parity(a&b)).length)));
    const families=[["constant",[0,0],[1,3]],["rank-one",[0,1],[1,1]],["common-row",Array.from({length:1<<n},(_,x)=>x),Array.from({length:1<<n},(_,x)=>x+1)],["duplicate",[0,0,1,1],[1,2,3,4]]];
    if(n>=2)families.push(["rank-two",[0,1+(1<<(n+1))],[1,1]],["mixed",[0,1,1<<(n+1),1+(1<<(n+1))],[1,2,3,4]]);
    if(n===3)families.push(["rank-three",[0,1+16+256],[2,3]],["distributed",[0,1,16,256,273,42],[1,2,3,4,5,6]]);
    for(const [name,B,w] of families){
      const weights=new Map();let W=0n;for(let i=0;i<B.length;i++){const wi=BigInt(w[i]);W+=wi;weights.set(B[i],(weights.get(B[i])||0n)+wi)}
      let copy=new Map([[0,1n]]),prev=null;
      for(let k=1;k<=4;k++){
        copy=xorConv(copy,weights);const spectrum=xorConv(copy,copy),den=W**BigInt(2*k);check([...spectrum.values()].reduce((a,b)=>a+b,0n)===den,"spectral mass");
        const E=sets.map((S,r)=>{
          const direct=S.reduce((sum,A)=>{let overlap=0n;for(let i=0;i<B.length;i++)overlap+=BigInt(w[i])*(parity(A&B[i])?-1n:1n);return sum+2n*(den-overlap**BigInt(2*k))},0n);
          const spectral=[...spectrum].reduce((sum,[b,m])=>sum+4n*m*odd[r][b],0n);
          check(direct===spectral,`${n}/${name}/${k}/spectral`);spectralChecks++;return {num:direct,den:den*BigInt(S.length)};
        });
        const high=[...spectrum].reduce((sum,[b,m])=>sum+(ranks[b]>=2?4n*m*odd[0][b]:0n),0n);
        const [a,b]=E,c=2n*(q-1n);
        check(b.num*a.den*q<=c*a.num*b.den,"sharp bound");
        check(3n*b.num*a.den*q+c*high*b.den<=3n*c*a.num*b.den,"defect");
        if(name==="constant")check(a.num===0n&&b.num===0n,"constant");
        if(["rank-one","common-row","duplicate"].includes(name))check(a.num>0n&&b.num*a.den*q===c*a.num*b.den,"saturation");
        if(["rank-two","rank-three","mixed","distributed"].includes(name))check(high>0n&&b.num*a.den*q<c*a.num*b.den,"strict higher rank");
        if(prev)for(let r=0;r<2;r++){check(E[r].num*prev[r].den>=prev[r].num*E[r].den,"copy monotonicity")}
        const single=k===1?E:rows[rows.length-k+1].raw.map(([num,den])=>({num:BigInt(num),den:BigInt(den)}));
        for(let r=0;r<2;r++)check(E[r].num*single[r].den<=BigInt(k)*single[r].num*E[r].den,"copy linear bound");
        comparisonChecks++;
        rows.push({n,family:name,k,raw:E.map(e=>[String(e.num),String(e.den)]),ratio:a.num?Number(b.num*a.den)/Number(b.den*a.num):null,highFraction:a.num?Number(high)/Number(a.num):null});prev=E;
      }
    }
  }
  check(rows.length===72,"frozen case count");check(spectralChecks===144,"frozen spectral check count");
  return {schema:"qobs-02-v1",cases:rows.length,spectralChecks,comparisonChecks,rows};
}
console.log(JSON.stringify(runQobs(),null,2));
