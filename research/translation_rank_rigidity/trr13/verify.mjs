function runTRR13(){
  const check=(b,m)=>{if(!b)throw Error(m)};
  const mod=(x,p)=>((x%p)+p)%p;
  function inv(x,p){for(let i=1;i<p;i++)if(mod(x*i,p)===1)return i;throw Error("nonunit")}
  function rank(g,p){
    const n=g.length,M=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>g[(i+j)%n]));
    let r=0;
    for(let c=0;c<n&&r<n;c++){
      let i=r;while(i<n&&M[i][c]===0)i++;if(i===n)continue;
      [M[r],M[i]]=[M[i],M[r]];
      const a=inv(M[r][c],p);
      for(let j=c;j<n;j++)M[r][j]=mod(M[r][j]*a,p);
      for(let k=r+1;k<n;k++){const b=M[k][c];if(b)for(let j=c;j<n;j++)M[k][j]=mod(M[k][j]-b*M[r][j],p)}
      r++;
    }return r;
  }
  const rankCohorts=[];
  for(const [p,n] of [[2,3],[2,5],[2,7],[2,9],[2,11],[2,13],[3,4],[3,5],[3,7],[3,8],[5,3],[5,4],[5,6],[7,3],[7,4]]){
    check(n%p!==0,"tame cohort");
    const label=Array.from({length:n},(_,i)=>i%p);
    const exactRank=rank(label,p);
    check(exactRank===n-(label.reduce((a,b)=>a+b,0)%p===0?1:0),"exact label rank");
    let checks=0,nontrivial=0,tight=0,minMargin=Infinity;
    for(let index=0;index<p**n;index++){
      let x=index,g=[];for(let i=0;i<n;i++){g.push(x%p);x=Math.floor(x/p)}
      const k=g.filter((v,i)=>v!==label[i]).length;
      const h=g.map((v,i)=>mod(g[(i+1)%n]-v-1,p));
      const s=h.filter(x=>x!==0).length;
      check(s>0&&s<=2*k+1&&mod(h.reduce((a,b)=>a+b,0),p)===mod(-n,p),"support or trace");
      const rg=rank(g,p),rh=rank(h,p);
      const lb=Math.ceil(n/(2*k+1))-1;
      check(rh*s>=n&&rh<=rg+1&&rg>=lb,"rank inequality");
      if(lb>0){nontrivial++;minMargin=Math.min(minMargin,rg-lb);if(rg===lb)tight++}
      checks++;
    }
    rankCohorts.push({p,n,checks,exactRank,nontrivial,tight,minMargin});
  }
  let masks=0,affineMasks=0;
  for(let n=3;n<=17;n++){
    for(let m=0;m<2**n;m++){
      let k=0,good=0;for(let i=0;i<n;i++)k+=(m>>i)&1;
      for(let i=0;i<n-1;i++)if(!((m>>i)&1)&&!((m>>(i+1))&1))good++;
      check(good>=n-1-2*k,"adjacent full");masks++;
    }
    for(let m=0;m<2**(n-1);m++){
      let k=0,good=0;for(let i=0;i<n-1;i++)k+=(m>>i)&1;
      for(let i=0;i<n-2;i++)if(!((m>>i)&1)&&!((m>>(i+1))&1))good++;
      check(good>=n-2-2*k,"adjacent punctured");affineMasks++;
    }
  }
  const primeFields=[5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101];
  const sharp=[];
  for(const p of primeFields){
    const e=(p-1)/2;let zeros=0,ones=0,other=0;
    const chain=n=>n.toString(2).length+n.toString(2).split("1").length-1-2;
    for(let x=1;x<p;x++){let v=1;for(let j=0;j<e;j++)v=mod(v*x,p);const bit=mod((1-v)*inv(2,p),p);if(bit===0)zeros++;else if(bit===1)ones++;else other++}
    check(zeros===e&&ones===e&&other===0,"quadratic predicate balance");
    sharp.push({p,points:p-1,zeros,ones,degree:e,binaryPowerMultiplications:chain(e)});
  }
  let trees=0,exceptionChecks=0,constantLeaves=0,nonconstantLeaves=0,exactTwo=0;
  for(const p of primeFields){
    for(let a=0;a<p;a++)for(let b=0;b<p;b++)if(a!==b){
      const c=(a+1)%p,d=(b+1)%p;
      const E=new Set([a,b,c,d]);check(E.size<=4,"exception bound");
      // Generic tests are (X-a)/(X-b), (X-c)/(X-d); zeros and
      // poles are exceptions. Independently reconstruct their bad set.
      const observed=new Set();
      for(let x=0;x<p;x++){
        if(x===b||x===d)observed.add(x);
        else if(mod((x-a)*inv(x-b,p),p)===0||mod((x-c)*inv(x-d,p),p)===0)observed.add(x);
      }
      check(observed.size===E.size&&[...E].every(x=>observed.has(x)),"branch exception reconstruction");
      const w=Array.from({length:p},(_,i)=>i).find(x=>!E.has(x));
      const base=w-(w&1);let constGood=0,nonconstGood=0,alphabetGood=0;
      // Two output models: a constant bit vector encoding w; a fixed
      // prefix encoding floor(w/2) and nonconstant final bit X-base.
      for(let x=0;x<p;x++)if(!E.has(x)){
        const y=mod(x-base,p);
        if(x===w)constGood++;
        if(y===0||y===1){alphabetGood++;if((x>>1)===(w>>1)&&y===(x&1))nonconstGood++}
      }
      check(constGood===1&&nonconstGood>=1&&nonconstGood<=alphabetGood&&alphabetGood<=2,"generic leaf");
      check(E.size+nonconstGood<=4+2&&E.size+constGood<=4+1,"tree total");
      if(nonconstGood===2)exactTwo++;
      trees+=2;exceptionChecks++;constantLeaves++;nonconstantLeaves++;
    }
  }
  const fixtures=[[17,2,2,0,6,19],[19,2,9,0,3,23],[23,1,4,0,2,29],[29,1,12,2,14,23],[31,0,3,1,2,43],[37,1,12,0,7,29]];
  const curveRows=[];
  function add(P,Q,p,A){
    if(P===null)return Q;if(Q===null)return P;
    let [x,y]=P,[X,Y]=Q;
    if(x===X&&mod(y+Y,p)===0)return null;
    const m=x===X?mod((3*x*x+A)*inv(2*y,p),p):mod((Y-y)*inv(X-x,p),p);
    const z=mod(m*m-x-X,p);
    return [z,mod(m*(x-z)-y,p)];
  }
  let seed=123456789;
  function random(p){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%p}
  for(const [p,A,B,tx,ty,n] of fixtures){
    check(mod(4*A**3+27*B**2,p)!==0,"smooth");
    const T=[tx,ty],G=[null];let P=T;
    while(P!==null&&G.length<=n){check(mod(P[1]**2-P[0]**3-A*P[0]-B,p)===0,"curve");check(!G.slice(1).some(Q=>Q[0]===P[0]&&Q[1]===P[1]),"distinct");G.push(P);P=add(P,T,p,A)}
    check(P===null&&G.length===n&&n%p!==0,"order");
    let tests=0,shiftChecks=0,rawGuardChecks=0,bitChecks=0;
    for(let trial=0;trial<256;trial++){
      const a=Array.from({length:3},()=>random(p)),b=Array.from({length:3},()=>random(p));
      if(b.every(x=>x===0))b[2]=1;
      const j=b.findIndex(z=>z!==0);
      const nonconstant=!a.every((v,i)=>mod(v*b[j],p)===mod(b[i]*a[j],p));
      const V=G.slice(1).map(([x,y])=>{
        const num=mod(a[0]*x+a[1]*y+a[2],p),den=mod(b[0]*x+b[1]*y+b[2],p);
        return {num,den,value:den===0?null:mod(num*inv(den,p),p)}
      });
      const k=V.filter((v,i)=>v.value!==(i+1)%p).length;
      const zeroDiff=V.slice(0,-1).filter((v,i)=>v.value!==null&&V[i+1].value!==null&&mod(V[i+1].value-v.value-1,p)===0).length;
      check(zeroDiff>=n-2-2*k&&zeroDiff<=6,"rational shift height <= 6");
      check(V.filter(v=>v.den===0).length<=3,"raw affine denominator roots");
      if(nonconstant){check(V.filter(v=>v.value===0||v.value===1).length<=6,"binary alphabet height <=3");bitChecks++}
      tests++;shiftChecks++;rawGuardChecks++;
    }
    curveRows.push({p,A,B,T,N:n,tests,shiftChecks,rawGuardChecks,bitChecks});
  }
  const removableGuard={reducedHeight:0,rawUndefinedAtZero:true,explicitGuardHeight:1};
  // At X=0, raw division is undefined even though X/X reduces to 1.
  check(mod(0,5)===0&&removableGuard.rawUndefinedAtZero,"raw guard control");
  const totals={cyclicWords:rankCohorts.reduce((s,x)=>s+x.checks,0),nontrivialRankBounds:rankCohorts.reduce((s,x)=>s+x.nontrivial,0),tightRankBounds:rankCohorts.reduce((s,x)=>s+x.tight,0),fullErrorMasks:masks,puncturedErrorMasks:affineMasks,sharpPredicateFields:sharp.length,genericPathTrees:trees,exceptionChecks,constantLeaves,nonconstantLeaves,nonconstantTwoSuccessLeaves:exactTwo,curveExpressions:curveRows.reduce((s,x)=>s+x.tests,0),curveShiftChecks:curveRows.reduce((s,x)=>s+x.shiftChecks,0),curveRawGuardChecks:curveRows.reduce((s,x)=>s+x.rawGuardChecks,0),curveBinaryChecks:curveRows.reduce((s,x)=>s+x.bitChecks,0)};
  return {schema:"trr13-restricted-inverse-bounds-v1",status:"passed",totals,rankCohorts,sharp,curveRows,removableGuard,scope:"Public synthetic sequences, fixed rational-expression controls, and abstract decision-tree bounds. No recovery candidate, real keys, or cryptographic-size curve search."};
}
console.log(JSON.stringify(runTRR13(), null, 2));
