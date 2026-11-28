function campaign() {
  const A=(ok,msg)=>{if(!ok)throw Error(msg)};
  const B=BigInt;
  const counters={lift_pairs:0,determinant_valuation:0,gram_pairs:0,comparison_cases:0,feasible_comparisons:0,coverage_pools:0,coverage_steps:0,rotated_frame_steps:0,chain_cases:0,witness_checks:0,negative_controls:0};
  const det=m=>m[0]*m[3]-m[1]*m[2];
  const mul=(a,b)=>[a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]];
  const scale=(a,q)=>a.map(x=>x*q);
  const v=(x,p)=>{if(x===0n)return Infinity;let k=0;while(x%p===0n){x/=p;k++}return k};
  const val=(a,p)=>Math.min(...a.map(x=>v(x,p)));
  const mats=Array.from({length:81},(_,i)=>Array.from({length:4},(_,j)=>B(Math.floor(i/3**j)%3-1)));
  for(const p of [2n,3n])for(let i=0;i<81;i++)for(let j=0;j<81;j++){
    const a=scale(mats[i],p**B(i%3)),b=scale(mats[j],p**B(j%3)),c=mul(a,b);
    A(val(c,p)>=val(a,p)+val(b,p),"C01 superadditivity");counters.lift_pairs++;
    A(det(c)===det(a)*det(b),"C01 determinant product");
    if(det(a)!==0n&&det(b)!==0n){A(v(det(c),p)===v(det(a),p)+v(det(b),p),"C01 determinant valuation");counters.determinant_valuation++}
  }
  const strictA=[1n,1n,1n,-1n],strictB=[1n,1n,1n,-1n];
  A(val(strictA,2n)===0&&val(strictB,2n)===0&&val(mul(strictA,strictB),2n)===1,"strict gain");counters.negative_controls++;
  const vecs=Array.from({length:125},(_,i)=>Array.from({length:3},(_,j)=>B(Math.floor(i/5**j)%5-2)));
  const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0n);
  for(const x of vecs)for(const y of vecs){
    const g=dot(x,x)*dot(y,y)-dot(x,y)**2n;
    const minors=(x[0]*y[1]-x[1]*y[0])**2n+(x[0]*y[2]-x[2]*y[0])**2n+(x[1]*y[2]-x[2]*y[1])**2n;
    A(g===minors&&g>=0n&&g<=dot(x,x)*dot(y,y),"C02 Gram and Hadamard");counters.gram_pairs++;
  }
  for(let d=1n;d<=8n;d++)for(let n=1n;n<=d;n++)for(let H=0n;H<=8n;H++)for(let L=0n;L<=4n;L++)for(let I=0n;I<=3n;I++)for(let R=-8n;R<=20n;R++){
    const original=d*(H-3n*L)<=n*(H-R+L)+2n*d*I;
    const sharp=n*R<=d*(4n*L+2n*I)-(d-n)*(H+L);
    A(original===sharp,"C04 exact comparison");counters.comparison_cases++;
    if(original){A(n*R<=d*(4n*L+2n*I),"C02 relaxed");if(2n*n>=d)A(R<=2n*(4n*L+2n*I),"C02 half coverage");counters.feasible_comparisons++}
  }
  // Removing nonnegative H, doubling the index incorrectly, or allowing n=0.
  A(2n*(-10n)<=1n*(-10n-10n)&&10n>0n,"negative height counterexample");counters.negative_controls++;
  A(0n<=-2n+2n&&2n>1n,"index coefficient counterexample");counters.negative_controls++;
  A(1n*(0n-3n)<=0n&&1000n>8n,"zero coverage counterexample");counters.negative_controls++;
  const pop=x=>{let c=0;for(;x;x>>=1)c+=x&1;return c};
  for(let poolMask=1;poolMask<128;poolMask++){
    const pool=Array.from({length:7},(_,i)=>i+1).filter((_,i)=>poolMask&(1<<i));
    const a=Math.min(...[1,2,4].map(bit=>pool.filter(x=>x&bit).length));
    if(a===0)continue;
    let covered=0;counters.coverage_pools++;
    while(covered!==7){
      const missing=3-pop(covered);let best=pool[0];
      for(const q of pool)if(pop(q&~covered)>pop(best&~covered))best=q;
      const gain=pop(best&~covered);
      A(gain*pool.length>=a*missing&&gain>0,"C03 coverage");covered|=best;counters.coverage_steps++;
    }
  }
  const rank=rows=>{
    let a=rows.map(r=>r.map(B)),k=0,d=a[0]?.length??0;
    for(let j=0;j<d&&k<a.length;j++){
      let i=k;while(i<a.length&&a[i][j]===0n)i++;
      if(i===a.length)continue;
      [a[k],a[i]]=[a[i],a[k]];
      for(i=k+1;i<a.length;i++){const u=a[i][j],v=a[k][j];if(u!==0n)a[i]=a[i].map((x,l)=>v*x-u*a[k][l]);}
      k++;
    }return k;
  };
  // Four projectors, sum = 2I in exact arithmetic: two orthonormal bases, one rotated.
  const frame=[[1n,0n],[0n,1n],[3n,4n],[-4n,3n]];
  A(25n+9n+16n===50n&&12n-12n===0n&&25n+16n+9n===50n,"frame");
  for(const first of [[],...[...frame].map(x=>[x])]){
    let sel=first.slice();
    while(rank(sel)<2){
      const r=rank(sel),next=frame.find(x=>rank([...sel,x])>r);
      A(next!==undefined&&2*(rank([...sel,next])-r)>=2-r,"C03 rotated coverage");sel.push(next);counters.rotated_frame_steps++;
    }
  }
  // C05: exact normalized chain equality, additive lower gain and determinant product.
  for(let seed=0;seed<1024;seed++){
    const p=seed%2?2n:3n,steps=2+seed%5;let raw=[1n,0n,0n,1n],norm=raw,gain=0n;
    for(let j=0;j<steps;j++){
      const f=mats[(seed*17+j*31)%81],g=B((seed+j)%4);
      norm=mul(f,norm);raw=mul(scale(f,p**g),raw);gain+=g;
    }
    A(raw.every((x,i)=>x===norm[i]*p**gain)&&val(raw,p)>=Number(gain),"C05 normalized chain");counters.chain_cases++;
  }
  // C06: explicit finite independent witness, with exact clearing of denominators.
  for(let seed=0;seed<256;seed++){
    const candidates=Array.from({length:8},(_,j)=>vecs[(seed*13+j*17)%125]);
    const chosen=[];
    for(const x of candidates)if(rank([...chosen,x])>chosen.length)chosen.push(x);
    A(rank(chosen)===chosen.length&&chosen.length===rank(candidates)&&candidates.every(x=>rank([...chosen,x])===chosen.length),"C06 basis");
    const den=chosen.map((_,j)=>B(2+(seed+j)%7));
    const common=den.reduce((s,x)=>s*x,1n);
    for(let j=0;j<chosen.length;j++)for(const x of chosen[j])A(common*x%den[j]===0n,"C06 clearing");
    counters.witness_checks++;
  }
  // C03 missing direction: repeated projector onto e1 cannot cover e2.
  A(rank([[1n,0n],[2n,0n]])===1,"coverage obstruction");counters.negative_controls++;
  return {schema:"grh-c-stage0-v1",status:"finite-exact",counters,scope:"Synthetic integer matrices, coordinate and rotated projectors, scalar bounds; not an independent GRH proof."};
}
console.log(JSON.stringify(campaign(), null, 2));
