/* VPVNP five-track exact finite regressions. Run: node research/VPVNP/five_track_check.mjs */
function runFive() {
  const check=(v,msg)=>{if(!v)throw Error(msg)};
  const fields=[2,3,5,7];
  const mod=(x,p)=>((x%p)+p)%p;
  const trim=a=>{while(a.length>1&&a[a.length-1]===0)a.pop();return a};
  const add=(a,b,p,sgn=1)=>trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>mod((a[i]||0)+sgn*(b[i]||0),p)));
  const mul=(a,b,p)=>{const c=Array(a.length+b.length-1).fill(0);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]=mod(c[i+j]+a[i]*b[j],p);return trim(c)};
  const eq=(a,b)=>a.length===b.length&&a.every((v,i)=>v===b[i]);
  let seed=20261124;const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n};
  const report={schema:"vpvnp-five-01",seed:20261124,scope:"finite exact regressions; no upstream theorem or open conjecture certified",AC:{},IPS:{},GEO:{},LOOP:{},CROSS:{}};
  // AC: toy idempotent commutative monoid (subsets of two elements, union).
  // Single-element covers are inclusions. Coordinates are restricted to {1,2,3}.
  const gauge=q=>[0,1,2,3].every(a=>[0,1,2,3].every(b=>q[a|b]<=q[a]*q[b]&&((a|b)!==b||q[a]<=q[b])));
  const keeps=(q,p0)=>[0,1,2,3].every(x=>[0,1,2,3].every(y=>{
    let n=0,d=1;for(let t=0;t<4;t++)if(p0[t|x]*d>n*p0[t|y]){n=p0[t|x];d=p0[t|y]}
    return [0,1,2,3].every(t=>q[t|x]*d<=n*q[t|y]);
  }));
  const gauges=[];for(let a=1;a<=3;a++)for(let b=1;b<=3;b++)for(let c=1;c<=3;c++){const q=[1,a,b,c];if(gauge(q))gauges.push(q)}
  let feasiblePairs=0;
  for(const p0 of gauges){
    const feasible=gauges.filter(q=>q.every((v,i)=>v<=p0[i])&&keeps(q,p0));
    feasiblePairs+=feasible.length;
    let lex=feasible;
    for(let i=0;i<4;i++){const best=Math.min(...lex.map(q=>q[i]));lex=lex.filter(q=>q[i]===best)}
    check(lex.length===1,"AC unique finite minimizer");
    const q=lex[0];
    check(!feasible.some(r=>r.some((v,i)=>v<q[i])&&r.every((v,i)=>v<=q[i])),"AC minimal");
    for(let a=0;a<4;a++)for(let b=0;b<4;b++)check(q[a|b]===q[a]*q[b],"AC finite multiplicativity");
  }
  report.AC={toy_gauges:gauges.length,feasible_pairs:feasiblePairs,minima_checked:gauges.length};
  // Generate DAGs with exact univariate x-polynomial leaves and y placeholders.
  function dag(p) {
    const g=[{op:"x"},{op:"y",i:0},{op:"y",i:1},{op:"y",i:2},{op:"c",v:rnd(p)},{op:"c",v:rnd(p)}];
    for(let i=0;i<14;i++)g.push({op:["a","s","m"][rnd(3)],a:rnd(g.length),b:rnd(g.length)});
    return g;
  }
  function evaluate(g,F,p,cert=false) {
    const v=[],z=[],d=[];
    for(let i=0;i<g.length;i++){
      const k=g[i];
      if(k.op==="x"||k.op==="c"||k.op==="y"){
        const a=k.op==="x"?[0,1]:k.op==="c"?[mod(k.v,p)]:F[k.i];
        v.push(a);z.push(k.op==="y"?[0]:a);
        d.push(F.map((_,j)=>[k.op==="y"&&k.i===j?1:0]));
      }else{
        const {a,b}=k;
        if(k.op==="m"){
          v.push(mul(v[a],v[b],p));z.push(mul(z[a],z[b],p));
          d.push(F.map((_,j)=>add(mul(d[a][j],v[b],p),mul(z[a],d[b][j],p),p)));
        }else{
          const s=k.op==="s"?-1:1;v.push(add(v[a],v[b],p,s));z.push(add(z[a],z[b],p,s));
          d.push(F.map((_,j)=>add(d[a][j],d[b][j],p,s)));
        }
      }
      if(cert){
        const rhs=F.reduce((acc,f,j)=>add(acc,mul(f,d[i][j],p),p),[0]);
        check(eq(add(v[i],z[i],p,-1),rhs),"IPS exact polynomial difference at gate "+i);
      }
    }
    return {v,z,d};
  }
  // CROSS: explicit gate translation from +/-/* to +/*.
  function translate(g,p) {
    const h=[{op:"c",v:p-1}],map=[];
    for(const k of g){
      if(k.op==="s"){
        h.push({op:"m",a:0,b:map[k.b]});
        h.push({op:"a",a:map[k.a],b:h.length-1});
      }else if(k.op==="a"||k.op==="m")h.push({op:k.op,a:map[k.a],b:map[k.b]});
      else h.push({...k});
      map.push(h.length-1);
    }
    return {h,map};
  }
  let gates=0,dags=0,translated=0,diagonal=0,ipsWitnesses=0;
  for(const p of fields){
    for(let k=0;k<80;k++){
      const g=dag(p),F=Array.from({length:3},()=>trim([rnd(p),rnd(p),rnd(p)]));
      const original=evaluate(g,F,p,true);
      gates+=g.length;dags++;
      const {h,map}=translate(g,p),res=evaluate(h,F,p);
      check(h.length<=2*g.length+1,"CROSS gate overhead");
      for(let i=0;i<g.length;i++){check(eq(original.v[i],res.v[map[i]]),"CROSS polynomial semantics");translated++}
    }
    // Actual small IPS certificate: y0+y1+(y0-x)y1, F=(x,1-x,0).
    const g=[{op:"x"},{op:"y",i:0},{op:"y",i:1},{op:"a",a:1,b:2},{op:"s",a:1,b:0},{op:"m",a:4,b:2},{op:"a",a:3,b:5}];
    const F=[[0,1],[1,p-1],[0]],r=evaluate(g,F,p,true);
    check(eq(r.v[6],[1])&&eq(r.z[6],[0]),"IPS witness");
    ipsWitnesses++;
    for(let v=0;v<p;v++){check(mod(v+1,p)!==v,"CROSS diagonal toy");diagonal++}
  }
  report.IPS={dags,gate_identities:gates,actual_certificate_examples:ipsWitnesses,fields};
  report.CROSS={translated_gate_outputs:translated,diagonal_values:diagonal,fields};
  // GEO: exact flattening ranks for orthogonal diameter identity tensor.
  function rank(A,p){
    A=A.map(row=>row.slice());let r=0;const m=A.length,n=A[0].length;
    for(let j=0;j<n&&r<m;j++){
      let k=r;while(k<m&&A[k][j]===0)k++;if(k===m)continue;
      [A[r],A[k]]=[A[k],A[r]];let inv=1;while(mod(A[r][j]*inv,p)!==1)inv++;
      for(let c=j;c<n;c++)A[r][c]=mod(A[r][c]*inv,p);
      for(let i=r+1;i<m;i++){const f=A[i][j];if(f)for(let c=j;c<n;c++)A[i][c]=mod(A[i][c]-f*A[r][c],p)}
      r++;
    }return r;
  }
  let cuts=0,rankSum=0;
  for(const p of fields)for(const m of [1,2])for(let mask=0;mask<16;mask++){
    const left=[],right=[];for(let i=0;i<4;i++)((mask>>i)&1?left:right).push(i);
    const q=2**m,decode=(a,idx,x)=>{for(const i of idx){x[i]=a%q;a=Math.floor(a/q)}};
    const A=Array.from({length:q**left.length},(_,a)=>Array.from({length:q**right.length},(_,b)=>{
      const x=[];decode(a,left,x);decode(b,right,x);return x[0]===x[1]&&x[2]===x[3]?1:0;
    }));
    const crossing=Number(Boolean(mask&1)!==Boolean(mask&2))+Number(Boolean(mask&4)!==Boolean(mask&8));
    check(rank(A,p)===q**crossing,"GEO flattening rank");
    cuts++;
  }
  for(const p of fields)for(let i=0;i<60;i++){
    const A=Array.from({length:6},()=>Array.from({length:6},()=>rnd(p)));
    const B=Array.from({length:6},()=>Array.from({length:6},()=>rnd(p)));
    const C=A.map((row,j)=>row.map((v,k)=>mod(v+B[j][k],p)));
    check(rank(C,p)<=rank(A,p)+rank(B,p),"GEO rank subadditivity");rankSum++;
  }
  report.GEO={exact_flattening_ranks:cuts,rank_sum_checks:rankSum,fields};
  // LOOP: tied affine polynomial cells. Homogeneous augmented coordinates and binary powering.
  const mm=(A,B,p)=>A.map(row=>B[0].map((_,j)=>row.reduce((s,x,k)=>add(s,mul(x,B[k][j],p),p),[0])));
  const eye=n=>Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>[Number(i===j)]));
  const matEq=(A,B)=>A.every((row,i)=>row.every((v,j)=>eq(v,B[i][j])));
  function power(A,t,p){
    let R=eye(A.length),B=A;
    while(t){if(t%2)R=mm(R,B,p);t=Math.floor(t/2);if(t)B=mm(B,B,p)}
    return R;
  }
  let loopCases=0;
  for(const p of fields)for(let k=0;k<20;k++){
    const width=1+rnd(3),poly=()=>trim([rnd(p),rnd(p)]);
    const A=Array.from({length:width},()=>Array.from({length:width+1},poly));
    A.push(Array.from({length:width+1},(_,j)=>[Number(j===width)]));
    const h=Array.from({length:width},()=>[poly()]);h.push([[1]]);
    let direct=h;
    for(let t=0;t<=31;t++){
      if([0,1,2,3,5,8,13,21,31].includes(t)){
        check(matEq(direct,mm(power(A,t,p),h,p)),"LOOP fast-forward exact polynomial");loopCases++;
      }
      if(t<31)direct=mm(A,direct,p);
    }
  }
  report.LOOP={exact_polynomial_cases:loopCases,fields,steps:[0,1,2,3,5,8,13,21,31],widths:[1,2,3]};
  return report;
}
console.log(JSON.stringify(runFive(), null, 2));
