// HAD-01 exact finite-chain and clipped-cube certificate replay.
// Run: node research/hadwiger_trajectory/verify.mjs
import assert from 'node:assert/strict';
const add = (a,b) => a.map((x,i)=>x+b[i]);
const sub = (a,b) => a.map((x,i)=>x-b[i]);
const mul = (a,b) => b.map(x=>a*x);
const zero = d => Array(d).fill(0n);
const eq = (a,b) => a.every((x,i)=>x===b[i]);
const sum = (a,d) => a.reduce(add,zero(d));
function certify(vertices, weights, pairs, x0, budget) {
  const d=x0.length;
  assert.equal(weights.length,pairs.length);
  assert(weights.every(a=>a>=0n));
  assert(pairs.every(([i,j])=>vertices[i] && vertices[j]));
  const A=weights.reduce((x,y)=>x+y,0n);
  assert(budget>=A && budget>0n);
  const U=pairs.map(([i],r)=>mul(weights[r],vertices[i]));
  const W=pairs.map(([,j],r)=>mul(weights[r],vertices[j]));
  // Padding uses vertex 0, so the origin need not be in K.
  const pad=mul(budget-A,vertices[0]);
  const v=sub(x0,add(sum(U,d),pad));
  let x=x0;
  for(let j=0;j<=pairs.length;j++){
    const witness=add(add(sum(W.slice(0,j),d),sum(U.slice(j),d)),pad);
    assert(eq(sub(x,v),witness));
    if(j<pairs.length) x=add(x,sub(W[j],U[j]));
  }
  return {v,A};
}
let cases=0;
for(let d=1;d<=6;d++){
  const vertices=[Array(d).fill(3n),...Array.from({length:d},(_,i)=>Array.from({length:d},(_,j)=>i===j?5n:3n))];
  for(let a=0;a<vertices.length;a++)
    for(let b=0;b<vertices.length;b++)
      for(let c=0;c<vertices.length;c++)
        for(let w=0;w<=3;w++){
          certify(vertices,[BigInt(w),2n,1n],[[a,b],[b,c],[c,a]],Array(d).fill(-7n),BigInt(w+4));
          cases++;
        }
}
assert.throws(()=>certify([[0n],[1n]],[2n],[[0,1]],[0n],1n));
assert.throws(()=>certify([[0n],[1n]],[-1n],[[0,1]],[0n],1n));
// K_t = [-1,1]^3 intersect sum x <= 3-t, t=k/8, k=0..16.
// Scale all coordinates by 48 to avoid fractions in corner witnesses.
let cornerChecks=0;
for(let k=0;k<=16;k++){
  const t=6n*BigInt(k), D=48n;
  const inK=p=>p.every(x=>x>=-D && x<=D)&&p.reduce((a,b)=>a+b,0n)<=3n*D-t;
  for(let mask=0;mask<8;mask++){
    const s=Array.from({length:3},(_,i)=>(mask>>i)&1?1n:-1n);
    // Difference is 2(1-t/6)s; all witnesses remain in K_t.
    let p=mul(D-t/6n,s),q=mul(-D,s);
    if(mask===0){p=mul(D,s);q=mul(-(D-t/3n),s);}
    else if(mask!==7){q=mul(-(D-t/6n),s);}
    else {p=mul(D-t/3n,s);}
    assert(inK(p)&&inK(q));
    assert(eq(sub(p,q),mul(2n*D-t/3n,s)));
    cornerChecks++;
  }
}
// Exact support for K_t at integral directions: h=||u||_1-t min(u) on positive octant.
let supportChecks=0;
for(let k=0;k<=16;k++){
  const D=8n,t=BigInt(k);
  const V=[];
  for(let mask=0;mask<7;mask++) V.push(Array.from({length:3},(_,i)=>(mask>>i)&1?D:-D));
  for(let i=0;i<3;i++) V.push(Array.from({length:3},(_,j)=>i===j?D-t:D));
  for(let x=-4;x<=4;x++)for(let y=-4;y<=4;y++)for(let z=-4;z<=4;z++){
    const u=[x,y,z].map(BigInt);
    const abs=u.reduce((s,a)=>s+(a<0n?-a:a),0n);
    const m=u.reduce((a,b)=>a<b?a:b);
    const expected=D*abs-(m>0n?t*m:0n);
    const observed=V.map(v=>v.reduce((s,a,i)=>s+a*u[i],0n)).reduce((a,b)=>a>b?a:b);
    assert.equal(observed,expected);
    supportChecks++;
  }
}
console.log(JSON.stringify({chain_cases:cases,negative_controls:2,corner_checks:cornerChecks,support_checks:supportChecks}));
