// Exact small-cell-complex observation certificate audit.
function runSmithAudit() {
  const abs=x=>x<0n?-x:x;
  const gcd=(a,b)=>{a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b];}return a;};
  function combos(n,k){if(k===0)return [[]];if(k>n)return [];const out=[];function walk(start,r){if(r.length===k){out.push(r.slice());return;}for(let i=start;i<=n-(k-r.length);i++){r.push(i);walk(i+1,r);r.pop();}}walk(0,[]);return out;}
  function det(A){
    if(!A.length)return 1n;
    if(A.length===1)return A[0][0];
    let z=0n;
    for(let j=0;j<A.length;j++)z+=(j%2?-1n:1n)*A[0][j]*det(A.slice(1).map(r=>r.filter((_,k)=>k!==j)));
    return z;
  }
  function smithInvariants(A,g){
    const B=A.map(r=>r.map(BigInt)),div=[1n],examined=[];
    for(let k=1;k<=Math.min(B.length,g);k++){
      let d=0n,n=0;
      for(const rows of combos(B.length,k))for(const cols of combos(g,k)){
        d=gcd(d,det(rows.map(i=>cols.map(j=>B[i][j]))));n++;
      }
      examined.push(n);if(d===0n)break;div.push(d);
    }
    const factors=div.slice(1).map((d,i)=>{if(d%div[i])throw Error("nonintegral factor");return d/div[i]});
    if(factors.some((d,i)=>i&&d%factors[i-1]))throw Error("nondivisibility");
    return {rank:factors.length,free:g-factors.length,factors:factors.map(String),divisors:div.map(String),examined};
  }
  function bruteKernel(A,g,m){
    let count=0,visits=0;const x=Array(g).fill(0);
    function walk(i){
      if(i===g){visits++;if(A.every(row=>row.reduce((s,a,j)=>s+a*x[j],0)%m===0))count++;return;}
      for(let a=0;a<m;a++){x[i]=a;walk(i+1);}
    }
    walk(0);return {count,visits};
  }
  const edges=[[0,1],[0,2],[0,4],[1,3],[1,5],[2,3],[2,6],[3,7],[4,5],[4,6],[5,7],[6,7]],faces=[[0,1,3,2],[4,5,7,6],[0,1,5,4],[2,3,7,6],[0,2,6,4],[1,3,7,5]];
  const tree=[0,1,2,3,4,6,7],chords=edges.map((_,i)=>i).filter(i=>!tree.includes(i));
  const A=faces.map(f=>chords.map(c=>{
    const [a,b]=edges[c];let v=0;for(let j=0;j<f.length;j++){const x=f[j],y=f[(j+1)%f.length];if(x===a&&y===b)v++;if(x===b&&y===a)v--;}return v;
  }));
  const fixtures=[{name:"Q3_all_faces",A,g:5}];
  for(const k of [4,5])for(const ids of combos(6,k))fixtures.push({name:"Q3_"+k+"_faces_"+ids.join(""),A:ids.map(i=>A[i]),g:5});
  fixtures.push({name:"circle",A:[],g:1},{name:"torus_abelianized_face",A:[[0,0]],g:2},{name:"degree_2_attaching_map_RP2",A:[[2]],g:1},{name:"degree_6_attaching_map",A:[[6]],g:1},{name:"nontrivial_integer_mixed_presentation",A:[[2,4],[6,8]],g:2},{name:"rank_deficient_with_torsion",A:[[2,4,0],[4,8,0]],g:3});
  let checks=0,visits=0;
  const rows=fixtures.map(({name,A,g})=>{
    const snf=smithInvariants(A,g),moduli=g>=5?[2,3,4,5,6]:[2,3,4,5,6,8,12];
    const modular=moduli.map(m=>{
      const exact=BigInt(m)**BigInt(snf.free)*snf.factors.reduce((v,d)=>v*gcd(BigInt(m),BigInt(d)),1n);
      const brute=bruteKernel(A,g,m);checks++;visits+=brute.visits;
      if(exact!==BigInt(brute.count))throw Error("kernel mismatch "+name+" mod "+m);
      return {m,predicted:Number(exact),enumerated:brute.count,assignments:brute.visits};
    });
    return {name,A,g,...snf,modular};
  });
  const q=rows.filter(x=>x.name.startsWith("Q3_"));
  if(q.some(x=>x.factors.some(d=>d!=="1")))throw Error("unexpected Q3 torsion");
  return {version:"PGC-SNF-01",evidence:"exact integer minors and exhaustive finite cyclic kernels; no hardware",fixture_count:rows.length,checks,assignments:visits,edge_order:edges,faces,chord_indices:chords,fixtures:rows,limitations:["Determinantal minors scale combinatorially; this is a small-certificate reference implementation, not a production SNF algorithm.","Finite-modulus enumerations check the formula on selected fixtures only.","The torus classification uses the standard mathematical Smith normal form theorem; no general SNF existence proof in Lean is claimed."]};
}
console.log(JSON.stringify(runSmithAudit(),null,2));
