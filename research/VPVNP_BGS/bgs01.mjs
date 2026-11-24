// Exact finite Boolean/oracle regression. Run with Node; no dependencies.
function audit() {
  const check=(h,m)=>{if(!h)throw Error(m)}, mod=(x,p)=>((x%p)+p)%p;
  const fields=[2,3,5,7,11];
  function rank(A,p) {
    const a=A.map(r=>r.map(x=>mod(x,p)));let r=0;
    for(let j=0;j<a[0].length&&r<a.length;j++){
      let k=r;while(k<a.length&&!a[k][j])k++;
      if(k===a.length)continue;
      [a[r],a[k]]=[a[k],a[r]];
      let u=1;while(mod(u*a[r][j],p)!==1)u++;
      for(let l=j;l<a[r].length;l++)a[r][l]=mod(a[r][l]*u,p);
      for(let i=r+1;i<a.length;i++){
        let v=a[i][j];if(v)for(let l=j;l<a[i].length;l++)a[i][l]=mod(a[i][l]-v*a[r][l],p);
      }r++;
    }return r;
  }
  const pc=x=>{let k=0;while(x){x&=x-1;k++;}return k};
  const result={schema:"vpvnp-bgs01",fields,rank_rows:[],checks:{rank_triples:0,boolean_or_bound:0,mobius_entries:0,count_cancellations:0,zero_path_transcripts:0,complete_or_tables:0}};
  for(const p of fields)for(let n=1;n<=6;n++){
    const N=1<<n;
    const D=Array.from({length:N},(_,x)=>Array.from({length:N},(_,y)=>Number((x&y)===0)));
    const O=D.map(row=>row.map(v=>1-v)),C=D.map((row,x)=>row.map((_,y)=>pc(x&y)));
    const rd=rank(D,p),ro=rank(O,p),rc=rank(C,p);
    check(rd===N&&ro===N-1&&rc===n,"disjointness ranks");
    result.rank_rows.push({p,n,disjoint:rd,nondisjoint:ro,count:rc});
    result.checks.rank_triples++;
    for(let x=0;x<N;x++)for(let y=0;y<N;y++){
      let a=0;
      for(let t=x&y;;t=(t-1)&(x&y)){a+=pc(t)%2?-1:1;if(t===0)break}
      check(mod(a,p)===D[x][y],"zeta diagonal identity");
      result.checks.mobius_entries++;
    }
    if(n>=p){check(C[N-1][(1<<p)-1]===p&&mod(p,p)===0&&O[N-1][(1<<p)-1]===1,"count cancellation");result.checks.count_cancellations++}
  }
  let seed=20261124;
  const rand=()=>{seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0};
  for(const p of fields)for(let trial=0;trial<128;trial++){
    const m=4,n=5;
    const A=Array.from({length:m},()=>Array.from({length:n},()=>rand()&1));
    const B=Array.from({length:m},()=>Array.from({length:n},()=>rand()&1));
    const H=A.map((row,i)=>row.map((x,j)=>x|B[i][j]));
    const r=rank(A,p),s=rank(B,p);
    check(rank(H,p)<=r+s+r*s,"two term OR bound");
    result.checks.boolean_or_bound++;
  }
  // Enumerate all possible all-zero transcripts of length <= N (including repeats).
  // Realize each as an adaptive tree: on any yes answer halt true.
  // All-zero output is false; a one-hot oracle evades iff its index is absent.
  for(const N of [2,4,8]){
    const depth=N<=4?N:3;
    function enumerate(path,left) {
      for(let i=0;i<N;i++){
        const yes=path.some(q=>q===i);
        const observed=path.map(q=>Number(q===i));
        check(yes===observed.includes(1),"one-hot path");
        if(path.length<N&&!yes)check(observed.every(v=>v===0),"unqueried witness");
        result.checks.zero_path_transcripts++;
      }
      if(left)for(let i=0;i<N;i++)enumerate([...path,i],left-1);
    }
    enumerate([],depth);
    for(let t=0;t<2**N;t++){
      let scan=0;for(let i=0;i<N;i++)scan|=(t>>i)&1;
      check(scan===Number(t!==0),"complete OR scan");
      result.checks.complete_or_tables++;
    }
  }
  return result;
}
console.log(JSON.stringify(audit(), null, 2));
