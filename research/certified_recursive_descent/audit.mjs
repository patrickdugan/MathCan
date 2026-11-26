// CRD-01: exact rational certificate checks and synthetic proof obligations.
// Run: node audit.mjs; node audit.mjs --dataset > cases.jsonl
// No claim of validating Cogentic's factorization theorem.
function check(ok, message){if(!ok) throw new Error(message);}

function cube(n){return n*n*n;}

function verify({pNum,pDen,rNum,rDen,a,c}){
  const v=[pNum,pDen,rNum,rDen,a,c];
  if(v.some(x=>!Number.isSafeInteger(x))) return "domain";
  if(pNum<=0||pNum>=pDen||rNum<=0||rNum>=rDen||a<0||c<=0) return "domain";
  const [pn,pd,rn,rd,aa,cc]=v.map(BigInt);
  if(cube(rn)*pd<pn*cube(rd)) return "contraction";
  if(aa*rd+cc*rn>=cc*rd) return "slack";
  return "valid";
}

function upperRoot(pNum,pDen,rDen){
  let lo=0,hi=rDen;
  while(hi-lo>1){
    const m=Math.floor((hi+lo)/2);
    if(cube(BigInt(m))*BigInt(pDen)>=BigInt(pNum)*cube(BigInt(rDen))) hi=m;
    else lo=m;
  }
  return hi;
}

function cases(){
  const rows=[];
  // Split by complete shrink-ratio families, not by individual paired examples.
  for(const pDen of [7,11,13,17,19,23]){
    for(let pNum=1;pNum<pDen;pNum++){
      const rDen=5000, rNum=upperRoot(pNum,pDen,rDen);
      for(const c of [4000,8000,10400,16000]){
        const a=Math.floor((c*(rDen-rNum)-1)/rDen);
        const base={pNum,pDen,rNum,rDen,a,c};
        const split=pDen<=13?"development":pDen===17?"validation":"heldout";
        const pair=`${pNum}/${pDen}:${c}`;
        // C and a share hundredth units. Exact rational comparisons decide labels.
        rows.push({split,pair,certificate:base,expected:"valid"});
        rows.push({split,pair,certificate:{...base,a:a+1},expected:"slack"});
        rows.push({split,pair,certificate:{...base,rNum:rNum-1,a:0},expected:"contraction"});
      }
    }
  }
  return rows;
}

function gcd(a,b){while(b){[a,b]=[b,a%b];}return Math.abs(a);}

function squareAudit(){
  let moduli=0,unitPairs=0,congruent=0,degenerate=0,nontrivial=0;
  for(let n=9;n<=127;n+=2){
    if(!Array.from({length:Math.floor(Math.sqrt(n))-1},(_,i)=>i+2).some(d=>n%d===0)) continue;
    moduli++;
    const units=Array.from({length:n-1},(_,i)=>i+1).filter(x=>gcd(x,n)===1);
    for(const x of units) for(const y of units){
      unitPairs++;
      if((x*x-y*y)%n!==0) continue;
      congruent++;
      const g=gcd(x-y,n), h=gcd(x+y,n);
      check(g*h===n&&gcd(g,h)===1,"odd-unit square partition");
      const trivial=(x===y||x+y===n);
      check(trivial===(g===1||g===n),"trivial-sign classification");
      if(trivial) degenerate++; else nontrivial++;
    }
  }
  return {moduli,unitPairs,congruent,degenerate,nontrivial};
}

function audit(){
  check(2n*cube(3969n)>cube(5000n),"rational cube upper bound");
  check(104n*3969n*100n<8256n*5000n,"82.56 upper bound");
  check(2115n+8256n===10371n&&10371n<10400n,"induction ledger");
  check(verify({pNum:1,pDen:2,rNum:3969,rDen:5000,a:2115,c:10400})==="valid","reported ledger");
  check(verify({pNum:1,pDen:2,rNum:3969,rDen:5000,a:2115,c:10200})==="slack","failed bound");
  check(verify({pNum:1,pDen:2,rNum:3968,rDen:5000,a:2115,c:10400})==="contraction","invalid cube");
  const rows=cases(), splits={}, outcomes={};
  for(const row of rows){
    const actual=verify(row.certificate);
    check(actual===row.expected,`${row.pair}:${actual} != ${row.expected}`);
    splits[row.split]=(splits[row.split]||0)+1;
    outcomes[actual]=(outcomes[actual]||0)+1;
  }
  // Leading-term crossover, not finite-N time guarantee.
  const target=105**6;
  let lo=2,hi=1e16;
  for(let i=0;i<100;i++){const mid=(hi+lo)/2;if(mid/Math.log(mid)>target)hi=mid;else lo=mid;}
  return {status:"PASS",scope:"conditional arithmetic and bounded examples only",certificateCases:rows.length,splits,outcomes,squareAudit:squareAudit(),fixedPoint:21.15/(1-Math.cbrt(0.5)),crossoverBits:(hi+lo)/(2*Math.LN2)};
}

export {verify, cases, squareAudit, audit};
if (process.argv.includes('--dataset')) {
  for(const {expected,...row} of cases()) console.log(JSON.stringify({...row,expected}));
} else {
  console.log(JSON.stringify(audit(),null,2));
}
