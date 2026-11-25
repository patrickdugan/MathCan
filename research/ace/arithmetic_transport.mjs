// ACE-02 finite semantic transport regression. Node 22.
function rng(seed) {
  let s=seed>>>0;
  return n=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)%n;};
}

function termScope(t,k) {
  if(!Array.isArray(t)) return false;
  switch(t[0]) {
    case "v": return t.length===2&&Number.isSafeInteger(t[1])&&t[1]>=0&&t[1]<k;
    case "z": return t.length===1;
    case "s": return t.length===2&&termScope(t[1],k);
    case "+": case "*": return t.length===3&&termScope(t[1],k)&&termScope(t[2],k);
    default:return false;
  }
}

function formulaScope(p,k) {
  if(!Number.isSafeInteger(k)||k<0||!Array.isArray(p))return false;
  switch(p[0]) {
    case "F":return p.length===1;
    case "=":case "<":return p.length===3&&termScope(p[1],k)&&termScope(p[2],k);
    case "&":case "|":case ">":return p.length===3&&formulaScope(p[1],k)&&formulaScope(p[2],k);
    case "A":case "E":return p.length===2&&formulaScope(p[1],k+1);
    default:return false;
  }
}

function makeTerm(r,k,d) {
  const op=d===0?r(2):r(5);
  if(op===0&&k)return ["v",r(k)];
  if(op<=1)return ["z"];
  if(op===2)return ["s",makeTerm(r,k,d-1)];
  return [op===3?"+":"*",makeTerm(r,k,d-1),makeTerm(r,k,d-1)];
}

function makeFormula(r,k,d) {
  const op=d===0?r(3):r(8);
  if(op===0)return ["F"];
  if(op<=2)return [op===1?"=":"<",makeTerm(r,k,3),makeTerm(r,k,3)];
  if(op<=5)return [["&","|",">"][op-3],makeFormula(r,k,d-1),makeFormula(r,k,d-1)];
  return [op===6?"A":"E",makeFormula(r,k+1,d-1)];
}

function directTerm(t,env,m) {
  switch(t[0]) {
    case "v":return env[t[1]];
    case "z":return 0;
    case "s":return (1+directTerm(t[1],env,m))%m;
    case "+":return (directTerm(t[1],env,m)+directTerm(t[2],env,m))%m;
    case "*":return (directTerm(t[1],env,m)*directTerm(t[2],env,m))%m;
    default:throw Error("bad term");
  }
}

function directSat(p,env,m) {
  switch(p[0]){
    case "F":return false;
    case "=":return directTerm(p[1],env,m)===directTerm(p[2],env,m);
    case "<":return directTerm(p[1],env,m)<directTerm(p[2],env,m);
    case "&":return directSat(p[1],env,m)&&directSat(p[2],env,m);
    case "|":return directSat(p[1],env,m)||directSat(p[2],env,m);
    case ">":return !directSat(p[1],env,m)||directSat(p[2],env,m);
    case "A":for(let x=0;x<m;x++)if(!directSat(p[1],[x,...env],m))return false;return true;
    case "E":for(let x=0;x<m;x++)if(directSat(p[1],[x,...env],m))return true;return false;
    default:throw Error("bad formula");
  }
}

function permutation(r,m) {
  const a=Array.from({length:m},(_,i)=>i);
  for(let i=m-1;i>0;i--){const j=r(i+1);[a[i],a[j]]=[a[j],a[i]];}
  if(a.every((x,i)=>x===i))[a[0],a[1]]=[a[1],a[0]];
  return a;
}

function makeTable(f) {
  const m=f.length, domain=Array.from({length:m},(_,i)=>i);
  const inv=domain.map(i=>f.indexOf(i));
  return {domain,zero:f[0],succ:domain.map(x=>f[(inv[x]+1)%m]),
    add:domain.map(x=>domain.map(y=>f[(inv[x]+inv[y])%m])),
    mul:domain.map(x=>domain.map(y=>f[(inv[x]*inv[y])%m])),
    lt:domain.map(x=>domain.map(y=>inv[x]<inv[y]))};
}

function checkIso(f,N) {
  const m=f.length;
  if(N.domain.length!==m||new Set(f).size!==m||f.some(x=>!N.domain.includes(x))||f[0]!==N.zero)return false;
  for(let i=0;i<m;i++){
    if(f[(i+1)%m]!==N.succ[f[i]])return false;
    for(let j=0;j<m;j++)if(f[(i+j)%m]!==N.add[f[i]][f[j]]||
      f[(i*j)%m]!==N.mul[f[i]][f[j]]||(i<j)!==N.lt[f[i]][f[j]])return false;
  }
  return true;
}

function tableTerm(t,env,N) {
  const op=t[0];
  if(op==="v")return env[t[1]];
  if(op==="z")return N.zero;
  if(op==="s")return N.succ[tableTerm(t[1],env,N)];
  const a=tableTerm(t[1],env,N),b=tableTerm(t[2],env,N);
  if(op==="+")return N.add[a][b];
  if(op==="*")return N.mul[a][b];
  throw Error("bad term");
}

function tableSat(p,env,N) {
  const op=p[0];
  if(op==="F")return false;
  if(op==="A"||op==="E"){
    const values=N.domain.map(x=>tableSat(p[1],[x,...env],N));
    return op==="A"?values.every(Boolean):values.some(Boolean);
  }
  if(op==="="||op==="<"){
    const a=tableTerm(p[1],env,N),b=tableTerm(p[2],env,N);
    return op==="="?a===b:N.lt[a][b];
  }
  const a=tableSat(p[1],env,N),b=tableSat(p[2],env,N);
  if(op==="&")return a&&b;
  if(op==="|")return a||b;
  if(op===">")return !a||b;
  throw Error("bad formula");
}

function demand(x,msg) {if(!x)throw Error(msg);}

function run() {
  const seeds={}, controls={invalid_scope:0,known_binder:0,non_surjective_truth_flips:0,
    broken_iso_rejections:0,broken_operation_truth_flips:0};
  const binder=[
    [["A",["E",["=",["v",0],["v",1]]]],true],
    [["E",["A",["=",["v",0],["v",1]]]],false],
    [["A",["=",["+",["v",0],["z"]],["v",0]]],true],
    [["A",["E",["<",["v",1],["v",0]]]],false],
    [["E",["A",["<",["v",0],["v",1]]]],false],
    [["A",["E",["=",["s",["v",1]],["v",0]]]],true],
    [["E",["A",["=",["*",["v",0],["v",1]],["z"]]]],true]
  ];
  for(const seed of [109,113,127]){
    const r=rng(seed), s={structures:0,closed:0,open:0,true:0,false:0,transport_pass:0,scope_locality_pass:0};
    for(const m of [2,3,5]){
      const f=permutation(r,m),N=makeTable(f);
      demand(checkIso(f,N),"isomorphism");
      s.structures++;
      for(let i=0;i<256;i++){
        const k=i<128?0:1+r(3);
        const p=makeFormula(r,k,4);
        demand(formulaScope(p,k),"generated out of scope");
        const env=Array.from({length:k},()=>r(m));
        const val=directSat(p,env,m),relabeled=tableSat(p,env.map(x=>f[x]),N);
        demand(val===relabeled,"transport mismatch");
        const tail1=[0,m-1],tail2=[m-1,0];
        demand(val===directSat(p,[...env,...tail1],m)&&val===directSat(p,[...env,...tail2],m),"direct locality");
        demand(val===tableSat(p,[...env,...tail1].map(x=>f[x]),N)&&val===tableSat(p,[...env,...tail2].map(x=>f[x]),N),"table locality");
        s[k?"open":"closed"]++;s[val?"true":"false"]++;s.transport_pass++;s.scope_locality_pass++;
      }
      for(const [p,expected] of binder){
        demand(formulaScope(p,0)&&directSat(p,[],m)===expected&&tableSat(p,[],N)===expected,"known binder");
        controls.known_binder++;
      }
      const altered=JSON.parse(JSON.stringify(N));
      altered.succ[altered.zero]=altered.zero;
      demand(!checkIso(f,altered),"broken successor accepted");controls.broken_iso_rejections++;
      const p=["=",["s",["z"]],["z"]];
      demand(!directSat(p,[],m)&&tableSat(p,[],altered),"successor counterexample");controls.broken_operation_truth_flips++;
      for(const name of ["add","mul","lt"]){
        const bad=JSON.parse(JSON.stringify(N)),z=bad.zero;
        bad[name][z][z]=name==="lt"?!bad[name][z][z]:f[1];
        demand(!checkIso(f,bad),"broken "+name+" accepted");controls.broken_iso_rejections++;
      }
    }
    seeds[seed]=s;
  }
  const malformed=[
    [["=",["v",0],["z"]],0],
    [["A",["=",["v",1],["v",0]]],0],
    [["E",["=",["v",-1],["z"]]],0],
    [["=",["v",1.25],["z"]],2],
    [["A",["A",["=",["v",2],["v",1]]]],0],
    [["=",["s"],["z"]],0],
    [["A",["F"],["F"]],0],
    [["=",["z",0],["z"]],0],
    [["unknown"],0],
    [null,0]
  ];
  for(const [p,k] of malformed){demand(!formulaScope(p,k),"bad scope accepted");controls.invalid_scope++;}
  // A genuine proper substructure, not a PA model: constant-zero functions.
  const small={domain:[0],zero:0,succ:[0],add:[[0]],mul:[[0]],lt:[[false]]};
  const large={domain:[0,1],zero:0,succ:[0,0],add:[[0,0],[0,0]],mul:[[0,0],[0,0]],lt:[[false,false],[false,false]]};
  const all=["A",["=",["v",0],["z"]]],ex=["E",[">",["=",["v",0],["z"]],["F"]]];
  demand(tableSat(all,[],small)&&!tableSat(all,[],large),"universal domain counterexample");
  demand(!tableSat(ex,[],small)&&tableSat(ex,[],large),"existential domain counterexample");
  controls.non_surjective_truth_flips=2;
  return {experiment:"ACE-02",scope:"finite cyclic operation structures, not models of PA or ZF",seeds,controls,
    note:"truth preservation and scope locality checked against a direct modular evaluator and a relabeled table evaluator; synthetic deterministic tests only"};
}

console.log(JSON.stringify(run(),null,2));
