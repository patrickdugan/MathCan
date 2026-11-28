import { pathToFileURL } from "node:url";
// Parameter-free class definition generator; generated AST is in de Bruijn form.
function definition(prefix="v",internals=false){
  let serial=0;
  const Q=(a,b)=>["=",a,b],M=(a,b)=>["M",a,b],F=["F"],I=(p,q)=>[">",p,q],C=(...p)=>p.reduce((a,b)=>["&",a,b]),O=(...p)=>p.reduce((a,b)=>["|",a,b]),N=p=>I(p,F),B=(p,q)=>C(I(p,q),I(q,p));
  const bind=(op,body)=>{const v=prefix+(serial++);return [op,v,body(v)];};
  const A=f=>bind("A",f),E=f=>bind("E",f);
  const all=(a,f)=>A(x=>I(M(x,a),f(x))),some=(a,f)=>E(x=>C(M(x,a),f(x)));
  const empty=a=>A(x=>N(M(x,a)));
  const subset=(a,b)=>all(a,x=>M(x,b));
  const trans=a=>all(a,x=>subset(x,a));
  const ord=a=>C(trans(a),all(a,trans));
  const succ=(a,b)=>A(x=>B(M(x,b),O(M(x,a),Q(x,a))));
  const ind=a=>C(some(a,empty),all(a,x=>some(a,y=>succ(x,y))));
  const omega=a=>C(ind(a),A(b=>I(ind(b),subset(a,b))));
  const singleton=(p,a)=>A(x=>B(M(x,p),Q(x,a)));
  const unordered=(p,a,b)=>A(x=>B(M(x,p),O(Q(x,a),Q(x,b))));
  const pair=(p,a,b)=>E(u=>E(v=>C(singleton(u,a),unordered(v,a,b),unordered(p,u,v))));
  const val=(f,i,y)=>some(f,p=>pair(p,i,y));
  const uniqueValue=(f,i)=>E(y=>C(val(f,i,y),A(z=>I(val(f,i,z),Q(z,y)))));
  const graph=(f,d)=>C(all(f,p=>some(d,i=>E(y=>pair(p,i,y)))),all(d,i=>uniqueValue(f,i)));
  const tuple=(s,n,a)=>C(graph(s,n),all(n,i=>some(a,y=>val(s,i,y))));
  const agree=(s,t,n,i)=>all(n,j=>I(N(Q(i,j)),A(x=>B(val(s,j,x),val(t,j,x)))));
  const relAtom=(r,n,a,i,j,op)=>A(s=>{
    const property=some(a,x=>some(a,y=>C(val(s,i,x),val(s,j,y),op(x,y))));
    return B(M(s,r),C(tuple(s,n,a),property));
  });
  const relNeg=(r,p,n,a)=>A(s=>B(M(s,r),C(tuple(s,n,a),N(M(s,p)))));
  const relAnd=(r,p,q)=>A(s=>B(M(s,r),C(M(s,p),M(s,q))));
  const relEx=(r,p,n,a,i)=>A(s=>B(M(s,r),C(tuple(s,n,a),some(p,t=>agree(s,t,n,i)))));
  const entry=(f,k,r,n,a)=>O(
    some(n,i=>some(n,j=>relAtom(r,n,a,i,j,Q))),
    some(n,i=>some(n,j=>relAtom(r,n,a,i,j,M))),
    some(k,i=>E(p=>C(val(f,i,p),relNeg(r,p,n,a)))),
    some(k,i=>some(k,j=>E(p=>E(q=>C(val(f,i,p),val(f,j,q),relAnd(r,p,q)))))),
    some(k,i=>some(n,j=>E(p=>C(val(f,i,p),relEx(r,p,n,a,j)))))
  );
  const slice=(x,r,a,n,z,b)=>A(y=>{
    const witness=some(r,s=>C(val(s,z,y),agree(s,b,n,z)));
    return B(M(y,x),C(M(y,a),witness));
  });
  const lastSlice=(f,m,n,a,x)=>some(m,k=>C(succ(k,m),E(r=>{
    const atZero=some(n,z=>C(empty(z),E(b=>C(tuple(b,n,a),slice(x,r,a,n,z,b)))));
    return C(val(f,k,r),atZero);
  })));
  const validProgram=(f,m,n,a)=>C(graph(f,m),all(m,k=>E(r=>C(val(f,k,r),entry(f,k,r,n,a)))));
  const nonempty=a=>E(i=>M(i,a));
  const definable=(a,x)=>O(empty(x),E(w=>{
    const program=some(w,n=>some(w,m=>C(nonempty(n),nonempty(m),
      E(f=>C(validProgram(f,m,n,a),lastSlice(f,m,n,a,x))))));
    return C(omega(w),program);
  }));
  const defSet=(a,b)=>A(x=>B(M(x,b),definable(a,x)));
  const limit=b=>N(some(b,a=>succ(a,b)));
  const limitStage=(f,b,r)=>A(x=>B(M(x,r),some(b,i=>E(s=>C(val(f,i,s),M(x,s))))));
  const successorStage=(f,b,r)=>some(b,i=>C(succ(i,b),E(s=>C(val(f,i,s),defSet(s,r)))));
  const stage=(f,b,r)=>O(successorStage(f,b,r),C(limit(b),limitStage(f,b,r)));
  const stageGraph=(f,d)=>C(graph(f,d),all(d,b=>E(r=>C(val(f,b,r),stage(f,b,r)))));
  const l=x=>E(alpha=>C(ord(alpha),E(d=>C(succ(alpha,d),E(f=>{
    const witness=E(r=>C(val(f,alpha,r),M(x,r)));
    return C(stageGraph(f,d),witness);
  })))));
  const compile=(p,env)=>{
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="A"||op==="E")return [op,compile(b,[a,...env])];
    if(op==="M"||op==="="){
      const i=env.indexOf(a),j=env.indexOf(b);if(i<0||j<0)throw Error("free variable");
      return [op,i,j];
    }
    return [op,compile(a,env),compile(b,env)];
  };
  const free=Array.from({length:6},(_,i)=>"arg"+i);
  const result={
    empty:compile(empty(free[0]),[free[0]]),
    ordinal:compile(ord(free[0]),[free[0]]),
    successor:compile(succ(free[0],free[1]),free.slice(0,2)),
    pair:compile(pair(free[0],free[1],free[2]),free.slice(0,3)),
    omega:compile(omega(free[0]),[free[0]]),
    graph:compile(graph(free[0],free[1]),free.slice(0,2)),
    definable:compile(definable(free[0],free[1]),free.slice(0,2)),
    Def:compile(defSet(free[0],free[1]),free.slice(0,2)),
    L:compile(l(free[0]),[free[0]])
  };
  if(internals){
    result.val=compile(val(free[0],free[1],free[2]),free.slice(0,3));
    const add=(name,arity,fn)=>{result[name]=compile(fn(...free.slice(0,arity)),free.slice(0,arity));};
    add("singleton",2,singleton);add("unordered",3,unordered);add("inductive",1,ind);add("tuple",3,tuple);add("agree",4,agree);
    add("relMem",5,(r,n,a,i,j)=>relAtom(r,n,a,i,j,M));add("relEq",5,(r,n,a,i,j)=>relAtom(r,n,a,i,j,Q));add("relNeg",4,relNeg);add("relAnd",3,relAnd);add("relEx",5,relEx);add("entry",5,entry);add("slice",6,slice);
    add("validProgram",4,validProgram);add("lastSlice",5,lastSlice);add("stage",3,stage);
    result.stageGraph=compile(stageGraph(free[0],free[1]),free.slice(0,2));
  }
  return result;
}



function scopeStats(p,k){
  const out={nodes:0,atoms:0,quantifiers:0,max_binder_depth:0,free_indices:[]};
  const free=new Set();
  function rec(p,d){
    if(!Array.isArray(p))throw Error("non-array formula");
    out.nodes++;out.max_binder_depth=Math.max(out.max_binder_depth,d);
    const [op,a,b]=p;
    if(op==="F"&&p.length===1)return;
    if((op==="M"||op==="=")&&p.length===3){
      out.atoms++;
      for(const i of [a,b]){
        if(!Number.isSafeInteger(i)||i<0||i>=k+d)throw Error("scope");
        if(i>=d)free.add(i-d);
      }
      return;
    }
    if((op==="A"||op==="E")&&p.length===2){out.quantifiers++;rec(a,d+1);return;}
    if(["&","|",">"].includes(op)&&p.length===3){rec(a,d);rec(b,d);return;}
    throw Error("unknown grammar");
  }
  rec(p,0);out.free_indices=[...free].sort((a,b)=>a-b);return out;
}

function insistD(x,msg){if(!x)throw Error(msg);}

function rngD(seed){let s=seed>>>0;return n=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)%n;};}

function assignments(m,n){let t=[[]];for(let i=0;i<n;i++)t=t.flatMap(s=>Array.from({length:m},(_,j)=>[...s,j]));return t;}

function generated(r,n,d){
  const op=d?r(5):r(2);
  if(op<2)return [op?"mem":"eq",r(n),r(n)];
  if(op===2)return ["not",generated(r,n,d-1)];
  if(op===3)return ["and",generated(r,n,d-1),generated(r,n,d-1)];
  return ["exists",r(n),generated(r,n,d-1)];
}

function direct(p,s,m,R){
  const [op,a,b]=p;
  if(op==="eq")return s[a]===s[b];
  if(op==="mem")return R[s[a]][s[b]];
  if(op==="not")return !direct(a,s,m,R);
  if(op==="and")return direct(a,s,m,R)&&direct(b,s,m,R);
  if(op==="exists"){for(let x=0;x<m;x++){const v=s.slice();v[a]=x;if(direct(b,v,m,R))return true;}return false;}
  throw Error("direct op");
}

function program(p){
  const steps=[];
  function emit(p){
    const [op,a,b]=p;
    if(op==="eq"||op==="mem")steps.push([op,a,b]);
    else if(op==="not"){const j=emit(a);steps.push([op,j]);}
    else if(op==="and"){const j=emit(a),k=emit(b);steps.push([op,j,k]);}
    else if(op==="exists"){const j=emit(b);steps.push([op,j,a]);}
    else throw Error("compile op");
    return steps.length-1;
  }
  emit(p);return steps;
}

function relationProgram(steps,m,n,R){
  if(!Number.isSafeInteger(n)||n<=0||!Array.isArray(steps)||!steps.length)throw Error("shape");
  const tuples=assignments(m,n),rows=[];
  const idx=(x,k)=>Number.isSafeInteger(x)&&x>=0&&x<k;
  for(let i=0;i<steps.length;i++){
    const p=steps[i];if(!Array.isArray(p))throw Error("step");
    const [op,a,b]=p;
    if((op==="eq"||op==="mem")&&p.length===3&&idx(a,n)&&idx(b,n)){
      rows.push(tuples.map(s=>op==="eq"?s[a]===s[b]:R[s[a]][s[b]]));
    }else if(op==="not"&&p.length===2&&idx(a,i)){
      rows.push(rows[a].map(x=>!x));
    }else if(op==="and"&&p.length===3&&idx(a,i)&&idx(b,i)){
      rows.push(rows[a].map((x,j)=>x&&rows[b][j]));
    }else if(op==="exists"&&p.length===3&&idx(a,i)&&idx(b,n)){
      rows.push(tuples.map(s=>tuples.some((t,j)=>rows[a][j]&&s.every((x,k)=>k===b||x===t[k]))));
    }else throw Error("invalid relation step");
  }
  return {tuples,truth:rows.at(-1),rows};
}

function evalAst(p,env,D,R){
  const [op,a,b]=p;
  if(op==="F")return false;
  if(op==="=")return env[a]===env[b];
  if(op==="M")return R[env[b]].includes(env[a]);
  if(op==="A")return D.every(x=>evalAst(a,[x,...env],D,R));
  if(op==="E")return D.some(x=>evalAst(a,[x,...env],D,R));
  if(op==="&")return evalAst(a,env,D,R)&&evalAst(b,env,D,R);
  if(op==="|")return evalAst(a,env,D,R)||evalAst(b,env,D,R);
  if(op===">")return !evalAst(a,env,D,R)||evalAst(b,env,D,R);
  throw Error("bad AST");
}

function runD(){
  const defs=definition(),alpha=definition("fresh");
  const arity={empty:1,ordinal:1,successor:2,pair:3,omega:1,graph:2,definable:2,Def:2,L:1},formulas={};
  for(const [name,p] of Object.entries(defs)){
    insistD(JSON.stringify(p)===JSON.stringify(alpha[name]),"alpha instability "+name);
    const s=scopeStats(p,arity[name]);
    insistD(s.free_indices.length===arity[name],"missing free variable "+name);
    formulas[name]={...s,bytes:JSON.stringify(p).length};
  }
  const seeds={};
  for(const seed of [109,113,127]){
    const r=rngD(seed),s={programs:0,tuple_truth_checks:0,slice_checks:0,empty_domain_programs:0};
    for(let j=0;j<128;j++){
      const m=j%4,n=1+r(3),R=Array.from({length:m},()=>Array.from({length:m},()=>Boolean(r(2))));
      const p=generated(r,n,4),pr=relationProgram(program(p),m,n,R);
      for(let i=0;i<pr.tuples.length;i++){
        insistD(pr.truth[i]===direct(p,pr.tuples[i],m,R),"relational truth mismatch");s.tuple_truth_checks++;
      }
      for(const base of pr.tuples){
        const got=Array.from({length:m},(_,x)=>pr.tuples.some((t,i)=>pr.truth[i]&&t[0]===x&&t.slice(1).every((v,k)=>v===base[k+1])));
        const want=Array.from({length:m},(_,x)=>direct(p,[x,...base.slice(1)],m,R));
        insistD(JSON.stringify(got)===JSON.stringify(want),"parameter slice mismatch");s.slice_checks++;
      }
      if(!m)s.empty_domain_programs++;s.programs++;
    }
    seeds[seed]=s;
  }
  // Each subset of finite A of size m<=4 can be defined by a disjunction
  // of coordinate-zero equalities to parameters. Negation/conjunction
  // implement disjunction; the empty subset uses a contradiction.
  let finiteSubsetWitnesses=0;
  for(let m=1;m<=4;m++){
    const R=Array.from({length:m},()=>Array(m).fill(false));
    for(let mask=0;mask<2**m;mask++){
      const selected=Array.from({length:m},(_,i)=>i).filter(i=>mask>>i&1);
      const n=1+selected.length,base=[0,...selected];
      let formula=["not",["eq",0,0]];
      for(let j=1;j<n;j++)formula=["not",["and",["not",formula],["not",["eq",0,j]]]];
      // Avoid enumerating all tuples at m=4,n=5 for the largest witness:
      // the relation engine is still tractable (1024 tuples, no exists).
      const o=relationProgram(program(formula),m,n,R);
      const values=Array.from({length:m},(_,x)=>o.tuples.some((t,i)=>o.truth[i]&&t[0]===x&&t.slice(1).every((v,k)=>v===base[k+1])));
      insistD(values.every((v,i)=>v===Boolean(mask>>i&1)),"finite subset definition");finiteSubsetWitnesses++;
    }
  }
  // Build a transitive hereditarily finite domain from concrete sets.
  // This tests actual generated pair, successor, ordinal and graph
  // formulas on known graph objects, not the full L formula.
  const R=[],ids=new Map();
  function set(xs){const a=[...new Set(xs)].sort((x,y)=>x-y),key=a.join(",");if(!ids.has(key)){ids.set(key,R.length);R.push(a);}return ids.get(key);}
  const z=set([]),one=set([z]),two=set([z,one]),three=set([z,one,two]);
  const kp=(a,b)=>set([set([a]),set([a,b])]);
  const p00=kp(z,z),p01=kp(z,one),p10=kp(one,z),p11=kp(one,one);
  const good=set([p01,p10]),partial=set([p01]),nonfunctional=set([p00,p01,p10]),stray=set([p01,p10,z]);
  const D=R.map((_,i)=>i);
  let hfChecks=0;
  function check(name,args,want){const got=evalAst(defs[name],args,D,R);insistD(got===want,"HF "+name+" "+args);hfChecks++;}
  for(const a of D)check("empty",[a],R[a].length===0);
  for(const a of [z,one,two,three,p01])check("ordinal",[a],a!==p01);
  check("successor",[z,one],true);check("successor",[one,two],true);check("successor",[two,three],true);check("successor",[z,two],false);
  for(const [p,a,b,w] of [[p00,z,z,true],[p01,z,one,true],[p10,one,z,true],[p11,one,one,true],[p01,one,z,false],[z,z,z,false]])check("pair",[p,a,b],w);
  for(const [g,w] of [[good,true],[partial,false],[nonfunctional,false],[stray,false]])check("graph",[g,two],w);
  const badPrograms=[[["not",0]],[["exists",0,1]],[["eq",0,3]],[["eq",0,0],["and",0,1]],[["unknown",0,0]],[]];
  for(const p of badPrograms){let caught=false;try{relationProgram(p,2,2,[[false,false],[false,false]]);}catch(e){caught=true;}insistD(caught,"bad program accepted");}
  return {experiment:"ACE-03D",scope:"pure membership-language definition generator and finite semantic regressions; no formal ZF adequacy proof",formulas,seeds,finite_subset_witnesses:finiteSubsetWitnesses,hf_domain_size:D.length,hf_checks:hfChecks,invalid_programs_rejected:badPrograms.length,alpha_rename_matches:Object.keys(defs).length};
}



export { definition };
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(runD(),null,2));
