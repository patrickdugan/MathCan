// ACE-03A: restricted first-order proof compiler. Run with Node 22.
function fail(msg){throw Error(msg);}

function same(a,b){return JSON.stringify(a)===JSON.stringify(b);}

function idx(i,k){return Number.isSafeInteger(i)&&i>=0&&i<k;}

function scoped(p,k,g){
  if(!Array.isArray(p))return false;
  const [op,a,b]=p;
  if(op==="F")return p.length===1;
  if(op==="G")return g&&p.length===2&&idx(a,k);
  if(op==="="||op==="M")return p.length===3&&idx(a,k)&&idx(b,k);
  if(op==="A"||op==="E")return p.length===2&&scoped(a,k+1,g);
  if(["&","|",">"].includes(op))return p.length===3&&scoped(a,k,g)&&scoped(b,k,g);
  return false;
}

function mapVars(p,f,d=0){
  const [op,a,b]=p;
  if(op==="F")return p;
  if(op==="G")return [op,f(a,d)];
  if(op==="="||op==="M")return [op,f(a,d),f(b,d)];
  if(op==="A"||op==="E")return [op,mapVars(a,f,d+1)];
  return [op,mapVars(a,f,d),mapVars(b,f,d)];
}

function lift(p,c=0){return mapVars(p,(i,d)=>i>=d+c?i+1:i);}

function inst(p,x){return mapVars(p,(i,d)=>i===d?x+d:i>d?i-1:i);}

function rel(p){
  const [op,a,b]=p;
  if(op==="A")return ["A",[">",["G",0],rel(a)]];
  if(op==="E")return ["E",["&",["G",0],rel(a)]];
  if(["&","|",">"].includes(op))return [op,rel(a),rel(b)];
  return p;
}

function hyp(i){return ["h",i];}

function kernel(k,ctx,p,g=false){
  if(!Number.isSafeInteger(k)||k<0||!Array.isArray(ctx)||!ctx.every(a=>scoped(a,k,g)))fail("bad context");
  let visits=0;
  function rec(k,c,n){
    visits++;
    if(!Array.isArray(n))fail("bad proof");
    const [r,a,b,d,e]=n;
    const arity={h:2,iI:3,iE:3,aI:3,aL:2,aR:2,oL:3,oR:3,oE:4,fE:3,uI:2,uE:3,eI:4,eE:4,refl:2};
    if(!Object.hasOwn(arity,r)||n.length!==arity[r])fail("rule or arity");
    const formula=(v,j=k)=>{if(!scoped(v,j,g))fail("bad formula scope");return v;};
    const term=(i)=>{if(!idx(i,k))fail("bad variable");return i;};
    const get=(v,op)=>{if(v[0]!==op)fail("wrong connective");return v;};
    const eq=(a,b)=>{if(!same(a,b))fail("formula mismatch");};
    const q=(x)=>rec(k,c,x);
    switch(r){
      case "h":if(!idx(a,c.length))fail("bad hypothesis");return c[a];
      case "refl":term(a);return ["=",a,a];
      case "iI":formula(a);return [">",a,rec(k,[...c,a],b)];
      case "iE":{const p=get(q(a),">");eq(p[1],q(b));return p[2];}
      case "aI":return ["&",q(a),q(b)];
      case "aL":return get(q(a),"&")[1];
      case "aR":return get(q(a),"&")[2];
      case "oL":return ["|",q(a),formula(b)];
      case "oR":return ["|",formula(a),q(b)];
      case "oE":{const p=get(q(a),"|");const l=rec(k,[...c,p[1]],b),rr=rec(k,[...c,p[2]],d);eq(l,rr);return l;}
      case "fE":eq(q(a),["F"]);return formula(b);
      case "uI":return ["A",rec(k+1,c.map(x=>lift(x)),a)];
      case "uE":return inst(get(q(a),"A")[1],term(b));
      case "eI":formula(a,k+1);term(b);eq(inst(a,b),q(d));return ["E",a];
      case "eE":{
        const p=get(q(a),"E");formula(b);
        eq(rec(k+1,[...c.map(x=>lift(x)),p[1]],d),lift(b));return b;
      }
      default:fail("unknown");
    }
  }
  return {goal:rec(k,ctx,p),visits};
}

function compile(k,ctx,p){
  const source=kernel(k,ctx,p);
  const targetCtx=[...Array.from({length:k},(_,i)=>["G",i]),...ctx.map(rel)];
  function tr(k,c,n,m,h,guards){
    const [r,a,b,d]=n;
    const rec=(v)=>tr(k,c,v,m,h,guards);
    switch(r){
      case "h":return h[a];
      case "refl":return n;
      case "iI":return ["iI",rel(a),tr(k,[...c,a],b,m+1,[...h,hyp(m)],guards)];
      case "iE":case "aI":return [r,rec(a),rec(b)];
      case "aL":case "aR":return [r,rec(a)];
      case "oL":return [r,rec(a),rel(b)];
      case "oR":return [r,rel(a),rec(b)];
      case "oE":{
        const p=kernel(k,c,a).goal;
        return [r,rec(a),tr(k,[...c,p[1]],b,m+1,[...h,hyp(m)],guards),
          tr(k,[...c,p[2]],d,m+1,[...h,hyp(m)],guards)];
      }
      case "fE":return [r,rec(a),rel(b)];
      case "uI":return ["uI",["iI",["G",0],tr(k+1,c.map(x=>lift(x)),a,m+1,h,[hyp(m),...guards])]];
      case "uE":return ["iE",["uE",rec(a),b],guards[b]];
      case "eI":return ["eI",["&",["G",0],rel(a)],b,["aI",guards[b],rec(d)]];
      case "eE":{
        const p=kernel(k,c,a).goal;
        return ["eE",rec(a),rel(b),tr(k+1,[...c.map(x=>lift(x)),p[1]],d,m+1,
          [...h,["aR",hyp(m)]],[["aL",hyp(m)],...guards])];
      }
      default:fail("unsupported compiler rule");
    }
  }
  const proof=tr(k,ctx,p,targetCtx.length,ctx.map((_,i)=>hyp(k+i)),Array.from({length:k},(_,i)=>hyp(i)));
  const target=kernel(k,targetCtx,proof,true);
  if(!same(target.goal,rel(source.goal)))fail("translated goal mismatch");
  return {targetCtx,proof,source,target};
}

function rng(seed){let s=seed>>>0;return n=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)%n;};}

function gen(r,k,d){
  if(d===0){if(k===0||r(3)===0)return ["F"];return [r(2)?"=":"M",r(k),r(k)];}
  const o=r(6);
  if(o===0)return gen(r,k,0);
  if(o===1||o===2)return [o===1?"A":"E",gen(r,k+1,d-1)];
  return [["&","|",">"][o-3],gen(r,k,d-1),gen(r,k,d-1)];
}

function satSubset(p,env,S,E){
  const [op,a,b]=p;
  switch(op){
    case "F":return false;
    case "=":return env[a]===env[b];
    case "M":return E[env[a]][env[b]];
    case "&":return satSubset(a,env,S,E)&&satSubset(b,env,S,E);
    case "|":return satSubset(a,env,S,E)||satSubset(b,env,S,E);
    case ">":return !satSubset(a,env,S,E)||satSubset(b,env,S,E);
    case "A":return S.every(x=>satSubset(a,[x,...env],S,E));
    case "E":return S.some(x=>satSubset(a,[x,...env],S,E));
    default:fail("subset language");
  }
}

function satAmbient(p,env,D,S,E){
  const [op,a,b]=p;
  if(op==="F")return false;
  if(op==="G")return S.includes(env[a]);
  if(op==="=")return env[a]===env[b];
  if(op==="M")return E[env[a]][env[b]];
  if(op==="A"||op==="E"){
    const v=D.map(x=>satAmbient(a,[x,...env],D,S,E));
    return op==="A"?v.every(Boolean):v.some(Boolean);
  }
  const x=satAmbient(a,env,D,S,E),y=satAmbient(b,env,D,S,E);
  if(op==="&")return x&&y;
  if(op==="|")return x||y;
  if(op===">")return !x||y;
  fail("ambient language");
}

function templates(r,k){
  const p=gen(r,k+1,3),q=gen(r,k+1,3),z=gen(r,k,3),w=gen(r,k,3);
  const i=r(k),pr=inst(p,i);
  const pair=["&",p,p],exPair=["E",pair];
  return [
    {family:"identity",ctx:[],proof:["iI",z,hyp(0)]},
    {family:"universal_elim",ctx:[["A",p]],proof:["uE",hyp(0),i]},
    {family:"existential_intro",ctx:[pr],proof:["eI",p,i,hyp(0)]},
    {family:"universal_intro",ctx:[],proof:["uI",["iI",p,hyp(0)]]},
    {family:"existential_elim",ctx:[["E",p]],proof:["eE",hyp(0),exPair,["eI",lift(pair,1),0,["aI",hyp(1),hyp(1)]]]},
    {family:"quantified_mp",ctx:[["A",[">",p,q]],["A",p]],proof:["uI",["iE",["uE",hyp(0),0],["uE",hyp(1),0]]]},
    {family:"existential_mp",ctx:[["E",p],["A",[">",p,lift(z)]]],proof:["eE",hyp(0),z,["iE",["uE",hyp(1),0],hyp(2)]]},
    {family:"disjunction_elim",ctx:[["|",z,w],[">",z,pr],[">",w,pr]],proof:["oE",hyp(0),["iE",hyp(1),hyp(3)],["iE",hyp(2),hyp(3)]]},
    {family:"falsum",ctx:[["F"]],proof:["fE",hyp(0),z]},
    {family:"reflexivity",ctx:[],proof:["refl",i]}
  ];
}

function requireOk(b,msg){if(!b)fail(msg);}

function rejects(f){try{f();}catch(e){return true;}return false;}

function run(){
  const seeds={},counts={};
  for(const seed of [109,113,127]){
    const r=rng(seed),s={formulas:0,empty_class:0,proofs:0,semantic_proof_checks:0,nonvacuous_proof_checks:0,shift_commutes:0,substitution_commutes:0,source_nodes:0,target_nodes:0,source_bytes:0,target_bytes:0};
    for(let j=0;j<128;j++){
      const m=1+r(4),D=Array.from({length:m},(_,i)=>i),S=D.filter(()=>r(2)===1),E=D.map(()=>D.map(()=>Boolean(r(2))));
      const k=S.length? r(4):0, env=Array.from({length:k},()=>S[r(S.length)]),p=gen(r,k,4);
      requireOk(scoped(p,k,false)&&scoped(rel(p),k,true),"scope");
      requireOk(satSubset(p,env,S,E)===satAmbient(rel(p),env,D,S,E),"semantic disagreement");
      requireOk(same(lift(rel(p)),rel(lift(p))),"lift commute");s.shift_commutes++;
      if(k>0){
        const b=gen(r,k+1,4),i=r(k);
        requireOk(same(inst(rel(b),i),rel(inst(b,i))),"instantiate commute");s.substitution_commutes++;
      }
      s.formulas++;if(!S.length)s.empty_class++;
      const pk=1+r(3),ambientEnv=Array.from({length:pk},()=>D[r(D.length)]);
      for(const {family,ctx,proof} of templates(r,pk)){
        const out=compile(pk,ctx,proof);
        s.proofs++;counts[family]=(counts[family]||0)+1;
        s.source_nodes+=out.source.visits;s.target_nodes+=out.target.visits;
        s.source_bytes+=JSON.stringify(proof).length;s.target_bytes+=JSON.stringify(out.proof).length;
        const envs=[ambientEnv];
        if(S.length)envs.push(Array.from({length:pk},()=>S[r(S.length)]));
        for(const assignment of envs){
          const premises=out.targetCtx.every(f=>satAmbient(f,assignment,D,S,E));
          if(premises){s.nonvacuous_proof_checks++;requireOk(satAmbient(out.target.goal,assignment,D,S,E),"invalid translated proof");}
          s.semantic_proof_checks++;
        }
      }
    }
    seeds[seed]=s;
  }
  const controls=[
    ()=>kernel(0,[],["uE",["uI",["refl",0]],0]),
    ()=>kernel(1,[],["h",0]),
    ()=>kernel(1,[],["refl",1]),
    ()=>kernel(1,[["G",0]],hyp(0)),
    ()=>kernel(1,[["A",["=",0,1]]],["uE",hyp(0),1]),
    ()=>kernel(1,[["M",0,0]],["eI",["=",0,0],0,hyp(0)]),
    ()=>kernel(1,[["E",["M",0,1]]],["eE",hyp(0),["M",0,0],hyp(1)]),
    ()=>kernel(1,[["M",0,0]],["uI",["eI",["M",0,0],0,hyp(0)]]),
    ()=>kernel(1,[],["refl",0,0]),
    ()=>kernel(1,[],["axiom","choice"]),
    ()=>kernel(1,[["A",[">",["G",0],["=",0,0]]]],["iE",["uE",hyp(0),0],["refl",0]],true),
    ()=>kernel(1,[["E",["&",["G",0],["M",0,1]]]],["eE",hyp(0),["M",0,0],["aR",hyp(1)]],true)
  ];
  for(const [i,test] of controls.entries())requireOk(rejects(test),"negative control "+i);
  // Deliberately omit a universal guard: all x=x0 holds on singleton S, fails on D.
  const D=[0,1],S=[0],E=[[false,false],[false,false]],p=["A",["=",0,1]];
  requireOk(satSubset(p,[0],S,E)&&satAmbient(rel(p),[0],D,S,E)&&!satAmbient(p,[0],D,S,E),"unguarded all");
  const ex=["E",[">",["=",0,1],["F"]]];
  requireOk(!satSubset(ex,[0],S,E)&&!satAmbient(rel(ex),[0],D,S,E)&&satAmbient(ex,[0],D,S,E),"unguarded exists");
  return {experiment:"ACE-03A",scope:"restricted intuitionistic natural deduction; generic class, not constructible universe or ZF axioms",seeds,families:counts,negative_proof_controls:controls.length,unguarded_quantifier_truth_flips:2,encoding:"JSON proof AST bytes, contexts excluded, tree expansion counted; no wall-time comparison"};
}

console.log(JSON.stringify(run(),null,2));
