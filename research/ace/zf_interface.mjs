import { pathToFileURL } from "node:url";
// ACE-03B extended standalone proof kernel; derived from ACE-03A.
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

function kernel(k,ctx,p,g=false,theory="logic",classDef=null){
  if(!["logic","CL","ZF","ZFC"].includes(theory))fail("theory");
  if(classDef!==null&&(!g||!scoped(classDef,1,false)))fail("invalid class definition");
  if(!Number.isSafeInteger(k)||k<0||!Array.isArray(ctx)||!ctx.every(a=>scoped(a,k,g)))fail("bad context");
  let visits=0;
  function rec(k,c,n){
    visits++;
    if(!Array.isArray(n))fail("bad proof");
    const [r,a,b,d,e]=n;
    const arity={h:2,iI:3,iE:3,aI:3,aL:2,aR:2,oL:3,oR:3,oE:4,fE:3,uI:2,uE:3,eI:4,eE:4,refl:2,dne:2,eqS:4,axiom:2,closed:2,conv:3};
    if(!Object.hasOwn(arity,r)||n.length!==arity[r])fail("rule or arity");
    const formula=(v,j=k)=>{if(!scoped(v,j,g))fail("bad formula scope");return v;};
    const term=(i)=>{if(!idx(i,k))fail("bad variable");return i;};
    const get=(v,op)=>{if(v[0]!==op)fail("wrong connective");return v;};
    const eq=(a,b)=>{if(!same(a,b))fail("formula mismatch");};
    const q=(x)=>rec(k,c,x);
    switch(r){
      case "h":if(!idx(a,c.length))fail("bad hypothesis");return c[a];
      case "refl":term(a);return ["=",a,a];
      case "dne":{
        if(theory==="logic")fail("classical inference forbidden");
        const v=get(q(a),">"),w=get(v[1],">");eq(v[2],["F"]);eq(w[2],["F"]);return w[1];
      }
      case "eqS":{
        formula(a,k+1);const v=get(q(b),"=");eq(inst(a,v[1]),q(d));return inst(a,v[2]);
      }
      case "axiom":return axiomFormula(a,theory);
      case "closed":if(!g)fail("closed import target only");return rec(0,[],a);
      case "conv":{
        if(!g||classDef===null)fail("no class definition");
        formula(a);eq(expandClass(a,classDef),expandClass(q(b),classDef));return a;
      }
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

function compile(k,ctx,p,opts={}){
  const {sourceTheory="logic",targetTheory="logic",classDef=null,certificates=[]}=opts;
  if(!["logic","CL","ZF"].includes(targetTheory)||!Array.isArray(certificates))fail("target policy");
  const source=kernel(k,ctx,p,false,sourceTheory);
  const validated=certificates.map(c=>{
    if(!keys(c,["spec","proof"]))fail("certificate descriptor");
    const want=rel(axiomFormula(c.spec,sourceTheory));
    const got=kernel(0,[],c.proof,true,targetTheory,classDef);
    if(!same(got.goal,want))fail("certificate goal mismatch");
    return {want,proof:c.proof};
  });
  for(let i=0;i<validated.length;i++)for(let j=0;j<i;j++)
    if(same(validated[i].want,validated[j].want))fail("duplicate certificate");
  const targetCtx=[...Array.from({length:k},(_,i)=>["G",i]),...ctx.map(rel)];
  function tr(k,c,n,m,h,guards){
    const [r,a,b,d]=n;
    const rec=(v)=>tr(k,c,v,m,h,guards);
    switch(r){
      case "h":return h[a];
      case "refl":return n;
      case "dne":return ["dne",rec(a)];
      case "eqS":return ["eqS",rel(a),rec(b),rec(d)];
      case "axiom":{
        const want=rel(axiomFormula(a,sourceTheory));
        const c=validated.find(v=>same(v.want,want));if(!c)fail("missing relativized axiom proof");
        return ["closed",c.proof];
      }
      case "iI":return ["iI",rel(a),tr(k,[...c,a],b,m+1,[...h,hyp(m)],guards)];
      case "iE":case "aI":return [r,rec(a),rec(b)];
      case "aL":case "aR":return [r,rec(a)];
      case "oL":return [r,rec(a),rel(b)];
      case "oR":return [r,rel(a),rec(b)];
      case "oE":{
        const p=kernel(k,c,a,false,sourceTheory).goal;
        return [r,rec(a),tr(k,[...c,p[1]],b,m+1,[...h,hyp(m)],guards),
          tr(k,[...c,p[2]],d,m+1,[...h,hyp(m)],guards)];
      }
      case "fE":return [r,rec(a),rel(b)];
      case "uI":return ["uI",["iI",["G",0],tr(k+1,c.map(x=>lift(x)),a,m+1,h,[hyp(m),...guards])]];
      case "uE":return ["iE",["uE",rec(a),b],guards[b]];
      case "eI":return ["eI",["&",["G",0],rel(a)],b,["aI",guards[b],rec(d)]];
      case "eE":{
        const p=kernel(k,c,a,false,sourceTheory).goal;
        return ["eE",rec(a),rel(b),tr(k+1,[...c.map(x=>lift(x)),p[1]],d,m+1,
          [...h,["aR",hyp(m)]],[["aL",hyp(m)],...guards])];
      }
      default:fail("unsupported compiler rule");
    }
  }
  const proof=tr(k,ctx,p,targetCtx.length,ctx.map((_,i)=>hyp(k+i)),Array.from({length:k},(_,i)=>hyp(i)));
  const target=kernel(k,targetCtx,proof,true,targetTheory,classDef);
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


function keys(x,expected){return !!x&&typeof x==="object"&&!Array.isArray(x)&&same(Object.keys(x).sort(),expected.slice().sort());}

function axiomFormula(spec,theory){
  if(!["ZF","ZFC"].includes(theory)||!spec||typeof spec.name!=="string")fail("axiom policy");
  const name=spec.name;
  const A=(x,p)=>["A",x,p],E=(x,p)=>["E",x,p],M=(x,y)=>["M",x,y],Q=(x,y)=>["=",x,y];
  const I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],O=(p,q)=>["|",p,q],N=p=>I(p,["F"]);
  const B=(p,q)=>C(I(p,q),I(q,p));
  const empty=x=>A("w",N(M("w",x)));
  const successor=(x,y)=>A("w",B(M("w",y),O(M("w",x),Q("w",x))));
  const raw=(b,n)=>["raw",b,n];
  function encode(p,env=[]){
    const [op,a,b]=p;
    if(op==="F")return ["F"];
    if(op==="A"||op==="E")return [op,encode(b,[a,...env])];
    if(op==="="||op==="M"){
      const i=env.indexOf(a),j=env.indexOf(b);if(i<0||j<0)fail("unbound schema variable");
      return [op,i,j];
    }
    if(op==="raw"){
      return mapVars(a,(i,d)=>{
        if(i<d)return i;
        const j=env.indexOf(b[i-d]);if(j<0)fail("unbound schema parameter");
        return j+d;
      });
    }
    return [op,encode(a,env),encode(b,env)];
  }
  let p;
  if(name==="separation"||name==="replacement"){
    if(!keys(spec,["name","params","body"])||!Number.isSafeInteger(spec.params)||spec.params<0||spec.params>32)fail("schema descriptor");
    const n=spec.params,ps=Array.from({length:n},(_,i)=>"p"+i),b=spec.body;
    if(!scoped(b,n+(name==="separation"?1:2),false))fail("schema scope");
    if(name==="separation"){
      const phi=x=>raw(b,[x,...ps]);
      p=A("a",E("b",A("x",B(M("x","b"),C(M("x","a"),phi("x"))))));
    }else{
      const phi=(x,y)=>raw(b,[y,x,...ps]);
      const unique=A("x",I(M("x","a"),E("y",C(phi("x","y"),A("z",I(phi("x","z"),Q("z","y")))))));
      const image=E("b",A("y",B(M("y","b"),E("x",C(M("x","a"),phi("x","y"))))));
      p=A("a",I(unique,image));
    }
    for(const x of ps)p=A(x,p);
  }else{
    if(!keys(spec,["name"]))fail("fixed axiom descriptor");
    switch(name){
      case "extensionality":p=A("x",A("y",I(A("z",B(M("z","x"),M("z","y"))),Q("x","y"))));break;
      case "empty":p=E("x",empty("x"));break;
      case "pairing":p=A("x",A("y",E("z",A("w",B(M("w","z"),O(Q("w","x"),Q("w","y")))))));break;
      case "union":p=A("a",E("b",A("x",B(M("x","b"),E("y",C(M("y","a"),M("x","y")))))));break;
      case "power":p=A("a",E("b",A("x",B(M("x","b"),A("y",I(M("y","x"),M("y","a")))))));break;
      case "infinity":p=E("a",C(E("x",C(empty("x"),M("x","a"))),A("x",I(M("x","a"),E("y",C(M("y","a"),successor("x","y")))))));break;
      case "foundation":p=A("a",I(E("x",M("x","a")),E("x",C(M("x","a"),A("y",I(M("y","x"),N(M("y","a"))))))));break;
      case "choice":{
        if(theory!=="ZFC")fail("choice forbidden");
        const nonempty=A("x",I(M("x","a"),E("y",M("y","x"))));
        const disjoint=A("x",A("y",I(C(C(M("x","a"),M("y","a")),N(Q("x","y"))),A("z",I(M("z","x"),N(M("z","y")))))));
        const selected=E("c",A("x",I(M("x","a"),E("y",C(C(M("y","x"),M("y","c")),A("z",I(C(M("z","x"),M("z","c")),Q("z","y"))))))));
        p=A("a",I(C(nonempty,disjoint),selected));break;
      }
      default:fail("unknown axiom");
    }
  }
  const out=encode(p);
  if(!scoped(out,0,false))fail("axiom not closed");
  return out;
}

function expandClass(p,def){
  const [op,a,b]=p;
  if(op==="G")return inst(def,a);
  if(op==="F"||op==="="||op==="M")return p;
  if(op==="A"||op==="E")return [op,expandClass(a,def)];
  return [op,expandClass(a,def),expandClass(b,def)];
}

function expectedFixed(name,D,R){
  const all=f=>D.every(f),some=f=>D.some(f),mem=(x,y)=>R[x][y];
  const ext=(x,y)=>all(z=>mem(z,x)===mem(z,y));
  const subset=(x,y)=>all(z=>!mem(z,x)||mem(z,y));
  const empty=x=>all(z=>!mem(z,x));
  switch(name){
    case "extensionality":return all(x=>all(y=>!ext(x,y)||x===y));
    case "empty":return some(empty);
    case "pairing":return all(x=>all(y=>some(z=>all(w=>mem(w,z)===(w===x||w===y)))));
    case "union":return all(a=>some(b=>all(x=>mem(x,b)===some(y=>mem(y,a)&&mem(x,y)))));
    case "power":return all(a=>some(b=>all(x=>mem(x,b)===subset(x,a))));
    case "infinity":return some(a=>some(x=>empty(x)&&mem(x,a))&&all(x=>!mem(x,a)||some(y=>mem(y,a)&&all(w=>mem(w,y)===(mem(w,x)||w===x)))));
    case "foundation":return all(a=>!some(x=>mem(x,a))||some(x=>mem(x,a)&&all(y=>!mem(y,x)||!mem(y,a))));
    case "choice":return all(a=>{
      const family=D.filter(x=>mem(x,a));
      const disjoint=family.every(x=>family.every(y=>x===y||!some(z=>mem(z,x)&&mem(z,y))));
      return !disjoint||family.some(empty)||some(c=>family.every(x=>D.filter(y=>mem(y,x)&&mem(y,c)).length===1));
    });
    default:fail("bad fixed axiom");
  }
}

function expectedSchema(spec,D,R){
  const n=spec.params,all=f=>D.every(f),some=f=>D.some(f),mem=(x,y)=>R[x][y];
  function go(ps){
    if(ps.length<n)return all(x=>go([x,...ps]));
    if(spec.name==="separation"){
      const phi=x=>satSubset(spec.body,[x,...ps],D,R);
      return all(a=>some(b=>all(x=>mem(x,b)===(mem(x,a)&&phi(x)))));
    }
    const phi=(x,y)=>satSubset(spec.body,[y,x,...ps],D,R);
    return all(a=>{
      const members=D.filter(x=>mem(x,a));
      const functional=members.every(x=>D.filter(y=>phi(x,y)).length===1);
      return !functional||some(b=>all(y=>mem(y,b)===members.some(x=>phi(x,y))));
    });
  }
  return go([]);
}

function totalEmptyCertificate(){
  const spec={name:"empty"},goal=rel(axiomFormula(spec,"ZF"));
  // In the eE branch: h0 is the ordinary empty-set property.
  // Under uI it is shifted; h1 is the class guard for the newly bound object.
  return {spec,proof:["eE",["axiom",spec],goal,
    ["eI",lift(goal[1],1),0,["aI",["conv",["G",0],["refl",0]],
      ["uI",["iI",["G",0],["uE",hyp(0),0]]]]]]};
}

function runB(){
  const names=["extensionality","empty","pairing","union","power","infinity","foundation","choice"];
  const seeds={};
  for(const seed of [109,113,127]){
    const r=rng(seed),s={fixed_axiom_semantics:0,separation_semantics:0,replacement_semantics:0,logical_compiled:0,schema_leaves_checked:0,
      class_guard_transports:0,blocked_without_cert:0};
    for(let j=0;j<64;j++){
      const m=1+r(3),D=Array.from({length:m},(_,i)=>i),R=D.map(()=>D.map(()=>Boolean(r(2))));
      for(const name of names){
        const spec={name},theory=name==="choice"?"ZFC":"ZF",p=axiomFormula(spec,theory);
        requireOk(satSubset(p,[],D,R)===expectedFixed(name,D,R),"fixed axiom semantics "+name);
        const checked=kernel(0,[],["axiom",spec],false,theory);
        requireOk(same(checked.goal,p),"axiom goal");
        s.fixed_axiom_semantics++;
        requireOk(rejects(()=>compile(0,[],["axiom",spec],{sourceTheory:theory,targetTheory:"ZF"})),"axiom without certificate");
        s.blocked_without_cert++;
      }
      for(const name of ["separation","replacement"]){
        const n=r(3),b=gen(r,n+(name==="separation"?1:2),3),spec={name,params:n,body:b},p=axiomFormula(spec,"ZF");
        requireOk(satSubset(p,[],D,R)===expectedSchema(spec,D,R),"schema semantics "+name);
        requireOk(same(kernel(0,[],["axiom",spec],false,"ZF").goal,p),"schema leaf");
        s[name+"_semantics"]++;s.schema_leaves_checked++;
        requireOk(rejects(()=>compile(0,[],["axiom",spec],{sourceTheory:"ZF",targetTheory:"ZF"})),"schema without certificate");
        s.blocked_without_cert++;
      }
      const k=2+r(2),z=gen(r,k,4),body=gen(r,k+1,4),nn=[">",[">",z,["F"]],["F"]];
      const proofs=[
        {ctx:[nn],p:["dne",hyp(0)]},
        {ctx:[["=",0,1],inst(body,0)],p:["eqS",body,hyp(0),hyp(1)]},
        {ctx:[],p:["dne",["iI",[">",["A",["=",0,0]],["F"]],["iE",hyp(0),["uI",["refl",0]]]]]}
      ];
      for(const {ctx,p} of proofs){
        const o=compile(k,ctx,p,{sourceTheory:"ZF",targetTheory:"ZF"});
        requireOk(same(o.target.goal,rel(o.source.goal)),"classical/equality target");s.logical_compiled++;
      }
      const def=["=",0,0],c=totalEmptyCertificate(),options={sourceTheory:"ZF",targetTheory:"ZF",classDef:def,certificates:[c]};
      const checked=compile(0,[],["axiom",c.spec],options);
      requireOk(same(checked.target.goal,rel(axiomFormula(c.spec,"ZF"))),"positive axiom certificate");
      const open=compile(k,[],["axiom",c.spec],options);
      requireOk(same(open.target.goal,checked.target.goal),"closed certificate lift");
      s.class_guard_transports+=2;
    }
    seeds[seed]=s;
  }
  const c=totalEmptyCertificate(),def=["=",0,0],opts={sourceTheory:"ZF",targetTheory:"ZF",classDef:def,certificates:[c]};
  const controls=[
    ()=>kernel(0,[],["axiom",{name:"choice"}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"empty",formula:["F"]}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"separation",params:0,body:["M",0,1]}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"replacement",params:0,body:["G",0]}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"replacement",params:-1,body:["F"]}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"replacement",params:33,body:["F"]}],false,"ZF"),
    ()=>kernel(0,[],["axiom",{name:"made-up"}],false,"ZF"),
    ()=>kernel(1,[[">",[">",["F"],["F"]],["F"]]],["dne",hyp(0)],false,"logic"),
    ()=>kernel(2,[["M",0,1],["=",0,0]],["eqS",["=",0,0],hyp(0),hyp(1)],false,"ZF"),
    ()=>kernel(2,[["=",0,1],["M",0,0]],["eqS",["=",0,0],hyp(0),hyp(1)],false,"ZF"),
    ()=>kernel(1,[],["conv",["G",0],["refl",0]],true,"ZF"),
    ()=>kernel(1,[],["conv",["G",0],["refl",0]],true,"ZF",["M",0,0]),
    ()=>kernel(1,[],["conv",["G",0],["refl",0]],true,"ZF",["G",0]),
    ()=>kernel(1,[["F"]],["closed",hyp(0)],true,"ZF",def),
    ()=>compile(0,[],["axiom",c.spec],{...opts,certificates:[]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,certificates:[{spec:c.spec,proof:["axiom",c.spec]}]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,certificates:[{spec:c.spec,proof:hyp(0)}]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,certificates:[c,c]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,classDef:["M",0,0]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,targetTheory:"ZFC"}),
    ()=>compile(0,[],["axiom",{name:"choice"}],{...opts,sourceTheory:"ZFC",certificates:[{spec:{name:"choice"},proof:["axiom",{name:"choice"}]}]}),
    ()=>compile(0,[],["axiom",c.spec],{...opts,certificates:[{spec:c.spec,proof:["closed",hyp(0)]}]})
  ];
  for(const [i,fn] of controls.entries())requireOk(rejects(fn),"negative B "+i);
  return {experiment:"ACE-03B",scope:"explicit ZF/ZFC axiom syntax and proof-checked interpretation interface; total-class positive control only",seeds,
    negative_controls:controls.length,parameter_limit:32,choice_form:"choice set for disjoint nonempty family",target_policy:"ZF only, no AC; class predicate definition supplied separately",note:"finite structures need not satisfy ZF; no L certificates"};
}


function classProofs(){
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],O=(p,q)=>["|",p,q],F=["F"],N=p=>I(p,F),B=(p,q)=>C(I(p,q),I(q,p)),G=i=>["G",i],M=(i,j)=>["M",i,j],Q=(i,j)=>["=",i,j];
  const h=hyp,ii=(p,q)=>["iI",p,q],ie=(p,q)=>["iE",p,q],ai=(p,q)=>["aI",p,q],al=p=>["aL",p],ar=p=>["aR",p],ui=p=>["uI",p],ue=(p,...args)=>args.reduce((q,i)=>["uE",q,i],p),ei=(body,x,p)=>["eI",body,x,p],ee=(p,g,b)=>["eE",p,g,b],fe=(p,q)=>["fE",p,q],ax=name=>["axiom",{name}],cv=(p,q)=>["conv",p,q];
  const ag=p=>ui(ii(G(0),p));
  const goal=name=>rel(axiomFormula({name},"ZF"));
  const T=A(A(I(C(G(1),M(0,1)),G(0))));
  const E0=A(N(M(0,1))), EC=E(C(G(0),E0));
  const pairBody=A(B(M(0,1),O(Q(0,3),Q(0,2))));
  const PC=A(A(I(C(G(1),G(0)),E(C(G(0),pairBody)))));
  const unionBody=A(B(M(0,1),E(C(M(0,3),M(1,0)))));
  const UC=A(I(G(0),E(C(G(0),unionBody))));
  const H=A(I(G(0),B(M(0,2),M(0,1))));
  const lr=(x,g,proj)=>ii(M(0,x),ie(proj(ie(ue(h(3),0),ie(ue(h(0),x,0),ai(h(g),h(4))))),h(4)));
  const extInner=ie(ue(ax("extensionality"),1,0),ui(ai(lr(2,1,al),lr(1,2,ar))));
  const ext=ii(T,ag(ag(ii(H,extInner))));
  const emptyWitness=ei(lift(goal("empty")[1],1),0,ai(al(h(1)),ag(ue(ar(h(1)),0))));
  const empty=ii(EC,ee(h(0),goal("empty"),emptyWitness));
  const pg=goal("pairing")[1][2][1][2];
  const pairWitness=ei(lift(pg[1],1),0,ai(al(h(3)),ag(ue(ar(h(3)),0))));
  const pairing=ii(PC,ag(ag(ee(ie(ue(h(0),1,0),ai(h(1),h(2))),pg,pairWitness))));
  const ug=goal("union")[1][2];
  const ambEx=E(C(M(0,3),M(1,0))),guardEx=E(C(G(0),ambEx[1]));
  const guardY=ie(ue(h(0),3,0),ai(h(2),al(h(6))));
  const inL=ii(M(0,1),ee(ie(al(ue(ar(h(3)),0)),h(5)),guardEx,
    ei(lift(guardEx[1],1),0,ai(guardY,h(6)))));
  const inR=ii(guardEx,ie(ar(ue(ar(h(3)),0)),ee(h(5),ambEx,ei(lift(ambEx[1],1),0,ar(h(6))))));
  const unionWitness=ei(lift(ug[1],1),0,ai(al(h(3)),ag(ai(inL,inR))));
  const union=ii(T,ii(UC,ag(ee(ie(ue(h(1),0),h(2)),ug,unionWitness))));
  const nonempty=E(C(G(0),M(0,1)));
  const fg=goal("foundation")[1][2][2];
  const ambientNonempty=E(M(0,1));
  const ambientFound=ie(ue(ax("foundation"),0),ee(h(2),ambientNonempty,ei(lift(ambientNonempty[1],1),0,ar(h(3)))));
  const foundGuard=ie(ue(h(0),1,0),ai(h(1),al(h(3))));
  const foundWitness=ei(lift(fg[1],1),0,ai(foundGuard,ai(al(h(3)),ag(ue(ar(h(3)),0)))));
  const foundation=ii(T,ag(ii(nonempty,ee(ambientFound,fg,foundWitness))));
  const generic=[{name:"extensionality",premises:[T],proof:ext},{name:"empty",premises:[EC],proof:empty},{name:"pairing",premises:[PC],proof:pairing},{name:"union",premises:[T,UC],proof:union},{name:"foundation",premises:[T],proof:foundation}];
  const def=E0;
  const tContradiction=ie(ue(cv(lift(def,0),al(h(0))),0),ar(h(0)));
  const tProof=ui(ui(ii(C(G(1),M(0,1)),fe(tContradiction,G(0)))));
  const eProof=ee(ax("empty"),EC,ei(lift(EC[1],1),0,ai(cv(G(0),h(0)),h(0))));
  const noMem=ie(ue(cv(lift(def,0),h(0)),0),h(1));
  const rightFalse=ee(h(1),M(0,1),fe(ie(ue(cv(lift(lift(def,0),0),h(0)),0),al(h(2))),M(1,2)));
  const unionLeft=ii(M(0,1),fe(noMem,E(C(M(0,2),M(1,0)))));
  const unionRight=ii(E(C(M(0,2),M(1,0))),rightFalse);
  const unionClosure=ag(ei(UC[1][2][1],0,ai(h(0),ui(ai(unionLeft,unionRight)))));
  return {generic,def,closures:[{goal:T,proof:tProof},{goal:EC,proof:eProof},{goal:UC,proof:unionClosure}],goal};
}

function runC(){
  const p=classProofs();
  const generic={},closed={},certificates=[];
  for(const g of p.generic){
    const o=kernel(0,[],g.proof,true,"ZF");
    const want=g.premises.reduceRight((q,r)=>[">",r,q],p.goal(g.name));
    requireOk(same(o.goal,want),"conditional class theorem "+g.name);
    generic[g.name]={nodes:o.visits,premises:g.premises.length};
  }
  for(const c of p.closures){
    const o=kernel(0,[],c.proof,true,"ZF",p.def);
    requireOk(same(o.goal,c.goal),"closure proof mismatch");
  }
  for(const g of p.generic){
    const obligations=g.premises.map(x=>p.closures.find(c=>same(c.goal,x)));
    if(obligations.some(x=>!x))continue;
    const proof=obligations.reduce((q,c)=>["iE",q,c.proof],g.proof);
    const o=kernel(0,[],proof,true,"ZF",p.def);
    requireOk(same(o.goal,p.goal(g.name)),"discharged proof "+g.name);
    const cert={spec:{name:g.name},proof};certificates.push(cert);
    const r=compile(0,[],["axiom",cert.spec],{sourceTheory:"ZF",targetTheory:"ZF",classDef:p.def,certificates:[cert]});
    requireOk(same(r.target.goal,p.goal(g.name)),"compiler use "+g.name);
    closed[g.name]={nodes:o.visits,compiler_nodes:r.target.visits};
  }
  const opts={sourceTheory:"ZF",targetTheory:"ZF",classDef:p.def,certificates};
  for(const cert of certificates){
    const r=compile(2,[],["axiom",cert.spec],opts);
    requireOk(same(r.target.goal,p.goal(cert.spec.name)),"open import");
  }
  // A derivation of a conjunction of two distinct ZF axioms.
  const multi=["aI",["axiom",{name:"empty"}],["axiom",{name:"union"}]];
  const compiled=compile(0,[],multi,opts);
  requireOk(same(compiled.target.goal,["&",p.goal("empty"),p.goal("union")]),"composite source");
  // Exhaustive finite relations on domains 1..3 and all subclasses.
  // Verify semantic truth of each conditional class theorem whenever ambient
  // axioms used by that derivation are true. Also check closed proof goals
  // against the actual empty-object predicate.
  let structures=0,classes=0,conditionalChecks=0,conditionalNonvacuous=0,closedChecks=0,closedNonvacuous=0;
  let pairingCounterexamples=0,nontransitiveExtCounterexamples=0;
  const ambientNeeded={extensionality:["extensionality"],empty:[],pairing:[],union:[],foundation:["foundation"]};
  for(let n=1;n<=3;n++){
    const D=Array.from({length:n},(_,i)=>i);
    for(let mask=0;mask<2**(n*n);mask++){
      const R=D.map(i=>D.map(j=>Boolean((mask>>(i*n+j))&1)));
      structures++;
      const fixed=Object.fromEntries(["extensionality","empty","foundation","pairing","union"].map(x=>[x,expectedFixed(x,D,R)]));
      const S0=D.filter(x=>D.every(y=>!R[y][x]));
      for(const cert of certificates){
        const needed=[...ambientNeeded[cert.spec.name]];
        if(cert.spec.name==="empty")needed.push("empty");
        if(needed.every(x=>fixed[x])){
          closedNonvacuous++;
          requireOk(satAmbient(p.goal(cert.spec.name),[],D,S0,R),"closed semantic failure "+cert.spec.name);
        }
        closedChecks++;
      }
      if(fixed.extensionality&&fixed.empty&&S0.length===1&&!satAmbient(p.goal("pairing"),[],D,S0,R))pairingCounterexamples++;
      for(let sm=0;sm<2**n;sm++){
        const S=D.filter(i=>(sm>>i)&1);classes++;
        for(const g of p.generic){
          if(!ambientNeeded[g.name].every(x=>fixed[x]))continue;
          conditionalChecks++;
          const premise=g.premises.every(x=>satAmbient(x,[],D,S,R));
          if(premise){
            conditionalNonvacuous++;
            requireOk(satAmbient(p.goal(g.name),[],D,S,R),"conditional semantic failure "+g.name);
          }
        }
        if(fixed.extensionality&&!satAmbient(p.generic[0].premises[0],[],D,S,R)&&!satAmbient(p.goal("extensionality"),[],D,S,R))nontransitiveExtCounterexamples++;
      }
    }
  }
  requireOk(pairingCounterexamples>0&&nontransitiveExtCounterexamples>0,"missing control counterexamples");
  const controls=[
    ()=>compile(0,[],["axiom",{name:"pairing"}],opts),
    ()=>compile(0,[],["axiom",{name:"choice"}],{...opts,sourceTheory:"ZFC"}),
    ()=>compile(0,[],["axiom",{name:"empty"}],{...opts,classDef:["=",0,0]}),
    ()=>compile(0,[],["axiom",{name:"extensionality"}],{...opts,certificates:[{spec:{name:"extensionality"},proof:p.generic[0].proof}]}),
    ()=>compile(0,[],["axiom",{name:"union"}],{...opts,certificates:[{spec:{name:"union"},proof:p.closures[2].proof}]}),
    ()=>compile(0,[],["axiom",{name:"empty"}],{...opts,certificates:[{spec:{name:"empty"},proof:["axiom",{name:"empty"}]}]}),
    ()=>kernel(0,[],["iE",p.generic[0].proof,p.closures[1].proof],true,"ZF",p.def)
  ];
  for(const [i,x] of controls.entries())requireOk(rejects(x),"bad class certificate accepted "+i);
  return {experiment:"ACE-03C",scope:"conditional class closure derivations and closed singleton-empty-class controls; no definition of L",
    generic,closed,closure_proofs:p.closures.map(c=>kernel(0,[],c.proof,true,"ZF",p.def).visits),
    composite_source_nodes:compiled.source.visits,composite_target_nodes:compiled.target.visits,
    open_imports:certificates.length,finite_structures:structures,finite_subclasses:classes,conditional_checks:conditionalChecks,
    conditional_nonvacuous:conditionalNonvacuous,closed_checks:closedChecks,closed_nonvacuous:closedNonvacuous,
    pairing_counterexamples:pairingCounterexamples,nontransitive_extensionality_counterexamples:nontransitiveExtCounterexamples,
    negative_controls:controls.length};
}


export { same, scoped, inst, kernel, expandClass, classProofs, rejects, compile };
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) console.log(JSON.stringify({prior_regression:run(),current:runB(),class_closure:runC()},null,2));
