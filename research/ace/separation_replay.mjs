import { readFileSync } from 'node:fs';
import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects, expandClass, compile } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
import { buildDelta } from './bounded_absoluteness.mjs';
import { buildSep } from './separation_instances.mjs';

function runO(pinned,part){
  const defs=definition("v",true);if(!same(pinned,defs.L))throw Error("pinned L mismatch");
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],B=(p,q)=>C(I(p,q),I(q,p));
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){const f=i=>i<d?i:indices[i-d]+d;return [op,f(a),f(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  function rel(p,domain=null,d=0){
    const [op,a,b]=p,g=domain===null?defs.L:M(0,domain+d+1);
    if(op==="A")return A(I(g,rel(a,domain,d+1)));
    if(op==="E")return E(C(g,rel(a,domain,d+1)));
    if(["&","|",">"].includes(op))return [op,rel(a,domain,d),rel(b,domain,d)];
    return p;
  }
  function guarded(p){
    const [op,a,b]=p;
    if(op==="A")return A(I(["G",0],guarded(a)));
    if(op==="E")return E(C(["G",0],guarded(a)));
    if(["&","|",">"].includes(op))return [op,guarded(a),guarded(b)];
    return p;
  }
  const wrapParams=(n,q)=>{for(let i=n-1;i>=0;i--)q=A(I(M(0,i+1),q));return q;};
  function expectedDef(phi,k){
    const loc=rel(embed(phi,[0,...Array.from({length:k},(_,i)=>k+1-i)]),k+2);
    const spec=A(B(M(0,1),C(M(0,k+2),loc)));
    return A(wrapParams(k,A(I(spec,embed(defs.definable,[k+1,0])))));
  }
  function expectedDelta(phi,k){
    const p=embed(phi,Array.from({length:k},(_,i)=>k-1-i));
    const tr=A(I(M(0,1),A(I(M(0,1),M(0,2)))));
    return A(I(tr,I(A(I(M(0,1),defs.L)),wrapParams(k,B(rel(p,k),rel(p))))));
  }
  const compilerCases={
    atom:{phi:["M",0,1],k:1},
    existential:{phi:["E",["&",["M",0,1],["M",0,2]]],k:1},
    universal:{phi:["A",[">",["M",0,1],["|",["M",0,2],["=",0,2]]]],k:1},
    false:{phi:["F"],k:0}
  };
  const proofs={},counts={exact_goals:0,rejections:0};
  function check(n,p,policy="ZF",want=null){
    const r=kernel(0,[],p.proof,false,policy);
    if(!same(r.goal,p.goal))throw Error("goal mismatch "+n);
    if(want){if(!same(want,r.goal))throw Error("independent exact goal mismatch "+n);counts.exact_goals++;}
    proofs[n]={nodes:r.visits,proof_bytes:JSON.stringify(p.proof).length};
  }
  function reject(fn){if(!rejects(fn))throw Error("negative control accepted");counts.rejections++;}
  function def(phi,k){return buildF(defs,{mode:"compiler",formula:phi,params:k}).compiled_formula_definable;}
  function insertSetParam(phi,d=0){
    const [op,a,b]=phi;
    if(op==="F")return phi;
    if(op==="A"||op==="E")return [op,insertSetParam(a,d+1)];
    if(op==="M"||op==="="){const f=i=>i<=d?i:i+1;return [op,f(a),f(b)];}
    return [op,insertSetParam(a,d),insertSetParam(b,d)];
  }
  if(part==="compiler"){
    for(const [name,{phi,k}] of Object.entries(compilerCases)){
      const p=def(phi,k);check(name,p,"ZF",expectedDef(phi,k));
    }
    reject(()=>def(["M",0,1],0));reject(()=>def(["F"],4));reject(()=>def(["bogus"],0));
  }else if(part==="delta"){
    const cases=[
      ...Object.entries(compilerCases).map(([name,{phi,k}])=>({name,phi,k:k+1})),
      {name:"nested",phi:["A",[">",["M",0,1],["E",["&",["M",0,1],["M",0,3]]]]],k:2}
    ];
    for(const {name,phi,k} of cases)check(name,buildDelta(defs,phi,k),"logic",expectedDelta(phi,k));
    reject(()=>buildDelta(defs,["E",["M",0,1]],1));
    reject(()=>buildDelta(defs,["A",[">",["M",0,0],["F"]]],0));
    reject(()=>buildDelta(defs,["M",0,2],2));
  }else{
    const c=compilerCases[part];if(!c)throw Error("unknown part");
    const {phi,k}=c,compiled=C(M(0,1),insertSetParam(phi));
    const dp=def(compiled,k+1),delta=buildDelta(defs,phi,k+1);
    check("subset_definability",dp,"ZF",expectedDef(compiled,k+1));
    check("bounded_absoluteness",delta,"logic",expectedDelta(phi,k+1));
    const prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true);
    const p=buildSep(defs,stages,phi,k,dp,delta),spec={name:"separation",params:k,body:phi};
    const goal=guarded(kernel(0,[],["axiom",spec],false,"ZF").goal);
    const exact=expandClass(goal,defs.L);
    // Check pure certificate goal independently via the source schema.
    if(!same(p.goal,exact))throw Error("pure schema exact-goal mismatch");
    counts.exact_goals++;
    const proof=["conv",goal,["closed",p.proof]],cert={spec,proof},opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[cert]};
    const result=compile(0,[],["axiom",spec],opts);
    if(!same(result.target.goal,goal))throw Error("compiled schema goal mismatch");
    counts.exact_goals++;
    proofs.separation_certificate={nodes:result.target.visits-1,proof_bytes:JSON.stringify(proof).length};
    reject(()=>compile(0,[],["axiom",spec],{...opts,certificates:[]}));
    reject(()=>compile(0,[],["axiom",{name:"choice"}],{...opts,certificates:[]}));
    reject(()=>kernel(0,[],["conv",goal,["closed",["axiom",{name:"empty"}]]],true,"ZF",defs.L));
    return {experiment:"ACE-03O",part,spec,proofs,...counts,source_nodes:result.source.visits,target_nodes:result.target.visits,pinned_L_unchanged:true,scope:"one fixed bounded Separation instance, not unrestricted schema"};
  }
  return {experiment:"ACE-03O",part,proofs,...counts,pinned_L_unchanged:true,scope:part==="compiler"?"fixed formula program proof generator; finite resource caps":"bounded quantifier absoluteness"};
}

const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
console.log(JSON.stringify(runO(pinned,process.argv[2]),null,2));
