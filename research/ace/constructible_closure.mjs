import { readFileSync } from 'node:fs';
import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects, inst, expandClass, classProofs, compile } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';

function runJ(pinned,part){
  const defs=definition("v",true);
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  const finite=buildF(defs,"relations"),out={};
  function check(name,p,g=false,def=null){
    const r=kernel(0,[],p.proof,g,"ZF",def);
    if(!same(r.goal,p.goal))throw Error("goal mismatch "+name);
    out[name]={nodes:r.visits,proof_bytes:JSON.stringify(p.proof).length};
  }
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){
      const f=i=>i<d?i:indices[i-d]+d;
      return [op,f(a),f(b)];
    }
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b];
  const all=(n,p)=>{for(let i=0;i<n;i++)p=A(p);return p;};
  const imp=(...ps)=>ps.reduceRight((a,b)=>I(b,a));
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const SG=(f,d)=>embed(defs.stageGraph,[f,d]),V=(f,i,r)=>embed(defs.val,[f,i,r]),Succ=(b,d)=>embed(defs.successor,[b,d]),Ord=b=>embed(defs.ordinal,[b]),D=(a,x)=>embed(defs.definable,[a,x]),L=x=>embed(defs.L,[x]);
  const W=(b,r)=>E(C(Succ(b+1,0),E(C(SG(0,1),V(0,b+2,r+2)))));
  const Pair=(p,x,y)=>embed(defs.unordered,[p,x,y]);
  const Union=(x,p)=>A(B(M(0,p+1),E(C(M(0,x+2),M(1,0)))));
  function exact(p,goal,n){if(!same(p.goal,goal))throw Error("independent goal mismatch "+n);}
  if(part==="finite"){
    for(const n of ["equality_relation_exists","negation_relation_exists","intersection_relation_exists","existential_relation_exists","foundation_no_self","value_in_domain","graph_append_exists","ternary_tuple_exists","pair_definable","union_definable"])check(n,finite[n]);
    exact(finite.pair_definable,all(4,imp(M(2,3),M(1,3),Pair(0,2,1),D(3,0))),"pair_definable");
    exact(finite.union_definable,all(3,imp(trans(2),M(1,2),Union(1,0),D(2,0))),"union_definable");
    const tests=[()=>kernel(0,[],finite.pair_definable.proof,false,"CL"),()=>kernel(0,[],finite.union_definable.proof,false,"CL")];
    for(const t of tests)if(!rejects(t))throw Error("negative control accepted");
    return {proofs:out,independent_goal_checks:2,negative_controls:tests.length};
  }
  const prior=buildE(defs,true),p=buildI(defs,prior,finite,true),c=classProofs();
  if(part==="stage"){
    for(const n of ["ordinal_successor","binary_union_exists","ordinal_binary_union","ordinal_stage_value_transitive","ordinal_stage_value_monotone","common_constructible_stage","successor_stage_def","definable_subset_constructible"])check(n,p[n]);
    exact(p.definable_subset_constructible,all(3,imp(Ord(2),W(2,1),D(1,0),L(0))),"definable_subset_constructible");
    exact(p.common_constructible_stage,all(2,imp(L(1),L(0),E(E(C(C(C(Ord(1),W(1,0)),trans(0)),C(M(3,0),M(2,0))))))),"common_constructible_stage");
    return {proofs:out,independent_goal_checks:2,negative_controls:0};
  }
  if(part!=="pairing"&&part!=="union")throw Error("bad replay part");
  const ax=c.generic.find(x=>x.name===part),closure=part==="pairing"?ax.premises[0]:ax.premises[1],pure=p[part==="pairing"?"constructible_pair_closure":"constructible_union_closure"];
  exact(pure,expandClass(closure,defs.L),part+" closure");
  const guarded=["conv",closure,["closed",pure.proof]];
  let proof;
  if(part==="pairing")proof=["iE",ax.proof,guarded];
  else{
    const tr=prior.L_transitivity_conditional,inf=finite.def_inflation;
    if(!same(tr.goal[1],inf.goal))throw Error("inflation mismatch");
    const lP=["iE",tr.proof,inf.proof];
    const tx=["conv",inst(defs.L,1),["aL",["h",0]]];
    const sx=["iE",["uE",["closed",lP],1],tx],sy=["iE",["uE",sx,0],["aR",["h",0]]];
    const tg=["uI",["uI",["iI",["&",["G",1],["M",0,1]],["conv",["G",0],sy]]]];
    proof=["iE",["iE",ax.proof,tg],guarded];
  }
  const spec={name:part},cert={spec,proof},opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[cert]};
  const compiled=compile(0,[],["axiom",spec],opts);
  if(!same(compiled.target.goal,c.goal(part)))throw Error("compiler goal mismatch");
  const tests=[()=>compile(0,[],["axiom",spec],{...opts,certificates:[]}),()=>kernel(0,[],["conv",closure,["closed",["axiom",{name:"empty"}]]],true,"ZF",defs.L)];
  // The class binding control uses only the pure closed statement in its own
  // checked conversion. It rejects an alternative definition of G.
  if(!same(expandClass(closure,c.def),pure.goal))tests.push(()=>kernel(0,[],["conv",closure,["closed",["axiom",{name:"empty"}]]],true,"ZF",c.def));
  if(part==="union")tests.push(()=>compile(0,[],["axiom",{name:"choice"}],{...opts,certificates:[]}));
  for(const t of tests)if(!rejects(t))throw Error("negative control accepted");
  return {proofs:{[part==="pairing"?"constructible_pair_closure":"constructible_union_closure"]:{proof_bytes:JSON.stringify(pure.proof).length},[part+"_axiom"]:{nodes:compiled.target.visits-1,proof_bytes:JSON.stringify(proof).length}},independent_goal_checks:1,negative_controls:tests.length,closed_L_axiom_certificate:part,source_nodes:compiled.source.visits,target_nodes:compiled.target.visits};
}

const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
const part=process.argv[2];
if(!part)throw Error('choose finite, stage, pairing or union');
console.log(JSON.stringify(runJ(pinned,part),null,2));
