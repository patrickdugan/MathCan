import { definition } from './constructible_definition.mjs';
import { kernel, same, inst, classProofs, compile, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';

function runG(){
  const defs=definition("v",true),p=buildF(defs,true),e=buildE(defs),c=classProofs(),out={};
  const names=["def_zero_singleton","zero_stage_rule","zero_stage_graph","one_stage_graph","L_empty","L_contains_empty"];
  function check(name,goal,proof,g=false,def=null){
    const v=kernel(0,[],proof,g,"ZF",def);
    if(!same(v.goal,goal))throw Error("goal mismatch "+name);
    out[name]={nodes:v.visits,proof_bytes:JSON.stringify(proof).length};
  }
  for(const name of names)check(name,p[name].goal,p[name].proof);
  const emptyMember=["A",[">",defs.empty,defs.L]],contains=["E",["&",defs.L,defs.empty]];
  if(!same(p.L_empty.goal,emptyMember)||!same(p.L_contains_empty.goal,contains))throw Error("independent goal mismatch");
  const empty=c.generic.find(x=>x.name==="empty"),EC=empty.premises[0];
  const guard=["eE",["closed",p.L_contains_empty.proof],EC,["eI",EC[1],0,["aI",["conv",["G",0],["aL",["h",0]]],["aR",["h",0]]]]];
  check("L_empty_closure_guard",EC,guard,true,defs.L);
  const ep=["iE",empty.proof,guard];
  check("L_empty_axiom",c.goal("empty"),ep,true,defs.L);
  const tr=e.L_transitivity_conditional,inf=p.def_inflation;
  if(!same(tr.goal[1],inf.goal))throw Error("inflation target mismatch");
  const lP=["iE",tr.proof,inf.proof];
  const T=c.generic.find(x=>x.name==="extensionality").premises[0];
  const tx=["conv",inst(defs.L,1),["aL",["h",0]]];
  const sx=["iE",["uE",["closed",lP],1],tx];
  const sy=["iE",["uE",sx,0],["aR",["h",0]]];
  const tg=["uI",["uI",["iI",["&",["G",1],["M",0,1]],["conv",["G",0],sy]]]];
  const certs=[{spec:{name:"empty"},proof:ep}];
  for(const n of ["extensionality","foundation"]){
    const g=c.generic.find(x=>x.name===n);
    if(!same(g.premises[0],T))throw Error("wrong transitivity premise");
    certs.push({spec:{name:n},proof:["iE",g.proof,tg]});
  }
  const opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:certs};
  const src=["aI",["axiom",{name:"empty"}],["aI",["axiom",{name:"extensionality"}],["axiom",{name:"foundation"}]]];
  const want=["&",c.goal("empty"),["&",c.goal("extensionality"),c.goal("foundation")]];
  const compiled=compile(0,[],src,opts);
  if(!same(compiled.target.goal,want))throw Error("composite target mismatch");
  const tests=[
    ()=>kernel(0,[],p.L_empty.proof,false,"CL"),
    ()=>kernel(0,[],guard,true,"ZF",c.def),
    ()=>kernel(0,[],["iE",empty.proof,["closed",p.L_contains_empty.proof]],true,"ZF",defs.L),
    ()=>compile(0,[],src,{...opts,certificates:certs.slice(1)}),
    ...["pairing","union","power","infinity","choice"].map(name=>()=>compile(0,[],["axiom",{name}],opts))
  ];
  for(const test of tests)if(!rejects(test))throw Error("negative control accepted");
  return {experiment:"ACE-03G",scope:"closed proofs for pinned L predicate; explicit first two stage graphs, no general transfinite recursion",proofs:out,
    closed_L_axiom_certificates:certs.map(x=>x.spec.name),independent_goal_checks:2,
    composite_source_nodes:compiled.source.visits,composite_target_nodes:compiled.target.visits,negative_controls:tests.length,
    remaining:"general stage recursion and coherence, uniform adequacy, other L axioms, proof checker soundness"};
}

console.log(JSON.stringify(runG(),null,2));
