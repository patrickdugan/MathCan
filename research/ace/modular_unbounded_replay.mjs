import { readFileSync } from "node:fs";
import { definition } from "./constructible_definition.mjs";
import { kernel, same, expandClass, compile } from "./zf_interface.mjs";
import { verifyGraph, compileModular } from "./modular_certificate.mjs";
import { buildE } from "./hierarchy_closure.mjs";
import { buildF } from "./finite_witnesses.mjs";
import { buildI } from "./stage_recursion.mjs";
import { buildL } from "./constructible_power.mjs";
import { buildK } from "./constructible_infinity.mjs";
import { buildM } from "./reflection_bounds.mjs";
import { buildN } from "./reflection_iteration.mjs";
import { buildOmega } from "./omega_iteration.mjs";
import { buildLimit } from "./reflection_limit.mjs";
import { buildTV } from "./reflection_transport.mjs";
import { buildLink } from "./reflection_link.mjs";
import { buildUnboundedSep } from "./unbounded_separation.mjs";

function runUnboundedQ(pinned){
  const defs=definition("v",true),phi=["&",["E",["M",1,0]],["E",["M",0,1]]],spec={name:"separation",params:0,body:phi};
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  const link=buildLink(defs,phi,1),sep=buildUnboundedSep(defs,phi,0);
  if(!same(link.conclusion,sep.signatures.reflection))throw Error("reflection interface mismatch");
  const h=i=>["h",i],I=(a,b)=>[">",a,b];
  const node=(id,deps,goal,proof,guarded=false)=>({id,deps,goal,proof,guarded});
  function closed(id,p,want=p.goal){
    if(!same(p.goal,want))throw Error("exact interface mismatch "+id);
    return node(id,[],want,p.proof);
  }
  function cut(id,conditional,deps,goal){
    const proof=deps.reduce((p,_,i)=>["iE",p,h(i+1)],h(0));
    return node(id,[conditional,...deps],goal,proof);
  }
  const ax=["axiom",spec],sourceGoal=kernel(0,[],ax,false,"ZFC").goal;
  const want=compile(0,[sourceGoal],h(0),{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L}).target.goal;
  if(!same(expandClass(want,defs.L),sep.conclusion))throw Error("exact Separation axiom mismatch");
  function* graph(){
    const prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true),ranks=buildL(defs,prior,finite,stages);
    const extGoals=[];
    for(let i=0;i<link.clauses.length;i++){
      const c=link.clauses[i],p=buildM(defs,prior,stages,ranks,c.body,c.arity,true,["strict_stage_witness_extension"]).strict_stage_witness_extension;
      extGoals.push(p.goal);
      yield closed("extension."+i,p);
    }
    // Keep the shared theorem interfaces, not expanded copies of their
    // proofs, in the graph. Each generator result is verified at yield.
    const n=buildN(defs,prior,stages,ranks,link.clauses);
    if(!same(n.nextFormula,link.nextFormula))throw Error("step formula mismatch");
    yield closed("selector.conditional",n.proofs.canonical_extension_total_conditional,extGoals.reduceRight((a,b)=>I(b,a),link.signatures.canonical_extension_total));
    yield closed("selector.strict",n.proofs.canonical_extension_strict,link.signatures.canonical_extension_strict);
    yield cut("selector.total","selector.conditional",extGoals.map((_,i)=>"extension."+i),link.signatures.canonical_extension_total);
    {
      const o=buildOmega(defs,prior,stages,buildF(defs,"relations"),link.nextFormula,["omega_range_closed_conditional"]);
      yield closed("omega.range",o.proofs.omega_range_closed_conditional,link.signatures.omega_range_closed_conditional);
    }
    {
      const k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["ordinal_limit_stage_members","omega_ordinal"]);
      const p=buildLimit(defs,prior,stages,ranks,link.clauses,n.nextFormula,n.proofs.canonical_extension_strict,k.ordinal_limit_stage_members,["range_implies_reflecting_stage"],true);
      yield closed("limit.reflection",p.proofs.range_implies_reflecting_stage,link.signatures.range_implies_reflecting_stage);
      yield closed("omega.ordinal",k.omega_ordinal,link.signatures.omega_ordinal);
    }
    yield closed("omega.exists",finite.omega_exists,link.signatures.omega_exists);
    yield closed("stage.members",stages.stage_members_constructible,link.signatures.stage_members_constructible);
    {
      const tv=buildTV(defs,phi,1);
      if(!same(tv.clauses,link.clauses))throw Error("clause extraction mismatch");
      yield closed("transport",tv,link.signatures.conditional_transport);
    }
    const reflectionDeps=["selector.total","selector.strict","omega.range","limit.reflection","omega.exists","omega.ordinal","stage.members","transport"];
    yield closed("reflection.imp",link.proof,Object.values(link.signatures).reduceRight((a,b)=>I(b,a),link.conclusion));
    yield cut("reflection","reflection.imp",reflectionDeps,link.conclusion);
    const stageNames=["common_constructible_stage","ordinal_stage_value_monotone","ordinal_stage_value_transitive","definable_subset_constructible"];
    for(const name of stageNames)yield closed(name,stages[name],sep.signatures[name]);
    {
      const d=buildF(defs,{mode:"compiler",formula:["&",["M",0,1],phi],params:1}).compiled_formula_definable;
      yield closed("subset_definability",d,sep.signatures.subset_definability);
    }
    yield closed("separation.imp",sep.proof,Object.values(sep.signatures).reduceRight((a,b)=>I(b,a),sep.conclusion));
    yield cut("separation.pure","separation.imp",[...stageNames,"reflection","subset_definability"],sep.conclusion);
    yield node("separation.guard",["separation.pure"],want,["conv",want,h(0)],true);
  }
  // Two source leaves, including one under a quantifier, must resolve
  // to the same checked DAG certificate. No original direct import.
  const source=["aI",ax,["uI",["uE",ax,0]]];
  const out=compileModular(0,[],source,{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,nodes:graph(),certificates:[{spec,node:"separation.guard"}]});
  if(!same(out.target.goal,["&",want,want])||!same(out.target.context,[]))throw Error("final exact target mismatch");
  return {experiment:"ACE-03Q",part:"unbounded",spec,graph:out.receipts,stats:out.stats,source_nodes:out.source.visits,exact_target:true,pinned_L_unchanged:true,scope:"complete streamed proof DAG for fixed unbounded Separation and repeated source-axiom translation"};
}
const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
console.log(JSON.stringify(runUnboundedQ(pinned),null,2));
