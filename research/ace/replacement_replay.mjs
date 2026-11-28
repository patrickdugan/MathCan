import { readFileSync } from "node:fs";
import { definition } from "./constructible_definition.mjs";
import { kernel, same, expandClass, compile, rejects } from "./zf_interface.mjs";
import { buildE } from "./hierarchy_closure.mjs";
import { buildF } from "./finite_witnesses.mjs";
import { buildI } from "./stage_recursion.mjs";
import { buildL } from "./constructible_power.mjs";
import { buildDelta } from "./bounded_absoluteness.mjs";
import { buildReplacement } from "./replacement_instances.mjs";
import { compileModular } from "./modular_certificate.mjs";

// Source relation free indices: output y, input x, p0, p1, ...
// Image definition free indices: output y, domain a, p0, p1, ...
// Under the existential x, these become x,y,a,p0,p1,... .
function imageFormula(body){
  function move(p,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,move(a,d+1)];
    if(op==="M"||op==="="){
      const f=i=>i<d?i:i===d?d+1:i===d+1?d:i+1;
      return [op,f(a),f(b)];
    }
    return [op,move(a,d),move(b,d)];
  }
  return ["E",["&",["M",0,2],move(body)]];
}

function runR(pinned,part){
  const defs=definition("v",true);
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  const cases={
    identity:{params:0,body:["=",0,1]},
    singleton:{params:0,body:["&",["M",1,0],["A",[">",["M",0,1],["=",0,2]]]]},
    constant:{params:1,body:["=",0,2]},
    conditional:{params:2,body:["|",["&",["M",1,2],["=",0,3]],["&",[">",["M",1,2],["F"]],["=",0,1]]]}
  };
  const c=cases[part];if(!c)throw Error("unknown part");
  const spec={name:"replacement",...c},prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true),ranks=buildL(defs,prior,finite,stages);
  const link=buildReplacement(defs,c.body,c.params),image=imageFormula(c.body);
  const tr=prior.L_transitivity_conditional,inf=finite.def_inflation;
  if(!same(tr.goal[1],inf.goal))throw Error("inflation mismatch");
  const delta=buildDelta(defs,c.body,c.params+2);
  const dp=buildF(defs,{mode:"compiler",formula:image,params:c.params+1}).compiled_formula_definable;
  const proofByName={
    L_transitivity:{goal:tr.goal[2],proof:["iE",tr.proof,inf.proof]},
    constructible_set_stage_bound:ranks.constructible_set_stage_bound,
    ordinal_stage_value_transitive:stages.ordinal_stage_value_transitive,
    stage_members_constructible:stages.stage_members_constructible,
    definable_subset_constructible:stages.definable_subset_constructible,
    bounded_absoluteness:delta,
    image_definability:dp
  };
  const names=Object.keys(link.signatures);
  let exact=0,negative=0;
  function ok(a,b,n){if(!same(a,b))throw Error("exact formula mismatch "+n);exact++;}
  function reject(f){if(!rejects(f))throw Error("negative accepted");negative++;}
  const node=(id,deps,goal,proof,guarded=false)=>({id,deps,goal,proof,guarded});
  const graph=names.map(n=>{
    const p=proofByName[n];ok(p.goal,link.signatures[n],n);
    return node(n,[],p.goal,p.proof);
  });
  const conditional=names.reduceRight((p,n)=>[">",link.signatures[n],p],link.conclusion);
  ok(link.proof.goal,conditional,"link implication");
  graph.push(node("replacement.imp",[],conditional,link.proof.proof));
  const application=names.reduce((p,_,i)=>["iE",p,["h",i+1]],["h",0]);
  graph.push(node("replacement.pure",["replacement.imp",...names],link.conclusion,application));
  const sourceAxiom=["axiom",spec],sourceGoal=kernel(0,[],sourceAxiom,false,"ZFC").goal;
  const want=compile(0,[sourceGoal],["h",0],{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L}).target.goal;
  ok(expandClass(want,defs.L),link.conclusion,"independent source axiom expansion");
  graph.push(node("replacement.guard",["replacement.pure"],want,["conv",want,["h",0]],true));
  const source=["aI",sourceAxiom,["uI",["uE",sourceAxiom,0]]];
  const opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,nodes:graph,certificates:[{spec,node:"replacement.guard"}]};
  const out=compileModular(0,[],source,opts);
  ok(out.target.goal,["&",want,want],"repeated axiom target");
  ok(out.target.context,[],"closed target");
  // Small rejection fixtures check the exact links without repeatedly
  // expanding or replaying the large graph.
  reject(()=>kernel(0,[],link.proof.proof,false,"CL"));
  reject(()=>kernel(0,[conditional,...names.slice(1).map(n=>link.signatures[n])],application,false,"ZF"));
  reject(()=>kernel(0,[link.conclusion],["conv",want,["h",0]],true,"ZF",["=",0,0]));
  reject(()=>compileModular(0,[],source,{classDef:defs.L,nodes:[],certificates:[]}));
  return {experiment:"ACE-03R",part,spec,image_formula:image,graph:out.receipts,stats:out.stats,source_nodes:out.source.visits,exact_comparisons:exact,negative_controls:negative,pinned_L_unchanged:true,scope:"one fixed bounded Replacement instance; checked modular axiom import with repeated source leaves"};
}
const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
console.log(JSON.stringify(runR(pinned,process.argv[2]),null,2));
