import { readFileSync } from "node:fs";
import { definition } from "./constructible_definition.mjs";
import { kernel, same, expandClass, compile, rejects } from "./zf_interface.mjs";
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
import { buildReplacement } from "./replacement_instances.mjs";
import { compileModular } from "./modular_certificate.mjs";

function runS(pinned,part){
  const defs=definition("v",true),phi=["A",[">",["M",2,0],["M",1,0]]],spec={name:"replacement",params:0,body:phi};
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  const link=buildLink(defs,phi,2),rep=buildReplacement(defs,phi,0,true);
  if(!same(link.conclusion,rep.signatures.reflection))throw Error("reflection interface");
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],h=i=>["h",i];
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){const f=i=>i<d?i:indices[i-d]+d;return [op,f(a),f(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  function rel(p){
    const [op,a,b]=p;
    if(op==="A")return A(I(defs.L,rel(a)));
    if(op==="E")return E(C(defs.L,rel(a)));
    if(["&","|",">"].includes(op))return [op,rel(a),rel(b)];
    return p;
  }
  const Ord=a=>embed(defs.ordinal,[a]),Succ=(a,b)=>embed(defs.successor,[a,b]),W=(b,r)=>E(C(Succ(b+1,0),E(C(embed(defs.stageGraph,[0,1]),embed(defs.val,[0,b+2,r+2])))));
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  if(link.clauses.length!==1||link.clauses[0].arity!==2||link.clauses[0].kind!=="counterexample"||!same(link.clauses[0].body,[">",phi[1],["F"]]))throw Error("clause fixture");
  const p0=embed(rel(link.clauses[0].body),[0,2,1]);
  let clause=I(E(C(defs.L,p0)),E(C(M(0,3),p0)));
  for(let i=1;i>=0;i--)clause=A(I(M(0,3+i),clause));
  const ext=A(A(I(Ord(1),I(W(1,0),E(E(C(C(C(Ord(1),W(1,0)),M(3,1)),C(sub(2,0),clause))))))));
  const ax=["axiom",spec],sourceGoal=kernel(0,[],ax,false,"ZFC").goal;
  const want=compile(0,[sourceGoal],h(0),{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L}).target.goal;
  if(!same(expandClass(want,defs.L),rep.conclusion))throw Error("independent schema expansion mismatch");
  // Every graph node has an independently constructed expected interface.
  const reflectionDeps=["selector.total","selector.strict","omega.range","limit.reflection","omega.exists","omega.ordinal","stage.members","transport"];
  const repNames=Object.keys(rep.signatures),repDeps=repNames.map(n=>n==="stage_members_constructible"?"stage.members":n);
  const expected={
    "extension":ext,
    "selector.conditional":I(ext,link.signatures.canonical_extension_total),
    "selector.strict":link.signatures.canonical_extension_strict,
    "selector.total":link.signatures.canonical_extension_total,
    "omega.range":link.signatures.omega_range_closed_conditional,
    "limit.reflection":link.signatures.range_implies_reflecting_stage,
    "omega.exists":link.signatures.omega_exists,
    "omega.ordinal":link.signatures.omega_ordinal,
    "stage.members":link.signatures.stage_members_constructible,
    "transport":link.signatures.conditional_transport,
    "reflection.imp":Object.values(link.signatures).reduceRight((q,p)=>I(p,q),link.conclusion),
    "reflection":link.conclusion,
    ...Object.fromEntries(repNames.filter(n=>n!=="reflection"&&n!=="stage_members_constructible").map(n=>[n,rep.signatures[n]])),
    "replacement.imp":Object.values(rep.signatures).reduceRight((q,p)=>I(p,q),rep.conclusion),
    "replacement.pure":rep.conclusion,
    "replacement.guard":want
  };
  if(!same(expected["stage.members"],rep.signatures.stage_members_constructible))throw Error("shared stage interface");
  const node=(id,deps,proof,guarded=false)=>({id,deps,goal:expected[id],proof,guarded});
  function closed(id,p){
    if(!same(p.goal,expected[id]))throw Error("exact interface "+id);
    return node(id,[],p.proof);
  }
  function cut(id,conditional,deps){return node(id,[conditional,...deps],deps.reduce((p,_,i)=>["iE",p,h(i+1)],h(0)));}
  let prior,finite,stages,ranks;
  function init(needRanks=false){
    if(!prior){prior=buildE(defs,true);finite=buildF(defs);stages=buildI(defs,prior,finite,true);}
    if(needRanks&&!ranks)ranks=buildL(defs,prior,finite,stages);
  }
  function* generate(which){
    if(which==="links"){
      yield closed("reflection.imp",link.proof);
      yield cut("reflection","reflection.imp",reflectionDeps);
      yield closed("replacement.imp",rep.proof);
      yield cut("replacement.pure","replacement.imp",repDeps);
      yield node("replacement.guard",["replacement.pure"],["conv",want,h(0)],true);
      return;
    }
    init(["extension","selector","limit","replacement"].includes(which));
    if(which==="extension"){
      const c=link.clauses[0],p=buildM(defs,prior,stages,ranks,c.body,c.arity,true,["strict_stage_witness_extension"]).strict_stage_witness_extension;
      yield closed("extension",p);
    }else if(which==="selector"){
      const n=buildN(defs,prior,stages,ranks,link.clauses);
      if(!same(n.nextFormula,link.nextFormula))throw Error("selector step mismatch");
      yield closed("selector.conditional",n.proofs.canonical_extension_total_conditional);
      yield closed("selector.strict",n.proofs.canonical_extension_strict);
      yield cut("selector.total","selector.conditional",["extension"]);
    }else if(which==="omega"){
      const o=buildOmega(defs,prior,stages,buildF(defs,"relations"),link.nextFormula,["omega_range_closed_conditional"]);
      yield closed("omega.range",o.proofs.omega_range_closed_conditional);
    }else if(which==="limit"){
      const n=buildN(defs,prior,stages,ranks,link.clauses),k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["ordinal_limit_stage_members"]);
      if(!same(n.nextFormula,link.nextFormula))throw Error("limit step mismatch");
      const p=buildLimit(defs,prior,stages,ranks,link.clauses,n.nextFormula,n.proofs.canonical_extension_strict,k.ordinal_limit_stage_members,["range_implies_reflecting_stage"],true);
      yield closed("limit.reflection",p.proofs.range_implies_reflecting_stage);
    }else if(which==="base"){
      const k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["omega_ordinal"]);
      yield closed("omega.exists",finite.omega_exists);
      yield closed("omega.ordinal",k.omega_ordinal);
      yield closed("stage.members",stages.stage_members_constructible);
      const tv=buildTV(defs,phi,2);
      if(!same(tv.clauses,link.clauses))throw Error("transport clauses mismatch");
      yield closed("transport",tv);
    }else if(which==="replacement"){
      const tr=prior.L_transitivity_conditional,inf=finite.def_inflation;
      if(!same(tr.goal[1],inf.goal))throw Error("inflation mismatch");
      yield closed("L_transitivity",{goal:tr.goal[2],proof:["iE",tr.proof,inf.proof]});
      yield closed("constructible_set_stage_bound",ranks.constructible_set_stage_bound);
      for(const n of ["ordinal_stage_value_transitive","definable_subset_constructible","ordinal_stage_value_monotone"])yield closed(n,stages[n]);
      // Free output y, parameter a. Under exists x, the environment
      // is x,y,a; under forall z, it is z,x,y,a.
      const image=["E",["&",["M",0,2],["A",[">",["M",1,0],["M",2,0]]]]];
      const dp=buildF(defs,{mode:"compiler",formula:image,params:1}).compiled_formula_definable;
      yield closed("image_definability",dp);
    }else throw Error("unknown part");
  }
  const parts=["extension","selector","omega","limit","base","replacement","links"];
  const source=["aI",ax,["uI",["uE",ax,0]]],target=["&",want,want];
  if(part==="full"){
    function* graph(){for(const p of parts)yield* generate(p);}
    const out=compileModular(0,[],source,{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,nodes:graph(),certificates:[{spec,node:"replacement.guard"}]});
    if(!same(out.target.goal,target)||!same(out.target.context,[]))throw Error("full modular target mismatch");
    if(out.receipts.length!==Object.keys(expected).length)throw Error("full graph node coverage");
    return {experiment:"ACE-03S",part,spec,graph:out.receipts,stats:out.stats,source_nodes:out.source.visits,exact_target:true,pinned_L_unchanged:true,scope:"complete streamed modular import of fixed unbounded Replacement"};
  }
  if(!parts.includes(part))throw Error("unknown part");
  // Split replay: the entire interface is reconstructed for each part.
  // Nonempty contexts are discharged by the separately checked closed
  // graph nodes in topological order, not by treating receipts as proofs.
  const checks=[];let negative=0;
  function reject(fn){if(!rejects(fn))throw Error("negative control accepted");negative++;}
  for(const n of generate(part)){
    const ctx=n.deps.map(id=>expected[id]),r=kernel(0,ctx,n.proof,n.guarded,"ZF",n.guarded?defs.L:null);
    if(!same(r.goal,n.goal))throw Error("kernel result "+n.id);
    checks.push({id:n.id,nodes:r.visits,dependencies:n.deps,goal_bytes:JSON.stringify(n.goal).length});
    if(n.deps.length)reject(()=>kernel(0,ctx.slice(1),n.proof,n.guarded,"ZF",n.guarded?defs.L:null));
    if(n.id==="extension")reject(()=>kernel(0,[],n.proof,false,"CL"));
    if(n.id==="replacement.guard")reject(()=>kernel(0,ctx,n.proof,true,"ZF",["=",0,0]));
  }
  let translation=null;
  if(part==="links"){
    // Check the original source and the translation using a closed
    // axiom hypothesis, then discharge it by the verified graph cut.
    const sr=kernel(0,[],source,false,"ZFC");
    const rewritten=["aI",h(0),["uI",["uE",h(0),0]]];
    if(!same(kernel(0,[sourceGoal],rewritten,false,"ZFC").goal,sr.goal))throw Error("source rewrite mismatch");
    const t=compile(0,[sourceGoal],rewritten,{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L});
    if(!same(t.targetCtx,[want])||!same(t.target.goal,target))throw Error("translation interface mismatch");
    const cond=kernel(0,[],["iI",want,t.proof],true,"ZF",defs.L);
    const cut=kernel(0,[want,cond.goal],["iE",h(1),h(0)],true,"ZF",defs.L);
    if(!same(cut.goal,target))throw Error("final cut mismatch");
    reject(()=>compileModular(0,[],source,{classDef:defs.L,nodes:[],certificates:[]}));
    translation={source_nodes:sr.visits,translated_nodes:t.target.visits,conditional_nodes:cond.visits,cut_nodes:cut.visits};
  }
  return {experiment:"ACE-03S",part,spec,checks,exact_node_goals:checks.length,negative_controls:negative,translation,pinned_L_unchanged:true,scope:"split checked node proofs and exact interfaces for fixed unbounded Replacement; full streamed importer is a separate replay"};
}
const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
console.log(JSON.stringify(runS(pinned,process.argv[2]),null,2));
