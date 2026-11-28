import { readFileSync } from "node:fs";
import { kernel, same, scoped, classProofs, compile, rejects } from "./zf_interface.mjs";
import { verifyGraph, compileModular } from "./modular_certificate.mjs";
import { definition } from "./constructible_definition.mjs";
import { buildE } from "./hierarchy_closure.mjs";
import { buildF } from "./finite_witnesses.mjs";
import { buildI } from "./stage_recursion.mjs";
import { buildDelta } from "./bounded_absoluteness.mjs";
import { buildSep } from "./separation_instances.mjs";

function runQ(pinned,part){
  const defs=definition("v",true);if(!same(pinned,defs.L))throw Error("pinned L mismatch");
  const h=i=>["h",i],ax=name=>["axiom",{name}],A=p=>["A",p],E=p=>["E",p],I=(a,b)=>[">",a,b],C=(a,b)=>["&",a,b];
  let comparisons=0,negative=0;
  const ok=(a,b,n)=>{if(!same(a,b))throw Error("comparison "+n);comparisons++;};
  const reject=f=>{if(!rejects(f))throw Error("negative control accepted");negative++;};
  const node=(id,deps,goal,proof,guarded=true)=>({id,deps,goal,proof,guarded});
  const c=classProofs(),graph=[],certs=[],direct=[];
  for(let i=0;i<c.closures.length;i++){
    const p=c.closures[i];graph.push(node("closure."+i,[],p.goal,p.proof));
  }
  for(const x of c.generic){
    const ds=x.premises.map(p=>c.closures.findIndex(q=>same(p,q.goal)));
    if(ds.some(i=>i<0))continue;
    const goal=x.premises.reduceRight((a,b)=>I(b,a),c.goal(x.name)),id="generic."+x.name;
    graph.push(node(id,[],goal,x.proof));
    const deps=[id,...ds.map(i=>"closure."+i)],proof=ds.reduce((p,_,i)=>["iE",p,h(i+1)],h(0));
    graph.push(node("cert."+x.name,deps,c.goal(x.name),proof));
    certs.push({spec:{name:x.name},node:"cert."+x.name});
    direct.push({spec:{name:x.name},proof:ds.reduce((p,i)=>["iE",p,c.closures[i].proof],x.proof)});
  }
  if(part==="synthetic"){
    const opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:c.def,nodes:graph,certificates:certs};
    const empty=kernel(0,[],ax("empty"),false,"ZF").goal,union=kernel(0,[],ax("union"),false,"ZF").goal;
    const p=["M",0,0],q=["=",0,0],dis=["|",q,p];
    const ex=E(["=",0,0]),sourceCases=[
      {name:"conjunction",k:0,ctx:[],proof:["aI",ax("empty"),ax("union")]},
      {name:"duplicate_leaf",k:0,ctx:[],proof:["aI",ax("empty"),ax("empty")]},
      {name:"open_axiom",k:2,ctx:[["M",1,0]],proof:["aI",h(0),ax("foundation")]},
      {name:"local_under_binders",k:1,ctx:[p],proof:["uI",["iI",q,["aI",h(0),["aI",h(1),ax("empty")]]]]},
      {name:"existential_branch",k:1,ctx:[p],proof:["eE",ax("empty"),C(union,empty),["aI",ax("union"),["eI",empty[1],0,h(1)]]]},
      {name:"disjunction_branch",k:1,ctx:[dis],proof:["oE",h(0),["aI",["oL",h(1),p],ax("empty")],["aI",["oR",q,h(1)],ax("empty")]]},
      {name:"equality_substitution",k:2,ctx:[["=",0,1],["M",0,1]],proof:["aI",["eqS",["M",0,2],h(0),h(1)],ax("empty")]},
      {name:"classical",k:0,ctx:[],proof:["dne",["iI",I(empty,["F"]),["iE",h(0),ax("empty")]]]},
      {name:"universal_elimination",k:1,ctx:[],proof:["uE",ax("union"),0]},
      {name:"existential_introduction",k:1,ctx:[],proof:["aI",["eI",ex[1],0,["refl",0]],ax("empty")]},
      {name:"empty_context_no_axioms",k:0,ctx:[],proof:["uI",["refl",0]]}
    ],cases={};
    for(const t of sourceCases){
      const o=compileModular(t.k,t.ctx,t.proof,opts);
      const directOut=compile(t.k,t.ctx,t.proof,{sourceTheory:"ZFC",targetTheory:"ZF",classDef:c.def,certificates:direct});
      ok(o.target.goal,directOut.target.goal,t.name+" goal");
      ok(o.target.context,directOut.targetCtx,t.name+" ctx");
      cases[t.name]={source_nodes:o.source.visits,direct_target_nodes:directOut.target.visits,modular_target_nodes:o.stats.translated_nodes,conditional_nodes:o.stats.conditional_nodes,cut_nodes:o.stats.cut_nodes};
    }
    const original=verifyGraph(graph,{classDef:c.def});ok(original.goals.get("cert.empty"),c.goal("empty"),"graph output");
    const g0=graph[0],last=graph.at(-1),other={id:"unused",deps:[],goal:["F"],proof:["h",0],guarded:false};
    const bad=[
      ()=>verifyGraph([last,...graph.slice(0,-1)],{classDef:c.def}),
      ()=>verifyGraph([...graph,g0],{classDef:c.def}),
      ()=>verifyGraph([{...g0,deps:[g0.id]}],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("dupdep",[g0.id,g0.id],g0.goal,h(0))],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("unknown",["missing"],g0.goal,h(0))],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("unclosed",[],["M",0,0],h(0),false)],{classDef:c.def}),
      ()=>verifyGraph([...graph,{...other}],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("badgoal",[g0.id],["F"],h(0))],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("pure_guard",[g0.id],g0.goal,h(0),false)],{classDef:c.def}),
      ()=>verifyGraph([...graph,node("nested_closed",[g0.id],g0.goal,["closed",h(0)])],{classDef:c.def}),
      ()=>verifyGraph([node("choice",[],kernel(0,[],ax("choice"),false,"ZFC").goal,ax("choice"),false)],{classDef:c.def}),
      ()=>verifyGraph(graph,{classDef:["=",0,0]}),
      ()=>verifyGraph(graph,{classDef:c.def,targetTheory:"ZFC"}),
      ()=>verifyGraph(graph,{classDef:c.def,targetTheory:"CL"}),
      ()=>compileModular(0,[],ax("empty"),{...opts,certificates:[]}),
      ()=>compileModular(0,[],ax("empty"),{...opts,certificates:[{spec:{name:"empty"},node:"cert.union"}]}),
      ()=>compileModular(0,[],ax("empty"),{...opts,certificates:[certs[0],certs[0]]}),
      ()=>compileModular(0,[],ax("choice"),opts),
      ()=>compileModular(0,[],["h",0],opts),
      ()=>verifyGraph([{...g0,id:""}],{classDef:c.def}),
      ()=>verifyGraph([{...g0,ignored:true}],{classDef:c.def})
    ];for(const b of bad)reject(b);
    // An iterator mutates the first input goal after it was checked.
    // The checker must use its own saved theorem, not the changed AST.
    const ident=A(["=",0,0]),mutable=JSON.parse(JSON.stringify(ident));
    function* mutating(){yield node("a",[],mutable,["uI",["refl",0]],false);mutable[1][0]="M";yield node("b",["a"],ident,h(0),false);}
    const snapshot=verifyGraph(mutating());ok(snapshot.goals.get("b"),ident,"snapshot");
    return {experiment:"ACE-03Q",part,graph:original.receipts,cases,exact_comparisons:comparisons,negative_controls:negative,pinned_L_unchanged:true,scope:"singleton-empty-class graph and arbitrary source-rule regression"};
  }
  if(part!=="bounded")throw Error("unknown replay part");
  const prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true),phi=["M",0,1];
  const dp=buildF(defs,{mode:"compiler",formula:["&",["M",0,1],["M",0,2]],params:2}).compiled_formula_definable;
  const delta=buildDelta(defs,phi,2),p0=buildSep(defs,stages,phi,1,dp,delta),spec={name:"separation",params:1,body:phi};
  // Independent relativized formula is generated by the existing compiler
  // in its ordinary hypothesis mode.
  const sourceGoal=kernel(0,[],["axiom",spec],false,"ZFC").goal;
  const want=compile(0,[sourceGoal],h(0),{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L}).target.goal;
  const g=[node("pure.separation",[],p0.goal,p0.proof,false),node("cert.separation",["pure.separation"],want,["conv",want,h(0)])];
  const proof=["aI",["axiom",spec],["uI",["iI",["=",0,0],["aI",h(0),["axiom",spec]]]]];
  const out=compileModular(0,[],proof,{classDef:defs.L,nodes:g,certificates:[{spec,node:"cert.separation"}]});
  const baseline=compile(0,[],proof,{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[{spec,proof:["conv",want,["closed",p0.proof]]}]});
  ok(out.target.goal,baseline.target.goal,"pinned L separation goal");ok(out.target.context,baseline.targetCtx,"pinned L external context");
  reject(()=>compileModular(0,[],proof,{classDef:defs.L,nodes:g.slice(1),certificates:[{spec,node:"cert.separation"}]}));
  reject(()=>compileModular(0,[],proof,{classDef:defs.L,nodes:g,certificates:[]}));
  return {experiment:"ACE-03Q",part,spec,graph:out.receipts,stats:out.stats,source_nodes:out.source.visits,direct_target_nodes:baseline.target.visits,exact_comparisons:comparisons,negative_controls:negative,pinned_L_unchanged:true,scope:"pinned L bounded Separation DAG imported in a repeated-axiom source proof"};
}
const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
console.log(JSON.stringify(runQ(pinned,process.argv[2]),null,2));
