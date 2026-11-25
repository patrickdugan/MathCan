import { readFileSync } from 'node:fs';
import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects, expandClass, classProofs, compile } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
import { buildL } from './constructible_power.mjs';
import { buildK } from './constructible_infinity.mjs';
import { buildM } from './reflection_bounds.mjs';
import { buildN } from './reflection_iteration.mjs';
import { buildOmega } from './omega_iteration.mjs';
import { buildLimit } from './reflection_limit.mjs';
import { buildTV } from './reflection_transport.mjs';
import { buildLink } from './reflection_link.mjs';
import { buildUnboundedSep } from './unbounded_separation.mjs';

function runP(pinned,part){
  const defs=definition("v",true),phi=["&",["E",["M",1,0]],["E",["M",0,1]]],link=buildLink(defs,phi,1),sep=buildUnboundedSep(defs,phi,0),proofs={};
  if(!same(pinned,defs.L)||!same(link.conclusion,sep.signatures.reflection))throw Error("pinned formula or reflection interface mismatch");
  let exact=1,rejections=0;
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],B=(p,q)=>C(I(p,q),I(q,p)),G=i=>["G",i];
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
  function guard(p){
    const [op,a,b]=p;
    if(op==="A")return A(I(G(0),guard(a)));
    if(op==="E")return E(C(G(0),guard(a)));
    if(["&","|",">"].includes(op))return [op,guard(a),guard(b)];
    return p;
  }
  const Ord=a=>embed(defs.ordinal,[a]),Succ=(a,b)=>embed(defs.successor,[a,b]),W=(b,r)=>E(C(Succ(b+1,0),E(C(embed(defs.stageGraph,[0,1]),embed(defs.val,[0,b+2,r+2])))));
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  function expectedExtension(c){
    if(c.arity!==1)throw Error("fixture arity");
    const p=rel(c.body),clause=A(I(M(0,3),I(E(C(defs.L,p)),E(C(M(0,2),p)))));
    return A(A(I(Ord(1),I(W(1,0),E(E(C(C(C(Ord(1),W(1,0)),M(3,1)),C(sub(2,0),clause))))))));
  }
  const extensions=link.clauses.map(expectedExtension);
  function check(name,p,policy="ZF",want=null,measure=true){
    const r=kernel(0,[],p.proof,false,policy);
    if(!same(r.goal,p.goal))throw Error("proof goal "+name);
    if(want!==null){if(!same(r.goal,want))throw Error("interface mismatch "+name);exact++;}
    proofs[name]={nodes:r.visits,goal_bytes:JSON.stringify(r.goal).length};
    if(measure)proofs[name].proof_bytes=JSON.stringify(p.proof).length;
  }
  function reject(fn){if(!rejects(fn))throw Error("negative control accepted");rejections++;}
  function applyLink(name,conditional,antecedents,conclusion,policy="logic"){
    const expected=antecedents.reduceRight((p,q)=>I(q,p),conclusion);
    if(!same(conditional,expected))throw Error("link statement mismatch "+name);
    const application=antecedents.reduce((p,_,i)=>["iE",p,["h",i+1]],["h",0]);
    const out=kernel(0,[conditional,...antecedents],application,false,policy);
    if(!same(out.goal,conclusion))throw Error("link conclusion "+name);
    exact++;proofs[name]={nodes:out.visits,dependencies:antecedents.length};
    reject(()=>kernel(0,[conditional,...antecedents.slice(1)],application,false,policy));
  }
  const spec={name:"separation",params:0,body:phi};
  if(part==="links"){
    const sigs=Object.values(link.signatures),sepSigs=Object.values(sep.signatures);
    check("reflection_implication",link.proof,"logic",sigs.reduceRight((p,q)=>I(q,p),link.conclusion));
    applyLink("reflection_cut",link.proof.goal,sigs,link.conclusion);
    check("separation_implication",sep.proof,"ZF",sepSigs.reduceRight((p,q)=>I(q,p),sep.conclusion));
    applyLink("separation_cut",sep.proof.goal,sepSigs,sep.conclusion);
    const source=kernel(0,[],["axiom",spec],false,"ZFC"),want=guard(source.goal);
    if(!same(expandClass(want,defs.L),sep.conclusion))throw Error("exact relativized schema goal mismatch");
    exact++;
    const conv=["conv",want,["h",0]],conversion=kernel(0,[sep.conclusion],conv,true,"ZF",defs.L);
    if(!same(conversion.goal,want))throw Error("guard conversion");
    exact++;proofs.guard_conversion={nodes:conversion.visits};
    const translated=compile(0,[source.goal],["h",0],{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L});
    if(!same(translated.targetCtx,[want])||!same(translated.target.goal,want))throw Error("compiler context translation mismatch");
    exact++;proofs.compiler_context_translation={source_nodes:translated.source.visits,target_nodes:translated.target.visits,dependencies:1};
    // This is a cut with the exact derived guard formula, not a direct
    // expanded certificate import into compile's original tree interface.
    const cut=kernel(0,[sep.conclusion],["iE",["iI",want,translated.proof[0]==="h"?["h",1]:(()=>{throw Error("unexpected translated proof")})()],conv],true,"ZF",defs.L);
    if(!same(cut.goal,want))throw Error("final guarded cut");
    exact++;proofs.final_guarded_cut={nodes:cut.visits};
    reject(()=>kernel(0,[],conv,true,"ZF",defs.L));
    reject(()=>kernel(0,[sep.conclusion],conv,true,"ZF",classProofs().def));
    reject(()=>compile(0,[],["axiom",spec],{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[]}));
    return {experiment:"ACE-03P",part,spec,proofs,exact_interfaces:exact,negative_controls:rejections,pinned_L_unchanged:true,scope:"checked modular implication and context-translation links; all closed dependencies checked in other replay parts; no monolithic certificate import"};
  }
  const prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true);
  if(part==="base"){
    const k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["omega_ordinal"]),tv=buildTV(defs,phi,1);
    check("omega_exists",finite.omega_exists,"ZF",link.signatures.omega_exists);
    check("omega_ordinal",k.omega_ordinal,"ZF",link.signatures.omega_ordinal);
    check("stage_members_constructible",stages.stage_members_constructible,"ZF",link.signatures.stage_members_constructible);
    check("conditional_transport",tv,"CL",link.signatures.conditional_transport);
    if(!same(tv.clauses,link.clauses))throw Error("clause extraction mismatch");
    exact++;
  }else if(part==="separation"){
    for(const name of ["common_constructible_stage","ordinal_stage_value_monotone","ordinal_stage_value_transitive","definable_subset_constructible"])check(name,stages[name],"ZF",sep.signatures[name]);
    // Parameter-free source formula: insert separating-set parameter at slot 1.
    const compiled=C(M(0,1),phi),d=buildF(defs,{mode:"compiler",formula:compiled,params:1}).compiled_formula_definable;
    check("subset_definability",d,"ZF",sep.signatures.subset_definability);
    reject(()=>kernel(0,[],d.proof,false,"CL"));
  }else if(part==="omega"){
    const o=buildOmega(defs,prior,stages,buildF(defs,"relations"),link.nextFormula,["omega_range_closed_conditional"]);
    check("omega_range_closed_conditional",o.proofs.omega_range_closed_conditional,"ZF",link.signatures.omega_range_closed_conditional,false);
  }else{
    const ranks=buildL(defs,prior,finite,stages);
    if(part==="left"||part==="right"){
      const i=part==="left"?0:1,cl=link.clauses[i],p=buildM(defs,prior,stages,ranks,cl.body,cl.arity,true,["strict_stage_witness_extension"]).strict_stage_witness_extension;
      check("strict_stage_witness_extension",p,"ZF",extensions[i]);
      reject(()=>kernel(0,[],p.proof,false,"CL"));
    }else if(part==="selector"){
      const n=buildN(defs,prior,stages,ranks,link.clauses);
      if(!same(n.nextFormula,link.nextFormula))throw Error("canonical step mismatch");
      exact++;
      const p=n.proofs.canonical_extension_total_conditional,expected=extensions.reduceRight((a,b)=>I(b,a),link.signatures.canonical_extension_total);
      check("canonical_extension_total_conditional",p,"ZF",expected);
      check("canonical_extension_strict",n.proofs.canonical_extension_strict,"ZF",link.signatures.canonical_extension_strict);
      applyLink("canonical_total_cut",p.goal,extensions,link.signatures.canonical_extension_total);
      reject(()=>kernel(0,[p.goal,...extensions.slice().reverse()],["iE",["iE",["h",0],["h",1]],["h",2]],false,"logic"));
    }else if(part==="limit"){
      const n=buildN(defs,prior,stages,ranks,link.clauses),k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["ordinal_limit_stage_members"]);
      if(!same(n.nextFormula,link.nextFormula))throw Error("canonical step mismatch");
      exact++;
      const p=buildLimit(defs,prior,stages,ranks,link.clauses,n.nextFormula,n.proofs.canonical_extension_strict,k.ordinal_limit_stage_members,["range_implies_reflecting_stage"]);
      check("range_implies_reflecting_stage",p.proofs.range_implies_reflecting_stage,"ZF",link.signatures.range_implies_reflecting_stage,false);
    }else throw Error("unknown replay part");
  }
  return {experiment:"ACE-03P",part,spec,proofs,exact_interfaces:exact,negative_controls:rejections,pinned_L_unchanged:true,scope:"checked dependency or link for one fixed unbounded Separation instance; unrestricted schema remains open"};
}
const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
console.log(JSON.stringify(runP(pinned,process.argv[2]),null,2));
