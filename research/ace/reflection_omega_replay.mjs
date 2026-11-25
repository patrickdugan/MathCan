import { readFileSync } from 'node:fs';
import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
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

function runN(pinned,part){
  const defs=definition("v",true),formula=["E",["M",0,1]],link=buildLink(defs,formula,1),out={};
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  let exactInterfaces=0,controls=0;
  function check(n,p,policy="ZF",want=null,measure=false){
    const r=kernel(0,[],p.proof,false,policy);
    if(!same(r.goal,p.goal))throw Error("proof goal mismatch "+n);
    if(want!==null){if(!same(p.goal,want))throw Error("interface mismatch "+n);exactInterfaces++;}
    out[n]={nodes:r.visits,goal_bytes:JSON.stringify(p.goal).length};
    if(measure)out[n].proof_bytes=JSON.stringify(p.proof).length;
  }
  function reject(fn){if(!rejects(fn))throw Error("negative control accepted");controls++;}
  if(part==="link"){
    const deps=Object.values(link.signatures),expected=deps.reduceRight((p,q)=>[">",q,p],link.conclusion);
    check("reflection_link_implication",link.proof,"logic",expected,true);
    const app=deps.reduce((p,_,i)=>["iE",p,["h",i+1]],["h",0]);
    const r=kernel(0,[expected,...deps],app,false,"logic");
    if(!same(r.goal,link.conclusion))throw Error("linked conclusion mismatch");
    // Independently construct the final statement for exists x, x in p.
    const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],B=(p,q)=>C(I(p,q),I(q,p));
    function embed(p,indices,d=0){const [op,a,b]=p;if(op==="F")return p;if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];if(op==="M"||op==="="){const f=i=>i<d?i:indices[i-d]+d;return [op,f(a),f(b)];}return [op,embed(a,indices,d),embed(b,indices,d)];}
    const Ord=b=>embed(defs.ordinal,[b]),Succ=(b,d)=>embed(defs.successor,[b,d]),W=(b,r)=>E(C(Succ(b+1,0),E(C(embed(defs.stageGraph,[0,1]),embed(defs.val,[0,b+2,r+2])))));
    const agree=A(I(M(0,1),B(E(C(M(0,2),M(0,1))),E(C(defs.L,M(0,1))))));
    const want=A(I(Ord(0),E(E(C(C(C(Ord(1),W(1,0)),M(2,1)),agree)))));
    if(!same(want,r.goal))throw Error("independent reflection goal mismatch");
    exactInterfaces++;
    reject(()=>kernel(0,[expected,...deps.slice(1)],app,false,"logic"));
    reject(()=>kernel(0,[expected,...deps.slice().reverse()],app,false,"logic"));
    return {experiment:"ACE-03N",part,proofs:out,exact_interfaces:exactInterfaces,negative_controls:controls,link_applications:deps.length,conclusion_bytes:JSON.stringify(r.goal).length,pinned_L_unchanged:true,scope:"logical link only; all eight dependencies separately verified by other replay parts"};
  }
  const prior=buildE(defs,true),finite=buildF(defs),stages=buildI(defs,prior,finite,true);
  if(part==="base"){
    const k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["omega_ordinal"]);
    const tv=buildTV(defs,formula,1);
    check("omega_exists",finite.omega_exists,"ZF",link.signatures.omega_exists,true);
    check("omega_ordinal",k.omega_ordinal,"ZF",link.signatures.omega_ordinal,true);
    check("stage_members_constructible",stages.stage_members_constructible,"ZF",link.signatures.stage_members_constructible,true);
    check("conditional_transport",tv,"CL",link.signatures.conditional_transport,true);
    if(!same(tv.clauses,link.clauses))throw Error("clause extraction mismatch");
  }else if(part==="omega"){
    const o=buildOmega(defs,prior,stages,buildF(defs,"relations"),link.nextFormula,["omega_range_closed_conditional"]);
    check("omega_range_closed_conditional",o.proofs.omega_range_closed_conditional,"ZF",link.signatures.omega_range_closed_conditional);
  }else if(part==="recurrence"){
    // Small formula fixture: the conditional theorem is valid even
    // for a relation which fails the functionality antecedent.
    const o=buildOmega(defs,prior,stages,buildF(defs,"relations"),["M",1,0]);
    for(const [n,p] of Object.entries(o.proofs))check(n,p,"ZF",null,true);
    reject(()=>kernel(0,[],o.proofs.omega_range_closed_conditional.proof,false,"CL"));
    reject(()=>buildOmega(defs,prior,stages,finite,["M",0,2]));
  }else{
    const ranks=buildL(defs,prior,finite,stages);
    if(part==="canonical"){
      const cl=link.clauses[0],b=buildM(defs,prior,stages,ranks,cl.body,cl.arity,true,["strict_stage_witness_extension"]).strict_stage_witness_extension;
      const p=buildN(defs,prior,stages,ranks,link.clauses,[b]);
      if(!same(p.nextFormula,link.nextFormula))throw Error("next formula mismatch");
      check("canonical_extension_total",p.proofs.canonical_extension_total,"ZF",link.signatures.canonical_extension_total,true);
      check("canonical_extension_strict",p.proofs.canonical_extension_strict,"ZF",link.signatures.canonical_extension_strict,true);
      reject(()=>kernel(0,[],p.proofs.canonical_extension_total.proof,false,"CL"));
    }else if(part==="limit"){
      const n=buildN(defs,prior,stages,ranks,link.clauses),k=buildK(defs,prior,buildF(defs,"infinity"),stages,false,["ordinal_limit_stage_members"]);
      if(!same(n.nextFormula,link.nextFormula))throw Error("next formula mismatch");
      const p=buildLimit(defs,prior,stages,ranks,link.clauses,n.nextFormula,n.proofs.canonical_extension_strict,k.ordinal_limit_stage_members);
      check("successor_closed_range_limit",p.proofs.successor_closed_range_limit,"ZF",null,true);
      check("range_implies_reflecting_stage",p.proofs.range_implies_reflecting_stage,"ZF",link.signatures.range_implies_reflecting_stage,true);
    }else if(part==="two_clause"){
      const two=buildLink(defs,["&",["E",["M",0,1]],["E",["M",1,0]]],1);
      const n=buildN(defs,prior,stages,ranks,two.clauses);
      if(!same(n.nextFormula,two.nextFormula))throw Error("two-clause next mismatch");
      const expected=n.proofs.canonical_extension_total_conditional.goal[2][2];
      if(!same(expected,two.signatures.canonical_extension_total))throw Error("conditional consequent mismatch");
      for(const [name,p] of Object.entries(n.proofs))check(name,p,"ZF",name==="canonical_extension_strict"?two.signatures.canonical_extension_strict:null,true);
      reject(()=>buildN(defs,prior,stages,ranks,[]));
    }else throw Error("unknown replay part");
  }
  return {experiment:"ACE-03N",part,proofs:out,exact_interfaces:exactInterfaces,negative_controls:controls,pinned_L_unchanged:true,scope:part==="two_clause"?"conditional two-clause selector; no unconditional two-clause reflection":part==="recurrence"?"conditional finite-history recurrence fixture":"closed proof module for one fixed reflection example"};
}

const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
console.log(JSON.stringify(runN(pinned,process.argv[2]),null,2));
