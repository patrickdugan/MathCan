import { readFileSync } from "node:fs";
import { definition } from "./constructible_definition.mjs";
import { same, scoped, inst, kernel, expandClass, classProofs, rejects, compile } from "./zf_interface.mjs";

function gate(def,pinned){
  const insist=(x,msg)=>{if(!x)throw Error(msg);};
  insist(same(def,pinned)&&scoped(def,1,false),"pinned definition");
  let conversions=0;
  for(let k=1;k<=4;k++)for(let i=0;i<k;i++){
    const p=inst(def,i),g=["G",i],a=kernel(k,[p],["conv",g,["h",0]],true,"ZF",def);
    insist(same(a.goal,g),"definition introduction");conversions++;
    const b=kernel(k,[g],["conv",p,["h",0]],true,"ZF",def);
    insist(same(b.goal,p),"definition elimination");conversions++;
  }
  let binderChecks=0;
  for(let depth=0;depth<=4;depth++){
    let p=["G",depth],q=inst(def,depth);
    for(let i=0;i<depth;i++){p=["A",p];q=["A",q];}
    insist(scoped(p,1,true)&&scoped(q,1,false)&&same(expandClass(p,def),q),"capture-safe expansion");binderChecks++;
  }
  const p=classProofs(),certificates=[];
  for(const g of p.generic){
    const c=g.premises.map(x=>p.closures.find(z=>same(z.goal,x)));
    if(c.some(x=>!x))continue;
    certificates.push({spec:{name:g.name},proof:c.reduce((q,r)=>["iE",q,r.proof],g.proof)});
  }
  let wrongClass=0,missing=0;
  for(const cert of certificates){
    insist(rejects(()=>compile(0,[],["axiom",cert.spec],{sourceTheory:"ZF",targetTheory:"ZF",classDef:def,certificates:[cert]})),"wrong class certificate");
    wrongClass++;
  }
  for(const name of ["extensionality","empty","pairing","union","foundation","power","infinity","choice"]){
    insist(rejects(()=>compile(0,[],["axiom",{name}],{sourceTheory:"ZFC",targetTheory:"ZF",classDef:def})),"uncertified axiom");
    missing++;
  }
  return {experiment:"ACE-03D-gate",pinned_formula_matches:true,class_conversion_checks:conversions,binder_expansion_checks:binderChecks,
    wrong_class_certificates_rejected:wrongClass,missing_axiom_certificates_rejected:missing,
    scope:"syntax and certificate separation; no closed L-axiom derivation"};
}
const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
console.log(JSON.stringify(gate(definition().L,pinned),null,2));
