// ACE-03W. Independent targets for the natural relation and triple alphabet.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildNaturalCodeOrder} from './natural_code_order.mjs';
import {codeOrderExpectedLanguage} from './pair_product_order_replay.mjs';
import {syntaxInstructionCodeFormulas} from './syntax_instruction_codes.mjs';
import {buildWellOrder} from './constructible_well_order.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function expectedNaturalCodeOrder(defs) {
  const {M,I,C,A,E,quant,free,Omega,product,triple,tripleCarrier,wo,W,complete}=codeOrderExpectedLanguage(defs);
  const guarded=(w,x,y)=>C(C(M(x,w),M(y,w)),M(x,y));
  const phi=(ps,x,y)=>guarded(ps[0],x,y);
  return {formulas:{guarded_membership:guarded(free(2),free(0),free(1))(0),
    triple:triple(free(0),free(1),free(2),free(3))(0),triple_carrier:tripleCarrier(free(0),free(1))(0),
    product:product(free(0),free(1),free(2))(0),well_order:W(free(0),free(1))(0)},proofs:{
    omega_guarded_well_order:A(w=>I(Omega(w),wo(w,(x,y)=>guarded(w,x,y))))(0),
    omega_canonical_relation:A(w=>I(Omega(w),E(r=>complete([w],w,phi,r))))(0),
    omega_set_well_order_exists:A(w=>I(Omega(w),E(r=>W(w,r))))(0),
    nested_products_are_triple_carrier:quant(3,(w,p,c)=>I(product(w,w,p),I(product(w,p,c),tripleCarrier(c,w))))(0),
    natural_triple_well_order_exists:A(w=>I(Omega(w),E(c=>E(r=>C(tripleCarrier(c,w),W(c,r))))))(0)
  }};
}
function runNaturalCodeOrder() {
  const defs=definition('v',true),actual=buildNaturalCodeOrder(defs),expected=expectedNaturalCodeOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas)||!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('natural code interface');
  const syntax=syntaxInstructionCodeFormulas(defs);
  for(const id of ['triple','triple_carrier'])if(!same(actual.formulas[id],syntax[id]))throw Error('syntax triple interface '+id);
  if(!same(actual.formulas.well_order,buildWellOrder(defs).formulas.well_order))throw Error('well-order layout');
  const checks=[],controls=[],schemas=new Map();let logic=0;
  const reject=(id,fn)=>{if(!rejects(fn))throw Error('negative accepted '+id);controls.push(id);};
  const exact=(proof,want)=>{if(!same(kernel(0,[],proof,false,'ZF').goal,want))throw Error('goal mismatch');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent natural target '+id);
    const got=kernel(0,[],p.proof,false,'ZF');if(!same(p.goal,got.goal))throw Error('kernel goal '+id);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);schemas.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>!['extensionality','pairing','foundation','union','power','separation'].includes(x)))throw Error('natural code axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(p.proof,['E',p.goal[1]]));
    reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('pure logic');logic++;}
    if(id.startsWith('omega_')||id==='natural_triple_well_order_exists')
      reject(id+':omit_omega',()=>exact(p.proof,['A',p.goal[1][2]]));
  }
  for(let k=0;k<2;k++) {
    const goal=structuredClone(expected.proofs.nested_products_are_triple_carrier);let node=goal[1][1][1];
    if(k)node=node[2];node.splice(0,node.length,...node[2]);
    reject('triple_carrier:omit_product_'+k,()=>exact(actual.proofs.nested_products_are_triple_carrier.proof,goal));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'natural_relation_and_triple_alphabet',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    syntax_formula_link_checks:2,shared_well_order_layout_checks:1,logic_only_checks:logic,
    negative_controls:controls.length,controls,
    ambient_axiom_instances:[...schemas.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,scope:'canonical set relation for membership on a supplied omega set and an actual well-ordered carrier of normalized natural triples'};
}
export {expectedNaturalCodeOrder,runNaturalCodeOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runNaturalCodeOrder(),null,2));
