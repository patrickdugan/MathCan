// ACE-03X. Independently rebuilt exact restriction and pair-support contracts.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildRestrictedWellOrder} from './restricted_well_order.mjs';
import {codeOrderExpectedLanguage} from './pair_product_order_replay.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function expectedRestrictedWellOrder(defs) {
  const {M,Q,I,C,A,E,every,some,quant,free,Pair,Val,iff,subset,W}=codeOrderExpectedLanguage(defs);
  const support=(p,b)=>some(b,x=>some(b,y=>Pair(p,x,y)));
  const pairShape=(p,b)=>E(x=>E(y=>C(C(M(x,b),M(y,b)),Pair(p,x,y))));
  const exact=(s,r,b)=>A(p=>iff(M(p,s),C(M(p,r),support(p,b))));
  const pairOnly=(s,b)=>every(s,p=>pairShape(p,b));
  const agreement=(s,r,b)=>A(x=>A(y=>iff(Val(s,x,y),C(C(M(x,b),M(y,b)),Val(r,x,y)))));
  const premises=(ps,q)=>ps.reduceRight((tail,p)=>I(p,tail),q);
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  return {formulas:{
    exact_restriction:f(3,exact),pair_only:f(2,pairOnly),pair_support:f(2,pairShape),bounded_pair_support:f(2,support),
    guarded_agreement:f(3,agreement),well_order:f(2,W),subset:f(2,subset)
  },proofs:{
    restriction_exact_exists:g(2,(r,b)=>E(s=>exact(s,r,b))),
    restriction_exact_unique:g(4,(s,t,r,b)=>premises([exact(s,r,b),exact(t,r,b)],Q(s,t))),
    restriction_subset:g(3,(s,r,b)=>I(exact(s,r,b),subset(s,r))),
    restriction_pair_only:g(3,(s,r,b)=>I(exact(s,r,b),pairOnly(s,b))),
    restriction_value_agreement:g(3,(s,r,b)=>I(exact(s,r,b),agreement(s,r,b))),
    restriction_preserves_well_order:g(4,(a,r,b,s)=>premises([subset(b,a),W(a,r),exact(s,r,b)],W(b,s))),
    restricted_well_order_exists:g(3,(a,r,b)=>premises([subset(b,a),W(a,r)],E(s=>C(exact(s,r,b),C(W(b,s),pairOnly(s,b))))))
  }};
}

function runRestrictedWellOrder() {
  const defs=definition('v',true),expected=expectedRestrictedWellOrder(defs),actual=buildRestrictedWellOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas))throw Error('independent exact-restriction interfaces');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('restriction proof coverage');
  const checks=[],controls=[],axioms=new Map(),verified=new Map();let logic=0,kernelControls=0,contractControls=0;
  const reject=(id,fn,type='kernel')=>{if(!rejects(fn))throw Error('negative control accepted: '+id);controls.push(id);if(type==='kernel')kernelControls++;else contractControls++;};
  const exact=(got,want)=>{if(!same(got,want))throw Error('restricted-order exact target');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const q of p)if(Array.isArray(q))walk(q,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent restriction target '+id);
    let got;
    try {got=kernel(0,[],p.proof,false,'ZF');} catch(error) {throw new Error('restriction kernel '+id+': '+error.message,{cause:error});}
    exact(got.goal,expected.proofs[id]);verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','separation'].includes(n)))throw Error('unexpected restriction axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(got.goal,['E',expected.proofs[id][1]]),'contract');
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(kernel(0,[],p.proof,false,'CL').goal,p.goal);logic++;}
  }
  for(const [id,binders,count] of [['restriction_exact_unique',4,2],['restriction_subset',3,1],['restriction_pair_only',3,1],
    ['restriction_value_agreement',3,1],['restriction_preserves_well_order',4,3],['restricted_well_order_exists',3,2]]) {
    for(let k=0;k<count;k++) {
      const changed=structuredClone(expected.proofs[id]);let p=changed;
      for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<k;i++)p=p[2];p.splice(0,p.length,...p[2]);
      reject(id+':omitted_premise_'+k,()=>exact(verified.get(id),changed),'contract');
    }
  }
  const selection=structuredClone(actual.proofs.restriction_exact_exists.proof);let selected=false;
  walk(selection,n=>{if(!selected&&n[0]==='axiom'&&n[1].name==='separation'){n[1].body=['=',0,0];selected=true;}});
  if(!selected)throw Error('restriction omitted separation');
  reject('restriction_exact_exists:omit_pair_support_filter',()=>exact(kernel(0,[],selection,false,'ZF').goal,expected.proofs.restriction_exact_exists),'contract');
  const broken=structuredClone(actual.proofs.restriction_value_agreement.proof);let changed=false;
  walk(broken,n=>{if(!changed&&n[0]==='eqS'){n[1]=['=',0,0];changed=true;}});
  if(!changed)throw Error('restriction omitted coordinate transport');
  reject('restriction_value_agreement:corrupt_pair_coordinates',()=>kernel(0,[],broken,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03X',part:'actual_well_order_relation_on_subset',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    logic_only_checks:logic,negative_controls:controls.length,kernel_rejection_controls:kernelControls,contract_rejection_controls:contractControls,controls,
    main_quantifier_order:['A','R','B'],main_premises:['B subset A','WO(A,R)'],
    main_conclusion:'exists S (ExactRestriction(S,R,B) and (WO(B,S) and PairOnly(S,B)))',
    exact_restriction:'p in S iff p in R and exists x in B exists y in B Pair(p,x,y)',
    pair_only:'forall p (p in S implies exists x exists y ((x in B and y in B) and Pair(p,x,y)))',
    relation_is_subset_of_input:true,relation_contains_only_pairs_from_subset:true,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,ambient_choice_used:false,
    scope:'Separation restricts any carrier-relative well-order to a unique actual relation on a supplied subset, including exact pair support'};
}

export {expectedRestrictedWellOrder,runRestrictedWellOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runRestrictedWellOrder(),null,2));
