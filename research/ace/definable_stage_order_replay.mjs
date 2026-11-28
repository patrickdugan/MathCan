// ACE-03W. Independent exact pinned-Def order and successor-extension targets.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildDefinableStageOrder } from './definable_stage_order.mjs';
import { codeOrderExpectedLanguage } from './pair_product_order_replay.mjs';
import { expectedDescriptionCarrier } from './description_carrier_replay.mjs';
import { expectedDescriptionEvaluation } from './description_evaluation_replay.mjs';
import { expectedSyntaxInstructionCodes } from './syntax_instruction_codes_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedDefinableStageOrder(defs) {
  const {M,Q,I,C,A,E,every,some,quant,apply,free,Pair,Val,Omega,iff,W}=codeOrderExpectedLanguage(defs);
  const ef=expectedDescriptionEvaluation(defs).formulas;
  const df=expectedDescriptionCarrier(defs).formulas;
  const tf=expectedSyntaxInstructionCodes(defs).formulas;
  const Def=(a,b)=>apply(defs.Def,a,b);
  const Eval=(d,x,a,w,ts)=>apply(ef.evaluation,d,x,a,w,...ts);
  const Bank=(w,ts)=>apply(ef.canonical_bank,w,...ts);
  const Distinct=ts=>apply(tf.distinct,...ts);
  const Triple=(i,w)=>apply(df.triple_carrier,i,w);
  const Raw=(c,w,i,a)=>apply(df.raw_carrier,c,w,i,a);
  const Full=(d,x,c,b,a,w,ts)=>C(C(M(d,c),M(x,b)),Eval(d,x,a,w,ts));
  const Hit=(p,c,b,a,w,ts)=>some(c,d=>some(b,x=>C(Pair(p,d,x),Eval(d,x,a,w,ts))));
  const Exact=(f,c,b,a,w,ts)=>A(p=>iff(M(p,f),Hit(p,c,b,a,w,ts)));
  const Agreement=(f,c,b,a,w,ts)=>A(d=>A(x=>iff(Val(f,d,x),Full(d,x,c,b,a,w,ts))));
  const Func=(c,f)=>quant(3,(d,x,y)=>I(M(d,c),I(Val(f,d,x),I(Val(f,d,y),Q(x,y)))));
  const Surj=(c,b,f)=>every(b,x=>some(c,d=>Val(f,d,x)));
  const Trans=a=>every(a,x=>every(x,y=>M(y,a)));
  const Restriction=(a,r,t)=>quant(2,(x,y)=>I(M(x,a),I(M(y,a),iff(Val(t,x,y),Val(r,x,y)))));
  const Initial=(a,b,t)=>quant(2,(x,y)=>I(M(x,a),I(M(y,b),I(Val(t,y,x),M(y,a)))));
  const imps=(premises,goal)=>premises.reduceRight((g,p)=>I(p,g),goal);
  const proofs={
    evaluation_relation_exists:quant(9,(c,b,a,w,...ts)=>E(f=>Exact(f,c,b,a,w,ts)))(0),
    evaluation_relation_unique:quant(11,(c,b,a,w,...rest)=>{
      const ts=rest.slice(0,5),[f,g]=rest.slice(5);
      return imps([Exact(f,c,b,a,w,ts),Exact(g,c,b,a,w,ts)],Q(f,g));
    })(0),
    evaluation_relation_agreement:quant(10,(c,b,a,w,...rest)=>{
      const ts=rest.slice(0,5),f=rest[5];
      return I(Exact(f,c,b,a,w,ts),Agreement(f,c,b,a,w,ts));
    })(0),
    evaluation_relation_functional:quant(10,(c,b,a,w,...rest)=>{
      const ts=rest.slice(0,5),f=rest[5];
      return imps([Omega(w),Distinct(ts),Exact(f,c,b,a,w,ts)],Func(c,f));
    })(0),
    evaluation_relation_surjective:quant(11,(w,a,i,c,b,f,...ts)=>imps([
      Omega(w),Bank(w,ts),Triple(i,w),Raw(c,w,i,a),Def(a,b),Exact(f,c,b,a,w,ts)],Surj(c,b,f)))(0),
    coded_def_well_order:quant(11,(w,a,i,c,b,t,...ts)=>imps([
      Omega(w),Bank(w,ts),Triple(i,w),Raw(c,w,i,a),W(c,t),Def(a,b)],E(r=>W(b,r))))(0),
    definable_carrier_well_order:quant(4,(w,a,r,b)=>imps([Omega(w),W(a,r),Def(a,b)],E(s=>W(b,s))))(0),
    definable_stage_order_exists:quant(2,(a,r)=>I(W(a,r),E(b=>E(s=>C(Def(a,b),W(b,s))))))(0),
    definable_successor_end_extension:quant(3,(a,b,r)=>imps([Def(a,b),Trans(a),W(a,r)],
      E(t=>C(C(W(b,t),Restriction(a,r,t)),Initial(a,b,t)))))(0)
  };
  const ts=[5,6,7,8,9].map(free);
  const expandedDef=A(x=>iff(M(x,free(1)),apply(defs.definable,free(0),x)))(0);
  return {proofs,expanded_pinned_Def:expandedDef,formulas:{
    evaluation:ef.evaluation,canonical_bank:ef.canonical_bank,distinct:tf.distinct,
    raw_carrier:df.raw_carrier,triple_carrier:df.triple_carrier,
    exact_evaluation_graph:Exact(free(0),free(1),free(2),free(3),free(4),ts)(0),
    evaluation_agreement:Agreement(free(0),free(1),free(2),free(3),free(4),ts)(0),
    restriction:Restriction(free(0),free(1),free(2))(0),
    initial_segment:Initial(free(0),free(1),free(2))(0),
    functional:Func(free(0),free(1))(0),surjective:Surj(free(0),free(1),free(2))(0),well_order:W(free(0),free(1))(0)
  },changed_contracts:{
    reversed_Def_arguments:quant(2,(a,r)=>I(W(a,r),E(b=>E(s=>C(Def(b,a),W(b,s))))))(0),
    restriction_on_entire_successor:quant(3,(a,b,r)=>imps([Def(a,b),Trans(a),W(a,r)],
      E(t=>C(C(W(b,t),Restriction(b,r,t)),Initial(a,b,t)))))(0),
    reversed_initial_segment:quant(3,(a,b,r)=>imps([Def(a,b),Trans(a),W(a,r)],
      E(t=>C(C(W(b,t),Restriction(a,r,t)),quant(2,(x,y)=>I(M(x,a),I(M(y,b),I(Val(t,x,y),M(y,a)))))))))(0)
  }};
}

function runDefinableStageOrder() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildDefinableStageOrder(defs),expected=expectedDefinableStageOrder(defs);
  if(!same(defs.Def,expected.expanded_pinned_Def))throw Error('exact original Def schema expansion');
  if(!same(built.formulas,expected.formulas))throw Error('independent stage-order formulas');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('stage-order theorem coverage');
  const checks=[],controls=[],axioms=new Map(),logicOnly=[],verifiedGoals=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  // Each positive proof is checked in full once. A control that changes only
  // its requested contract compares against that retained kernel conclusion;
  // controls that alter a proof are always sent through the kernel afresh.
  function exact(proof,want){
    const goal=verifiedGoals.get(proof)||kernel(0,[],proof,false,'ZF').goal;
    if(!same(goal,want))throw Error('stage-order exact contract mismatch');
  }
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent stage-order goal: '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('kernel stage-order conclusion: '+id);
    verifiedGoals.set(p.proof,got.goal);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation','infinity'].includes(n)))throw Error('unexpected stage-order axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('logical stage-order goal');logicOnly.push(id);}
  }
  function omit(id,binders,index,label) {
    const target=structuredClone(expected.proofs[id]);let p=target;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,target));
  }
  omit('definable_stage_order_exists',2,0,'supplied_alphabet_well_order');
  for(const [index,label] of ['exact_Def','transitive_stage','supplied_stage_well_order'].entries())
    omit('definable_successor_end_extension',3,index,label);
  for(const [index,label] of ['omega','canonical_tags','triple_carrier','raw_carrier','code_well_order','exact_Def'].entries())
    omit('coded_def_well_order',11,index,label);
  for(const [index,label] of ['omega','distinct_tags','exact_evaluation_graph'].entries())
    omit('evaluation_relation_functional',10,index,label);
  for(const [index,label] of ['omega','canonical_tags','triple_carrier','raw_carrier','exact_Def','exact_evaluation_graph'].entries())
    omit('evaluation_relation_surjective',11,index,label);
  for(const [index,label] of ['omega','supplied_alphabet_well_order','exact_Def'].entries())
    omit('definable_carrier_well_order',4,index,label);
  omit('evaluation_relation_agreement',10,0,'exact_membership_contract');
  reject('definable_stage_order_exists:reverse_pinned_Def_arguments',()=>
    exact(built.proofs.definable_stage_order_exists.proof,expected.changed_contracts.reversed_Def_arguments));
  reject('end_extension:enlarge_restriction_domain_to_B',()=>
    exact(built.proofs.definable_successor_end_extension.proof,expected.changed_contracts.restriction_on_entire_successor));
  reject('end_extension:reverse_initial_segment_direction',()=>
    exact(built.proofs.definable_successor_end_extension.proof,expected.changed_contracts.reversed_initial_segment));

  const damaged=structuredClone(built.proofs.evaluation_relation_exists.proof);let changed=false;
  walk(damaged,n=>{
    if(changed||n[0]!=='axiom'||n[1].name!=='separation')return;
    function alter(p){if(!Array.isArray(p)||changed)return;if(p[0]==='M'||p[0]==='='){p[0]=p[0]==='M'?'=':'M';changed=true;return;}for(const x of p)alter(x);}
    alter(n[1].body);
  });
  if(!changed)throw Error('evaluation relation mutation changed nothing');
  reject('evaluation_relation_exists:corrupt_separation_predicate',()=>kernel(0,[],damaged,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03W',part:'least_description_code_order_on_exact_pinned_Def',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,reused_helper_checks:0,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:12,exact_pinned_Def_schema_comparisons:1,
    pure_logic_checks:logicOnly,negative_controls:controls.length,controls,
    contract_controls_use_verified_conclusions:true,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.name==='separation'?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    stage_order_quantifier_order:['A','R'],stage_order_premises:['WO(A,R)'],
    stage_order_conclusion:'exists B,S (Def(A,B) and WO(B,S))',
    end_extension_quantifier_order:['A','B','R'],
    end_extension_premises:['Def(A,B)','Trans(A)','WO(A,R)'],
    end_extension_conclusion:'exists T ((WO(B,T) and order restriction to A equals R) and A is an initial segment of B)',
    omega_existence_discharged:true,Def_set_existence_discharged:true,
    evaluation_graph_exact:true,evaluation_functional:true,evaluation_onto_pinned_Def:true,
    order_relation_is_actual_set:true,pinned_L_unchanged:true,
    scope:'ambient ZF construction of a well-order on the exact pinned Def of every supplied well-ordered set, with a transitive-stage successor end-extension',
    outside_this_replay:['coherent canonical histories across all constructible stages','constructibility of the resulting restricted orders','exact relativized Choice import','formal checker soundness']
  };
}

export { expectedDefinableStageOrder, runDefinableStageOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runDefinableStageOrder(),null,2));
