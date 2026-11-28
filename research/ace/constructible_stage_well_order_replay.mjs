// ACE-03X. Independent endpoints for the actual pinned constructible class.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { definition } from './constructible_definition.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';
import { buildConstructibleStageWellOrder } from './constructible_stage_well_order.mjs';
import { codeOrderExpectedLanguage } from './pair_product_order_replay.mjs';
import { expectedCarrierHistoryProjection } from './carrier_history_projection_replay.mjs';
import { expectedRestrictedWellOrder } from './restricted_well_order_replay.mjs';

function expectedConstructibleStageWellOrder(defs) {
  const {M,Q,I,C,A,E,every,quant,apply,free,Val,W}=codeOrderExpectedLanguage(defs);
  const pf=expectedCarrierHistoryProjection(defs).formulas,rf=expectedRestrictedWellOrder(defs).formulas;
  const Sub=(a,b)=>every(a,x=>M(x,b)),Trans=a=>every(a,x=>Sub(x,a));
  const Ord=d=>apply(defs.ordinal,d),Succ=(a,d)=>apply(defs.successor,a,d);
  const Pinned=(g,d)=>apply(pf.pinned_stage_graph,g,d),Hist=(f,d)=>apply(pf.history,f,d);
  const Complete=(f,d,g)=>apply(pf.complete,f,d,g),GoodCarriers=(g,d)=>apply(pf.good_carriers,g,d);
  const PairOnly=(s,b)=>apply(rf.pair_only,s,b),InL=x=>apply(defs.L,x);
  const Realized=d=>E(f=>E(g=>C(Hist(f,d),C(Complete(f,d,g),GoodCarriers(g,d)))));
  const expandedL=x=>E(a=>C(Ord(a),E(d=>C(Succ(a,d),E(g=>C(Pinned(g,d),E(b=>C(Val(g,a,b),M(x,b)))))))));
  const goals={
    well_order_on_subset:quant(3,(a,r,b)=>I(Sub(b,a),I(W(a,r),W(b,r))))(0),
    ordinal_history_with_pinned_projection:A(d=>I(Ord(d),Realized(d)))(0),
    all_pinned_stage_values_well_ordered:quant(2,(d,g)=>I(Ord(d),I(Pinned(g,d),GoodCarriers(g,d))))(0),
    every_constructible_set_has_ambient_well_order:A(x=>I(InL(x),E(s=>C(W(x,s),PairOnly(s,x)))))(0)
  };
  return {goals,expanded_L:expandedL(free(0))(0),formulas:{
    history:pf.history,projection:pf.complete,good_carriers:pf.good_carriers,
    realized_history:Realized(free(0))(0),well_order:W(free(0),free(1))(0),
    subset:Sub(free(0),free(1))(0),transitive:Trans(free(0))(0),pair_only:rf.pair_only,
    pinned_stage_graph:pf.pinned_stage_graph,pinned_L:expandedL(free(0))(0)
  },changed:{
    without_constructibility:A(x=>E(s=>C(W(x,s),PairOnly(s,x))))(0),
    internal_order_membership:A(x=>I(InL(x),E(s=>C(C(W(x,s),PairOnly(s,x)),InL(s)))))(0),
    reverse_relation_support:A(x=>I(InL(x),E(s=>C(W(x,s),PairOnly(x,s)))))(0),
    omit_pinned_stage_graph:quant(2,(d,g)=>I(Ord(d),GoodCarriers(g,d)))(0)
  }};
}

function runConstructibleStageWellOrder(part='all') {
  const defs=definition('v',true),expected=expectedConstructibleStageWellOrder(defs);
  const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned)||!same(defs.L,expected.expanded_L))throw Error('exact pinned L expansion');
  const trace=process.env.ACE_FINAL_DIAGNOSTICS?label=>console.error(label,JSON.stringify(process.memoryUsage())):undefined;
  const built=buildConstructibleStageWellOrder(defs,part,{onProgress:trace});
  if(typeof globalThis.gc==='function')globalThis.gc();
  trace?.('after_generation_collection');
  if(!same(built.formulas,expected.formulas))throw Error('final constructible-order interfaces');
  const ids=Object.keys(expected.goals).slice(0,{subset:1,projection:2,stages:3,all:4}[part]);
  if(!same(Object.keys(built.proofs),ids))throw Error('final theorem coverage');
  const checks=[],controls=[],verified=new Map(),axioms=new Set();let logic=0,kernelControls=0,contractControls=0;
  const hash=x=>createHash('sha256').update(JSON.stringify(x)).digest('hex');
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn,kind='kernel'){
    if(!rejects(fn))throw Error('final-order control accepted: '+name);
    controls.push(name);if(kind==='kernel')kernelControls++;else contractControls++;
  }
  function contract(id,target){if(!same(verified.get(id),target))throw Error('changed final-order conclusion');}
  // A persistent path copy changes one live axiom without cloning or
  // mutating the large complete proof tree retained for the positive check.
  function withForbiddenAxiom(p) {
    if(!Array.isArray(p))return null;
    if(p[0]==='axiom')return ['axiom',{name:'choice'}];
    for(let i=1;i<p.length;i++){
      const changed=withForbiddenAxiom(p[i]);
      if(changed){const out=p.slice();out[i]=changed;return out;}
    }
    return null;
  }
  for(const [id,p] of Object.entries(built.proofs)){
    if(typeof globalThis.gc==='function')globalThis.gc();
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.goals[id]))throw Error('exact final-order target: '+id);
    trace?.('checking_'+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    trace?.('checked_'+id);
    if(!same(got.goal,expected.goals[id]))throw Error('final-order kernel conclusion: '+id);
    verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.add(n[1].name);}});
    const allowed=['extensionality','empty','pairing','union','power','separation','replacement','foundation','infinity'];
    if([...used].some(name=>!allowed.includes(name)))throw Error('unexpected ambient axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(p.goal).length,goal_sha256:hash(p.goal),ambient_axioms:[...used].sort()});
    if(!used.size){const pure=kernel(0,[],p.proof,false,'CL');if(!same(pure.goal,p.goal))throw Error('logical restriction proof');logic++;}
    else {
      reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
      reject(id+':replace_live_axiom_with_choice',()=>kernel(0,[],withForbiddenAxiom(p.proof),false,'ZF'));
    }
    reject(id+':changed_conclusion',()=>contract(id,['F']),'contract');
  }
  const final='every_constructible_set_has_ambient_well_order';
  if(verified.has(final))for(const name of ['without_constructibility','internal_order_membership','reverse_relation_support'])
    reject(final+':'+name,()=>contract(final,expected.changed[name]),'contract');
  if(verified.has('all_pinned_stage_values_well_ordered'))reject('all_stage_values:omit_pinned_stage_graph',()=>contract('all_pinned_stage_values_well_ordered',expected.changed.omit_pinned_stage_graph),'contract');
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03X',part:'actual_pinned_L_stage_and_ambient_well_order_link_'+part,checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,p)=>n+p.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    exact_pinned_L_schema_comparisons:1,negative_controls:controls.length,kernel_rejection_controls:kernelControls,
    contract_rejection_controls:contractControls,contract_controls_use_verified_conclusions:true,controls,
    logic_only_checks:logic,ambient_axioms:[...axioms].sort(),pinned_L_unchanged:true,
    final_goal_sha256:verified.has(final)?hash(expected.goals[final]):null,
    final_goal:verified.has(final)?'forall x (L(x) -> exists R (WO(x,R) and every member of R is a Kuratowski pair of members of x))':null,
    order_relation_is_actual_set:verified.has(final),relation_pairs_within_carrier:verified.has(final),Choice_imported:false,
    scope:'ambient ZF well-orderability of every set in the exact pinned constructible class, obtained from canonical ordinal histories, their carrier projection and actual pair-relation restriction',
    outside_this_replay:['membership of the constructed order relation in L','exact relativized Choice import','unrestricted schema coverage','formal checker soundness']};
}

export {expectedConstructibleStageWellOrder,runConstructibleStageWellOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runConstructibleStageWellOrder(process.argv.find(s=>s.startsWith('--part='))?.slice(7)||'all'),null,2));
