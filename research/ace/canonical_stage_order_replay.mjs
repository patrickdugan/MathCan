// ACE-03X. Independent exact contracts for the canonical Def successor.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {canonicalStageOrderFormulas,buildCanonicalStageOrder} from './canonical_stage_order.mjs';
import {codeOrderExpectedLanguage} from './pair_product_order_replay.mjs';
import {expectedCanonicalDescriptionOrder} from './canonical_description_order_replay.mjs';
import {expectedDescriptionEvaluation} from './description_evaluation_replay.mjs';
import {expectedDefinableStageOrder} from './definable_stage_order_replay.mjs';
import {expectedCanonicalLimitOrder} from './canonical_limit_order_replay.mjs';
import {junkFixtures} from './canonical_relation_replay.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

// New targets use depth-indexed variables. The preceding description and
// evaluation interfaces come from their independent replay builders.
function canonicalStageExpectedLanguage(defs) {
  const L=codeOrderExpectedLanguage(defs),{M,Q,I,C,O,N,A,E,every,some,quant,apply,free,Pair,Val,Omega,iff,subset,W}=L;
  const raw=expectedCanonicalDescriptionOrder(defs).formulas,ev=expectedDescriptionEvaluation(defs).formulas;
  const Def=(a,b)=>apply(defs.Def,a,b),Trans=a=>every(a,x=>subset(x,a));
  const Restriction=(a,r,s)=>quant(2,(x,y)=>I(M(x,a),I(M(y,a),iff(Val(s,x,y),Val(r,x,y)))));
  const Initial=(a,b,s)=>every(a,x=>every(b,y=>I(Val(s,y,x),M(y,a))));
  const Construction=(w,a,r,i,c,t)=>apply(raw.construction,w,a,r,i,c,t);
  const Bank=(w,ts)=>apply(ev.canonical_bank,w,...ts),Eval=(d,x,a,w,ts)=>apply(ev.evaluation,d,x,a,w,...ts);
  const ExactEval=(f,c,b,a,w,ts)=>A(p=>iff(M(p,f),some(c,d=>some(b,x=>C(Pair(p,d,x),Eval(d,x,a,w,ts))))));
  const Minimum=(c,q,f,x,d)=>C(C(M(d,c),Val(f,d,x)),every(c,e=>I(Val(f,e,x),N(Val(q,e,d)))));
  const Induced=(c,b,q,f,x,y)=>C(C(M(x,b),M(y,b)),E(d=>E(e=>C(C(Minimum(c,q,f,x,d),Minimum(c,q,f,y,e)),Val(q,d,e)))));
  const Successor=(a,b,r,u,x,y)=>C(C(M(x,b),M(y,b)),O(C(C(M(x,a),M(y,a)),Val(r,x,y)),
    O(C(M(x,a),N(M(y,a))),C(C(N(M(x,a)),N(M(y,a))),Val(u,x,y)))));
  const Exact=(t,phi)=>A(p=>iff(M(p,t),E(x=>E(y=>C(Pair(p,x,y),phi(x,y))))));
  const ExactInduced=(u,c,b,q,f)=>Exact(u,(x,y)=>Induced(c,b,q,f,x,y));
  const ExactSuccessor=(s,a,b,r,u)=>Exact(s,(x,y)=>Successor(a,b,r,u,x,y));
  const AgreementSuccessor=(s,a,b,r,u)=>quant(2,(x,y)=>iff(Val(s,x,y),Successor(a,b,r,u,x,y)));
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const Facts=(a,r,b,s,w,ts,i,c,q,f,u,weak=false)=>C(C(C(Construction(w,a,r,i,c,q),ExactEval(f,c,b,a,w,ts)),
    ExactInduced(u,c,b,q,f)),(weak?AgreementSuccessor:ExactSuccessor)(s,a,b,r,u));
  const Core=(a,r,b,s,weak=false)=>E(w=>C(Omega(w),exs(5,ts=>C(Bank(w,ts),exs(5,([i,c,q,f,u])=>Facts(a,r,b,s,w,ts,i,c,q,f,u,weak))))));
  const Extension=(a,r,b,s)=>C(subset(a,b),C(Restriction(a,r,s),Initial(a,b,s)));
  const Stage=(a,r,b,s)=>C(C(Def(a,b),Core(a,r,b,s)),C(C(Trans(b),W(b,s)),Extension(a,r,b,s)));
  const Good=p=>E(a=>E(r=>C(Pair(p,a,r),C(Trans(a),W(a,r)))));
  const Next=(p,q)=>exs(4,([a,r,b,s])=>C(C(Pair(p,a,r),Pair(q,b,s)),Stage(a,r,b,s)));
  const Embed=(p,q)=>exs(4,([a,r,b,s])=>C(C(Pair(p,a,r),Pair(q,b,s)),Extension(a,r,b,s)));
  const premises=(hs,p)=>hs.reduceRight((g,h)=>I(h,g),p);
  return {...L,Def,Trans,Restriction,Initial,Construction,Bank,Eval,ExactEval,Minimum,Induced,Successor,Exact,ExactInduced,ExactSuccessor,
    AgreementSuccessor,exs,Facts,Core,Extension,Stage,Good,Next,Embed,premises};
}

const relationProofIds=['good_coordinates','embed_coordinates','extension_reflexive','extension_transitive','embed_reflexive',
  'embed_transitive','next_preserves_good','next_embeds','next_def_step'];

function expectedCanonicalStageOrder(defs) {
  const L=canonicalStageExpectedLanguage(defs),{M,Q,I,C,A,E,quant,apply,free,Pair,iff,subset,W,Def,Trans,Restriction,Initial,
    ExactEval,ExactInduced,ExactSuccessor,Facts,Core,Extension,Stage,Good,Next,Embed,premises}=L;
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  const proofs={
    good_coordinates:g(3,(p,a,r)=>premises([Good(p),Pair(p,a,r)],C(Trans(a),W(a,r)))),
    embed_coordinates:g(6,(p,q,a,r,b,s)=>premises([Embed(p,q),Pair(p,a,r),Pair(q,b,s)],Extension(a,r,b,s))),
    extension_reflexive:g(2,(a,r)=>Extension(a,r,a,r)),
    extension_transitive:g(6,(a,r,b,s,c,t)=>premises([Extension(a,r,b,s),Extension(b,s,c,t)],Extension(a,r,c,t))),
    embed_reflexive:g(1,p=>I(Good(p),Embed(p,p))),
    embed_transitive:g(3,(p,q,v)=>premises([Embed(p,q),Embed(q,v)],Embed(p,v))),
    next_preserves_good:g(2,(p,q)=>I(Next(p,q),Good(q))),
    next_embeds:g(2,(p,q)=>I(Next(p,q),Embed(p,q))),
    next_def_step:g(6,(p,q,a,r,b,s)=>premises([Next(p,q),Pair(p,a,r),Pair(q,b,s)],Def(a,b))),
    canonical_stage_given_Def:g(3,(a,r,b)=>premises([Trans(a),W(a,r),Def(a,b)],E(s=>Stage(a,r,b,s)))),
    canonical_stage_exists:g(2,(a,r)=>premises([Trans(a),W(a,r)],E(b=>E(s=>Stage(a,r,b,s))))),
    canonical_stage_core_unique:g(5,(a,r,b,s,t)=>premises([Core(a,r,b,s),Core(a,r,b,t)],Q(s,t))),
    canonical_stage_unique:g(6,(a,r,b,s,d,t)=>premises([Stage(a,r,b,s),Stage(a,r,d,t)],C(Q(b,d),Q(s,t)))),
    next_exists:g(1,p=>I(Good(p),E(q=>Next(p,q)))),
    next_unique:g(3,(p,q,t)=>premises([Next(p,q),Next(p,t)],Q(q,t)))
  };
  const expandedDef=A(x=>iff(M(x,free(1)),apply(defs.definable,free(0),x)))(0);
  return {formulas:{
    stage:f(4,Stage),core:f(4,Core),
    facts:f(15,(a,r,b,s,w,...vs)=>Facts(a,r,b,s,w,vs.slice(0,5),...vs.slice(5))),
    exact_evaluation_graph:f(10,(f,c,b,a,w,...ts)=>ExactEval(f,c,b,a,w,ts)),
    exact_induced_order:f(5,ExactInduced),exact_successor_order:f(5,ExactSuccessor),
    good:f(1,Good),next:f(2,Next),embed:f(2,Embed),extension:f(4,Extension),restriction:f(3,Restriction),initial:f(3,Initial),
    subset:f(2,subset),transitive:f(1,Trans),well_order:f(2,W)
  },proofs,expanded_pinned_Def:expandedDef,changed_contracts:{
    reversed_Def:g(6,(p,q,a,r,b,s)=>premises([Next(p,q),Pair(p,a,r),Pair(q,b,s)],Def(b,a))),
    swapped_unique_output:g(6,(a,r,b,s,d,t)=>premises([Stage(a,r,b,s),Stage(a,r,d,t)],C(Q(b,t),Q(s,d)))),
    Val_only_successor_uniqueness:g(5,(a,r,b,s,t)=>premises([Core(a,r,b,s,true),Core(a,r,b,t,true)],Q(s,t)))
  }};
}

function runCanonicalStageOrder(part='all') {
  if(!['relations','all'].includes(part))throw Error('canonical stage replay part');
  const defs=definition('v',true),expected=expectedCanonicalStageOrder(defs),built=buildCanonicalStageOrder(defs,part);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(defs.Def,expected.expanded_pinned_Def))throw Error('exact pinned Def expansion');
  if(!same(built.formulas,expected.formulas))throw Error('independent canonical stage interfaces');
  const prior=expectedDefinableStageOrder(defs).formulas,limit=expectedCanonicalLimitOrder(defs).formulas;
  for(const key of ['exact_evaluation_graph','well_order','restriction'])if(!same(expected.formulas[key],prior[key]))throw Error('prior interface '+key);
  for(const key of ['well_order','restriction','initial','transitive'])if(!same(expected.formulas[key],limit[key]))throw Error('limit interface '+key);
  const wanted=part==='relations'?relationProofIds:Object.keys(expected.proofs);
  if(!same(Object.keys(built.proofs),wanted))throw Error('canonical stage coverage');
  const checks=[],controls=[],axioms=new Map(),verified=new Map(),logic=[];let kernelControls=0,contractControls=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function dropUniversal(p){
    if(!Array.isArray(p))return null;if(p[0]==='uI')return p[1];
    for(let i=1;i<p.length;i++){const changed=dropUniversal(p[i]);if(changed){const q=p.slice();q[i]=changed;return q;}}
    return null;
  }
  const reject=(id,fn,type='kernel')=>{if(!rejects(fn))throw Error('negative control accepted '+id);controls.push(id);if(type==='kernel')kernelControls++;else contractControls++;};
  const exact=(got,want)=>{if(!same(got,want))throw Error('canonical stage target mismatch');};
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent canonical stage goal '+id);
    const got=kernel(0,[],p.proof,false,'ZF');exact(got.goal,expected.proofs[id]);verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation','infinity'].includes(n)))throw Error('canonical stage axiom '+id);
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    const bare=dropUniversal(p.proof);if(!bare)throw Error('missing quantified proof '+id);
    reject(id+':drop_universal',()=>kernel(0,[],bare,false,'ZF'));
    reject(id+':changed_outer_binder',()=>exact(got.goal,['E',expected.proofs[id][1]]),'contract');
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(kernel(0,[],p.proof,false,'CL').goal,expected.proofs[id]);logic.push(id);}
  }
  function omit(id,binders,index,label) {
    if(!verified.has(id))return;
    const changed=structuredClone(expected.proofs[id]);let p=changed;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];p.splice(0,p.length,...p[2]);
    reject(id+':omit_'+label,()=>exact(verified.get(id),changed),'contract');
  }
  for(const [id,binders,names] of [
    ['good_coordinates',3,['good_state','exact_pair']],['embed_coordinates',6,['embedding','source_pair','target_pair']],
    ['extension_transitive',6,['first_extension','second_extension']],['embed_transitive',3,['first_embedding','second_embedding']],
    ['next_def_step',6,['successor','source_pair','target_pair']],['canonical_stage_given_Def',3,['transitivity','input_well_order','exact_Def']],
    ['canonical_stage_exists',2,['transitivity','input_well_order']],['canonical_stage_core_unique',5,['first_recipe','second_recipe']],
    ['canonical_stage_unique',6,['first_stage','second_stage']],['next_exists',1,['good_state']],['next_unique',3,['first_successor','second_successor']]
  ])for(let i=0;i<names.length;i++)omit(id,binders,i,names[i]);
  reject('next_def_step:reverse_Def_arguments',()=>exact(verified.get('next_def_step'),expected.changed_contracts.reversed_Def),'contract');
  if(part==='all') {
    reject('canonical_stage_unique:swap_output_coordinates',()=>exact(verified.get('canonical_stage_unique'),expected.changed_contracts.swapped_unique_output),'contract');
    reject('canonical_stage_core_unique:Val_only_successor',()=>exact(verified.get('canonical_stage_core_unique'),expected.changed_contracts.Val_only_successor_uniqueness),'contract');
    const damage=structuredClone(built.proofs.canonical_stage_given_Def.proof);let changed=false;
    walk(damage,n=>{if(!changed&&n[0]==='axiom'&&n[1].name==='separation'){n[1]={...n[1],body:['F']};changed=true;}});
    if(!changed)throw Error('no live Separation instance');
    reject('canonical_stage_given_Def:corrupt_separation',()=>kernel(0,[],damage,false,'ZF'));
    const transport=structuredClone(built.proofs.canonical_stage_core_unique.proof);let found=false;
    walk(transport,n=>{if(!found&&n[0]==='eqS'){n[1]=['=',0,0];found=true;}});
    if(!found)throw Error('no live core equality transport');
    reject('canonical_stage_core_unique:corrupt_equality_transport',()=>kernel(0,[],transport,false,'ZF'));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03X',part:part==='all'?'canonical_Def_successor_state':'canonical_successor_packed_relations',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    exact_pinned_Def_schema_comparisons:1,prior_interface_checks:3,limit_interface_checks:4,
    logic_only_checks:logic.length,pure_logic_modules:logic,negative_controls:controls.length,
    kernel_rejection_controls:kernelControls,contract_rejection_controls:contractControls,controls,
    contract_controls_use_verified_conclusions:true,
    canonical_relation_junk_fixtures:part==='all'?junkFixtures():[],
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    omega_existence_discharged:part==='all',Def_set_existence_discharged:part==='all',
    exact_evaluation_graph:true,exact_induced_order:true,exact_successor_order:true,
    canonical_successor_unique:part==='all',ambient_choice_used:false,pinned_L_unchanged:true,
    scope:'unique exact successor state for every transitive set with a supplied well-order, using the pinned Def formula, preserving order restriction and initiality',
    open_obligations:['the recursive history must establish each input state is good','internal constructibility of the canonical order sets','exact relativized Choice import','formal checker soundness']};
}

export {canonicalStageExpectedLanguage,expectedCanonicalStageOrder,runCanonicalStageOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runCanonicalStageOrder(process.argv[2]??'all'),null,2));
