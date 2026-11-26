// ACE-03X. Independent projection targets for the exact pinned L hierarchy.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildCarrierHistoryProjection} from './carrier_history_projection.mjs';
import {codeOrderExpectedLanguage} from './pair_product_order_replay.mjs';
import {expectedCanonicalStageOrder} from './canonical_stage_order_replay.mjs';
import {expectedCanonicalLimitOrder} from './canonical_limit_order_replay.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function carrierProjectionExpectedLanguage(defs) {
  const L=codeOrderExpectedLanguage(defs),{M,Q,I,C,O,N,A,E,every,some,quant,apply,free,Pair,Val,iff,subset,W}=L;
  const sf=expectedCanonicalStageOrder(defs).formulas,lf=expectedCanonicalLimitOrder(defs).formulas;
  const Graph=(f,d)=>apply(defs.graph,f,d),Ord=d=>apply(defs.ordinal,d),Def=(a,b)=>apply(defs.Def,a,b),Succ=(a,b)=>apply(defs.successor,a,b);
  const Trans=a=>every(a,x=>subset(x,a)),Good=p=>apply(sf.good,p),Next=(p,q)=>apply(sf.next,p,q),Embed=(p,q)=>apply(sf.embed,p,q);
  const Value=(h,p)=>apply(lf.value,h,p),UnionCarrier=(h,a)=>apply(lf.union_carrier,h,a);
  const Range=(f,d,h)=>A(p=>iff(M(p,h),some(d,j=>Val(f,j,p))));
  const Pred=d=>some(d,j=>Succ(j,d));
  const Prior=(f,d,r)=>every(d,i=>A(p=>I(Val(f,i,p),Embed(p,r))));
  const SuccCase=(f,d,r)=>some(d,i=>C(Succ(i,d),E(p=>C(Val(f,i,p),Next(p,r)))));
  const LimitCase=(f,d,r)=>C(N(Pred(d)),E(h=>C(Range(f,d,h),Value(h,r))));
  const Step=(f,d,r)=>C(Good(r),C(Prior(f,d,r),O(SuccCase(f,d,r),LimitCase(f,d,r))));
  const Hist=(f,d)=>C(Graph(f,d),every(d,i=>E(r=>C(Val(f,i,r),Step(f,i,r)))));
  const Pointwise=(f,d)=>every(d,i=>A(p=>I(Val(f,i,p),Good(p))));
  const Carrier=(f,i,a)=>E(p=>E(r=>C(Val(f,i,p),Pair(p,a,r))));
  const Packed=(f,d)=>every(d,i=>A(p=>I(Val(f,i,p),E(a=>E(r=>Pair(p,a,r))))));
  const ProjectedPair=(q,f,i)=>E(a=>C(Carrier(f,i,a),Pair(q,i,a)));
  const Exact=(f,d,g)=>A(q=>iff(M(q,g),some(d,i=>ProjectedPair(q,f,i))));
  const Agreement=(f,d,g)=>every(d,i=>A(a=>iff(Val(g,i,a),Carrier(f,i,a))));
  const LimitStage=(g,i,a)=>A(x=>iff(M(x,a),some(i,j=>E(b=>C(Val(g,j,b),M(x,b))))));
  const PinnedStage=(g,i,a)=>O(some(i,j=>C(Succ(j,i),E(b=>C(Val(g,j,b),Def(b,a))))),C(N(Pred(i)),LimitStage(g,i,a)));
  const PinnedHistory=(g,d)=>C(Graph(g,d),every(d,i=>E(a=>C(Val(g,i,a),PinnedStage(g,i,a)))));
  const Complete=(f,d,g)=>C(C(Graph(g,d),Agreement(f,d,g)),PinnedHistory(g,d));
  const GoodCarriers=(g,d)=>every(d,i=>A(a=>I(Val(g,i,a),E(r=>C(Trans(a),W(a,r))))));
  const premises=(hs,p)=>hs.reduceRight((g,h)=>I(h,g),p);
  return {...L,Graph,Ord,Def,Succ,Trans,Good,Next,Embed,Value,UnionCarrier,Range,Pred,Prior,SuccCase,LimitCase,Step,Hist,Pointwise,
    Carrier,Packed,ProjectedPair,Exact,Agreement,LimitStage,PinnedStage,PinnedHistory,Complete,GoodCarriers,premises};
}

function expectedCarrierHistoryProjection(defs) {
  const L=carrierProjectionExpectedLanguage(defs),{M,Q,I,C,A,E,every,quant,free,Pair,Val,iff,W,Graph,Ord,Trans,Good,Step,Hist,Pointwise,
    Carrier,Packed,ProjectedPair,Exact,Agreement,Range,UnionCarrier,LimitStage,PinnedStage,PinnedHistory,Complete,GoodCarriers,premises}=L;
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  const WrongCarrier=(f,i,a)=>E(p=>E(r=>C(Val(f,i,p),Pair(p,r,a))));
  const WrongAgreement=(f,d,g)=>every(d,i=>A(a=>iff(Val(g,i,a),WrongCarrier(f,i,a))));
  return {formulas:{
    carrier:f(3,Carrier),packed_values:f(2,Packed),projected_pair:f(3,ProjectedPair),exact_projection:f(3,Exact),
    carrier_agreement:f(3,Agreement),pointwise:f(2,Pointwise),limit_stage:f(3,LimitStage),complete:f(3,Complete),
    good_carriers:f(2,GoodCarriers),history:f(2,Hist),step:f(3,Step),range:f(3,Range),
    pinned_stage:f(3,PinnedStage),pinned_stage_graph:f(2,PinnedHistory),transitive:f(1,Trans),well_order:f(2,W)
  },replacement_schema:{name:'replacement',params:1,body:ProjectedPair(free(0),free(2),free(1))(0)},proofs:{
    carrier_value_unique:g(5,(f,d,i,a,b)=>premises([Graph(f,d),M(i,d),Carrier(f,i,a),Carrier(f,i,b)],Q(a,b))),
    carrier_value_total:g(2,(f,d)=>premises([Graph(f,d),Packed(f,d)],every(d,i=>E(a=>Carrier(f,i,a))))),
    projected_pair_total_unique:g(2,(f,d)=>premises([Graph(f,d),Packed(f,d)],every(d,i=>E(q=>C(ProjectedPair(q,f,i),A(z=>I(ProjectedPair(z,f,i),Q(z,q)))))))),
    exact_projection_exists:g(2,(f,d)=>premises([Graph(f,d),Packed(f,d)],E(g=>Exact(f,d,g)))),
    exact_projection_unique:g(4,(f,d,g,h)=>premises([Exact(f,d,g),Exact(f,d,h)],Q(g,h))),
    exact_projection_agreement:g(3,(f,d,g)=>I(Exact(f,d,g),Agreement(f,d,g))),
    exact_projection_graph:g(3,(f,d,g)=>premises([Graph(f,d),Packed(f,d),Exact(f,d,g)],Graph(g,d))),
    history_values_are_good:g(2,(f,d)=>I(Hist(f,d),Pointwise(f,d))),
    history_values_are_packed:g(2,(f,d)=>I(Hist(f,d),Packed(f,d))),
    limit_carrier_projects:g(6,(f,d,g,i,h,a)=>premises([Trans(d),Agreement(f,d,g),M(i,d),Range(f,i,h),UnionCarrier(h,a)],LimitStage(g,i,a))),
    step_projects_stage:g(7,(f,d,g,i,p,a,r)=>premises([Trans(d),Agreement(f,d,g),M(i,d),Step(f,i,p),Pair(p,a,r)],PinnedStage(g,i,a))),
    history_projection_stage_graph:g(3,(f,d,g)=>premises([Trans(d),Hist(f,d),Exact(f,d,g)],PinnedHistory(g,d))),
    carrier_history_projection_exists:g(2,(f,d)=>premises([Trans(d),Hist(f,d)],E(g=>Complete(f,d,g)))),
    ordinal_carrier_history_projection:g(2,(f,d)=>premises([Ord(d),Hist(f,d)],E(g=>Complete(f,d,g)))),
    projected_carriers_are_good:g(3,(f,d,g)=>premises([Hist(f,d),Agreement(f,d,g)],GoodCarriers(g,d)))
  },changed_contracts:{
    order_coordinate_projection:g(3,(f,d,g)=>I(Exact(f,d,g),WrongAgreement(f,d,g))),
    input_is_pinned_history:g(3,(f,d,g)=>premises([Trans(d),Hist(f,d),Exact(f,d,g)],PinnedHistory(f,d)))
  }};
}

function runCarrierHistoryProjection() {
  const defs=definition('v',true),expected=expectedCarrierHistoryProjection(defs),built=buildCarrierHistoryProjection(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(expected.formulas.pinned_stage,defs.stage)||!same(expected.formulas.pinned_stage_graph,defs.stageGraph))throw Error('pinned stage schema expansion');
  if(!same(built.formulas,expected.formulas))throw Error('independent carrier projection interfaces');
  if(!same(built.replacement_schema,expected.replacement_schema)||!scoped(expected.replacement_schema.body,3,false))throw Error('exact projection Replacement schema');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('projection proof coverage');
  const checks=[],controls=[],axioms=new Map(),verified=new Map(),logic=[];let kernelControls=0,contractControls=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function dropUniversal(p){
    if(!Array.isArray(p))return null;if(p[0]==='uI')return p[1];
    for(let i=1;i<p.length;i++){const changed=dropUniversal(p[i]);if(changed){const q=p.slice();q[i]=changed;return q;}}
    return null;
  }
  const reject=(id,fn,type='kernel')=>{if(!rejects(fn))throw Error('negative control accepted '+id);controls.push(id);if(type==='kernel')kernelControls++;else contractControls++;};
  const exact=(got,want)=>{if(!same(got,want))throw Error('projection target mismatch');};
  for(const [id,p] of Object.entries(built.proofs)) {
    if(process.env.ACE_TRACE)console.error('checking '+id);
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent projection target '+id);
    const got=kernel(0,[],p.proof,false,'ZF');exact(got.goal,expected.proofs[id]);verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','replacement'].includes(n)))throw Error('projection axiom '+id);
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    const bare=dropUniversal(p.proof);if(!bare)throw Error('missing projection universal');
    reject(id+':drop_universal',()=>kernel(0,[],bare,false,'ZF'));
    reject(id+':changed_outer_binder',()=>exact(got.goal,['E',expected.proofs[id][1]]),'contract');
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(kernel(0,[],p.proof,false,'CL').goal,expected.proofs[id]);logic.push(id);}
  }
  for(const [id,binders,count] of [['carrier_value_unique',5,4],['exact_projection_exists',2,2],['exact_projection_graph',3,3],
      ['limit_carrier_projects',6,5],['step_projects_stage',7,5],['history_projection_stage_graph',3,3],
      ['carrier_history_projection_exists',2,2],['ordinal_carrier_history_projection',2,2],['projected_carriers_are_good',3,2]]) {
    for(let k=0;k<count;k++) {
      const changed=structuredClone(expected.proofs[id]);let p=changed;
      for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<k;i++)p=p[2];p.splice(0,p.length,...p[2]);
      reject(id+':omit_premise_'+k,()=>exact(verified.get(id),changed),'contract');
    }
  }
  reject('exact_projection_agreement:wrong_packed_coordinate',()=>exact(verified.get('exact_projection_agreement'),expected.changed_contracts.order_coordinate_projection),'contract');
  reject('history_projection_stage_graph:input_as_projected_graph',()=>exact(verified.get('history_projection_stage_graph'),expected.changed_contracts.input_is_pinned_history),'contract');
  const changed=structuredClone(built.proofs.exact_projection_exists.proof);let hit=false;
  walk(changed,n=>{if(!hit&&n[0]==='axiom'&&n[1].name==='replacement'){n[1]={...n[1],body:['F']};hit=true;}});
  if(!hit)throw Error('missing live projection Replacement');
  reject('exact_projection_exists:corrupt_Replacement_body',()=>kernel(0,[],changed,false,'ZF'));
  const corrupt=structuredClone(built.proofs.carrier_value_unique.proof);let found=false;
  walk(corrupt,n=>{if(!found&&n[0]==='eqS'){n[1]=['=',0,0];found=true;}});
  if(!found)throw Error('missing carrier coordinate transport');
  reject('carrier_value_unique:corrupt_coordinate_transport',()=>kernel(0,[],corrupt,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03X',part:'packed_order_history_carrier_projection',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    exact_pinned_stage_schema_comparisons:2,exact_Replacement_schema_comparisons:1,
    logic_only_checks:logic.length,pure_logic_modules:logic,negative_controls:controls.length,
    kernel_rejection_controls:kernelControls,contract_rejection_controls:contractControls,controls,
    contract_controls_use_verified_conclusions:true,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    replacement_schema:built.replacement_schema,pinned_L_unchanged:true,
    scope:'exact unique graph of carrier coordinates, with the original pinned stageGraph recursion and a well-order on each projected carrier, conditional on the packed canonical order history',
    open_obligations:['compose the projection with actual canonical order-history existence','internal constructibility of the canonical order sets','exact relativized Choice import','formal checker soundness']};
}

export {carrierProjectionExpectedLanguage,expectedCarrierHistoryProjection,runCarrierHistoryProjection};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runCarrierHistoryProjection(),null,2));
