// ACE-03X. Independent targets for exact directed initial-segment limits.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildCanonicalLimitOrder} from './canonical_limit_order.mjs';
import {codeOrderExpectedLanguage} from './pair_product_order_replay.mjs';
import {buildCoherentWellOrder} from './coherent_well_order.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

// The expected contracts are rebuilt with depth-indexed terms. This builder
// never reads any generated formula or proof conclusion from the new module.
function canonicalLimitExpectedLanguage(defs) {
  const L=codeOrderExpectedLanguage(defs),{M,Q,I,C,A,E,every,some,quant,free,Pair,Val,iff,subset,W}=L;
  const Union=(h,u)=>A(x=>iff(M(x,u),some(h,y=>M(x,y))));
  const CarrierFamily=(h,k)=>A(a=>iff(M(a,k),E(r=>Val(h,a,r))));
  const UnionCarrier=(h,b)=>A(x=>iff(M(x,b),E(a=>E(r=>C(Val(h,a,r),M(x,a))))));
  const Phi=(h,b,x,y)=>C(C(M(x,b),M(y,b)),E(a=>E(r=>C(C(Val(h,a,r),C(M(x,a),M(y,a))),Val(r,x,y)))));
  const Exact=(h,b,t)=>A(p=>iff(M(p,t),E(x=>E(y=>C(Pair(p,x,y),Phi(h,b,x,y))))));
  const Agreement=(h,b,t)=>A(x=>A(y=>iff(Val(t,x,y),Phi(h,b,x,y))));
  const Restriction=(a,r,t)=>A(x=>A(y=>I(M(x,a),I(M(y,a),iff(Val(t,x,y),Val(r,x,y))))));
  const Initial=(a,b,t)=>every(a,x=>every(b,y=>I(Val(t,y,x),M(y,a))));
  const Local=h=>quant(2,(a,r)=>I(Val(h,a,r),W(a,r)));
  const Directed=h=>quant(4,(a,r,b,s)=>I(Val(h,a,r),I(Val(h,b,s),E(c=>E(t=>C(Val(h,c,t),C(subset(a,c),subset(b,c))))))));
  const Extends=h=>quant(4,(a,r,b,s)=>I(Val(h,a,r),I(Val(h,b,s),I(subset(a,b),C(Restriction(a,r,s),Initial(a,b,s))))));
  const State=(h,b,t)=>C(UnionCarrier(h,b),Exact(h,b,t));
  const Value=(h,p)=>E(b=>E(t=>C(Pair(p,b,t),State(h,b,t))));
  const AllExtensions=(h,b,t)=>quant(2,(a,r)=>I(Val(h,a,r),C(subset(a,b),C(Restriction(a,r,t),Initial(a,b,t)))));
  const Trans=a=>every(a,x=>subset(x,a));
  const LocalTrans=h=>quant(2,(a,r)=>I(Val(h,a,r),Trans(a)));
  const Capture=(b,k)=>quant(3,(x,y,z)=>I(M(x,b),I(M(y,b),I(M(z,b),some(k,a=>C(C(M(x,a),M(y,a)),M(z,a)))))));
  const LocalAt=(b,k,t)=>every(k,a=>C(subset(a,b),W(a,t)));
  const InitialAt=(b,k,t)=>every(k,a=>Initial(a,b,t));
  const premises=(hs,p)=>hs.reduceRight((q,h)=>I(h,q),p);
  return {...L,Union,CarrierFamily,UnionCarrier,Phi,Exact,Agreement,Restriction,Initial,Local,Directed,Extends,State,Value,AllExtensions,
    Trans,LocalTrans,Capture,LocalAt,InitialAt,premises};
}

function expectedCanonicalLimitOrder(defs) {
  const L=canonicalLimitExpectedLanguage(defs),{M,Q,I,C,A,E,quant,free,Val,subset,W,Union,CarrierFamily,UnionCarrier,Phi,Exact,Agreement,
    Restriction,Initial,Local,Directed,Extends,State,Value,AllExtensions,Trans,LocalTrans,Capture,LocalAt,InitialAt,premises}=L;
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  const common=(h,b,t)=>[UnionCarrier(h,b),Directed(h),Extends(h),Agreement(h,b,t)];
  const family=(h,b,k,t)=>[UnionCarrier(h,b),CarrierFamily(h,k),Directed(h),Extends(h),Agreement(h,b,t)];
  return {formulas:{
    carrier_family:f(2,CarrierFamily),union_carrier:f(2,UnionCarrier),order_predicate:f(4,(x,y,h,b)=>Phi(h,b,x,y)),
    exact_order:f(3,Exact),agreement:f(3,Agreement),restriction:f(3,Restriction),initial:f(3,Initial),
    local:f(1,Local),directed:f(1,Directed),extends:f(1,Extends),state:f(3,State),value:f(2,Value),
    all_extensions:f(3,AllExtensions),well_order:f(2,W),transitive:f(1,Trans),local_transitive:f(1,LocalTrans)
  },proofs:{
    limit_relation_exists:g(2,(h,b)=>E(t=>Exact(h,b,t))),
    limit_relation_unique:g(4,(h,b,t,s)=>I(Exact(h,b,t),I(Exact(h,b,s),Q(s,t)))),
    limit_relation_agreement:g(3,(h,b,t)=>I(Exact(h,b,t),Agreement(h,b,t))),
    family_coordinates_double_union:g(5,(h,u,v,a,r)=>I(Union(h,u),I(Union(u,v),I(Val(h,a,r),C(M(a,v),M(r,v)))))),
    carrier_family_exists:g(1,h=>E(k=>CarrierFamily(h,k))),
    union_carrier_exists:g(1,h=>E(b=>UnionCarrier(h,b))),
    union_carrier_unique:g(3,(h,b,c)=>I(UnionCarrier(h,b),I(UnionCarrier(h,c),Q(b,c)))),
    stage_is_subset_of_union:g(4,(h,b,a,r)=>I(UnionCarrier(h,b),I(Val(h,a,r),subset(a,b)))),
    union_carrier_transitive:g(2,(h,b)=>I(UnionCarrier(h,b),I(LocalTrans(h),Trans(b)))),
    union_order_restriction:g(5,(h,b,t,a,r)=>premises([...common(h,b,t),Val(h,a,r)],Restriction(a,r,t))),
    union_order_initial:g(5,(h,b,t,a,r)=>premises([...common(h,b,t),Val(h,a,r)],Initial(a,b,t))),
    bounded_order_agreement_transfer:g(3,(a,r,t)=>I(W(a,r),I(Restriction(a,r,t),W(a,t)))),
    directed_union_capture:g(3,(h,b,k)=>premises([UnionCarrier(h,b),CarrierFamily(h,k),Directed(h)],Capture(b,k))),
    union_local_well_orders:g(4,(h,b,k,t)=>premises([...family(h,b,k,t),Local(h)],LocalAt(b,k,t))),
    union_stages_initial:g(4,(h,b,k,t)=>premises(family(h,b,k,t),InitialAt(b,k,t))),
    union_order_well_order:g(3,(h,b,t)=>premises([...common(h,b,t),Local(h)],W(b,t))),
    limit_state_exists:g(1,h=>E(b=>E(t=>State(h,b,t)))),
    limit_state_unique:g(5,(h,b,t,c,s)=>I(State(h,b,t),I(State(h,c,s),C(Q(b,c),Q(t,s))))),
    limit_state_well_order:g(3,(h,b,t)=>premises([Local(h),Directed(h),Extends(h),State(h,b,t)],W(b,t))),
    limit_state_extensions:g(3,(h,b,t)=>premises([Directed(h),Extends(h),State(h,b,t)],AllExtensions(h,b,t))),
    canonical_limit_complete:g(1,h=>premises([Local(h),Directed(h),Extends(h)],E(b=>E(t=>C(State(h,b,t),C(W(b,t),AllExtensions(h,b,t))))))),
    packed_limit_value_exists:g(1,h=>E(p=>Value(h,p))),
    packed_limit_value_unique:g(3,(h,p,q)=>I(Value(h,p),I(Value(h,q),Q(p,q))))
  },false_agreement_uniqueness:g(4,(h,b,t,s)=>I(Agreement(h,b,t),I(Agreement(h,b,s),Q(s,t))))};
}

function finiteHistoryControls() {
  const subset=(a,b)=>a.every(x=>b.includes(x)),edge=(r,x,y)=>r.some(([u,v])=>u===x&&v===y);
  const wo=({a,r})=>a.every(x=>!edge(r,x,x))&&a.every(x=>a.every(y=>a.every(z=>!edge(r,x,y)||!edge(r,y,z)||edge(r,x,z))))&&
    a.every(x=>a.every(y=>x===y||edge(r,x,y)||edge(r,y,x)));
  const local=h=>h.every(wo),directed=h=>h.every(x=>h.every(y=>h.some(z=>subset(x.a,z.a)&&subset(y.a,z.a))));
  const extendsAll=h=>h.every(x=>h.every(y=>!subset(x.a,y.a)||(x.a.every(a=>x.a.every(b=>edge(x.r,a,b)===edge(y.r,a,b)))&&
    x.a.every(a=>y.a.every(b=>!edge(y.r,b,a)||x.a.includes(b))))));
  const fixtures=[
    {omitted:'local',history:[{a:[0],r:[[0,0]]}]},
    {omitted:'directed',history:[{a:[0],r:[]},{a:[1],r:[]}]},
    {omitted:'extends',history:[{a:[0,1],r:[[0,1]]},{a:[0,1,2],r:[[1,0],[1,2],[0,2]]}]}
  ];
  return fixtures.map(({omitted,history})=>{
    const a=[...new Set(history.flatMap(x=>x.a))],r=[];
    for(const x of a)for(const y of a)if(history.some(s=>s.a.includes(x)&&s.a.includes(y)&&edge(s.r,x,y)))r.push([x,y]);
    const premises={local:local(history),directed:directed(history),extends:extendsAll(history)},well_order=wo({a,r});
    if(premises[omitted]||Object.entries(premises).some(([k,v])=>k!==omitted&&!v)||well_order)throw Error('history control failed '+omitted);
    return {omitted,premises,union_well_order:well_order,carrier_size:a.length};
  });
}

function runCanonicalLimitOrder() {
  const defs=definition('v',true),actual=buildCanonicalLimitOrder(defs),expected=expectedCanonicalLimitOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas))throw Error('independent limit formula interfaces');
  if(!same(actual.formulas.well_order,buildCoherentWellOrder(defs).formulas.well_order))throw Error('shared well-order layout');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('proof coverage');
  const checks=[],controls=[],schemas=new Map(),verified=new Map();let logic=0,kernelControls=0,contractControls=0;
  const reject=(id,fn,type='kernel')=>{if(!rejects(fn))throw Error('negative control accepted '+id);controls.push(id);if(type==='kernel')kernelControls++;else contractControls++;};
  const exact=(got,want)=>{if(!same(got,want))throw Error('independent contract mismatch');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent limit target '+id);
    const got=kernel(0,[],p.proof,false,'ZF');exact(got.goal,expected.proofs[id]);verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);schemas.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>!['pairing','union','power','separation','extensionality'].includes(x)))throw Error('limit axiom '+id);
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(got.goal,['E',expected.proofs[id][1]]),'contract');
    let unbound=p.proof;while(unbound[0]==='uI')unbound=unbound[1];
    reject(id+':dropped_binders',()=>kernel(0,[],unbound,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(kernel(0,[],p.proof,false,'CL').goal,expected.proofs[id]);logic++;}
  }
  for(const [id,binders,count] of [['union_order_well_order',3,5],['limit_state_well_order',3,4],
      ['limit_state_extensions',3,3],['canonical_limit_complete',1,3],['union_carrier_transitive',2,2]]) {
    for(let k=0;k<count;k++) {
      const changed=structuredClone(expected.proofs[id]);let n=changed;
      for(let i=0;i<binders;i++)n=n[1];for(let i=0;i<k;i++)n=n[2];n.splice(0,n.length,...n[2]);
      reject(id+':omitted_premise_'+k,()=>exact(verified.get(id),changed),'contract');
    }
  }
  reject('limit_relation_unique:Val_only_membership',()=>exact(verified.get('limit_relation_unique'),expected.false_agreement_uniqueness),'contract');
  for(const [axiom,replacement] of [['union',{name:'power'}],['separation',null]]) {
    const changed=structuredClone(actual.proofs.carrier_family_exists.proof);let hit=false;
    walk(changed,n=>{if(!hit&&n[0]==='axiom'&&n[1].name===axiom){n[1]=replacement??{...n[1],body:['F']};hit=true;}});
    if(!hit)throw Error('missing live '+axiom+' mutation');
    reject('carrier_family_exists:corrupt_'+axiom,()=>kernel(0,[],changed,false,'ZF'));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  const fixtures=finiteHistoryControls();
  return {experiment:'ACE-03X',part:'canonical_limit_order_sets',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    shared_well_order_layout_checks:1,logic_only_checks:logic,negative_controls:controls.length,
    kernel_rejection_controls:kernelControls,contract_rejection_controls:contractControls,controls,finite_history_controls:fixtures,
    ambient_axiom_instances:[...schemas.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'unconditional exact carrier and canonical relation sets from any set of packed states; unique packed output; transitivity and coherent limit well-order with restriction and initiality under explicit history hypotheses',
    open_obligations:['the indexed constructible history must supply local well-orders, directedness and initial-segment coherence','internal constructibility of the canonical relation sets','relativized Choice import','formal checker soundness']};
}

export {canonicalLimitExpectedLanguage,expectedCanonicalLimitOrder,finiteHistoryControls,runCanonicalLimitOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runCanonicalLimitOrder(),null,2));
