// ACE-03X. Independent indexed-history to directed-family contracts.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildIndexedOrderFamily} from './indexed_order_family.mjs';
import {canonicalLimitExpectedLanguage} from './canonical_limit_order_replay.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function indexedOrderFamilyExpectedLanguage(defs) {
  const l=canonicalLimitExpectedLanguage(defs),{M,I,C,A,E,every,some,quant,apply,Pair,Val,iff,subset,W,Trans,
    Restriction,Initial,Local,LocalTrans,Directed,Extends,State,AllExtensions,Value}=l;
  const Graph=(g,d)=>apply(defs.graph,g,d),Ord=d=>apply(defs.ordinal,d);
  const Range=(g,d,h)=>A(p=>iff(M(p,h),some(d,i=>Val(g,i,p))));
  const At=(g,i,a,r)=>E(p=>C(Val(g,i,p),Pair(p,a,r)));
  const Embed=(a,r,b,s)=>C(subset(a,b),C(Restriction(a,r,s),Initial(a,b,s)));
  const IndexedLocal=(g,d)=>quant(3,(i,a,r)=>I(M(i,d),I(At(g,i,a,r),W(a,r))));
  const IndexedTrans=(g,d)=>quant(3,(i,a,r)=>I(M(i,d),I(At(g,i,a,r),Trans(a))));
  const Forward=(g,d)=>quant(6,(i,j,a,r,b,s)=>I(M(i,d),I(M(j,d),I(At(g,i,a,r),I(At(g,j,b,s),I(M(i,j),Embed(a,r,b,s)))))));
  const IndexedExtensions=(g,d,b,t)=>quant(3,(i,a,r)=>I(M(i,d),I(At(g,i,a,r),Embed(a,r,b,t))));
  const Good=p=>E(a=>E(r=>C(Pair(p,a,r),C(Trans(a),W(a,r)))));
  const PackedEmbed=(p,q)=>E(a=>E(r=>E(b=>E(s=>C(C(Pair(p,a,r),Pair(q,b,s)),Embed(a,r,b,s))))));
  const Pointwise=(g,d)=>every(d,i=>A(p=>I(Val(g,i,p),Good(p))));
  const PackedForward=(g,d)=>every(d,i=>every(d,j=>I(M(i,j),A(p=>A(q=>I(Val(g,i,p),I(Val(g,j,q),PackedEmbed(p,q))))))));
  const Prior=(g,d,q)=>every(d,i=>A(p=>I(Val(g,i,p),PackedEmbed(p,q))));
  return {...l,Graph,Ord,Range,At,Embed,IndexedLocal,IndexedTrans,Forward,IndexedExtensions,Good,PackedEmbed,Pointwise,PackedForward,Prior};
}

function expectedIndexedOrderFamily(defs) {
  const l=indexedOrderFamilyExpectedLanguage(defs),{M,Q,I,C,O,A,E,quant,free,Val,W,Trans,Local,LocalTrans,Directed,Extends,State,AllExtensions,Value,
    Graph,Ord,Range,At,Embed,IndexedLocal,IndexedTrans,Forward,IndexedExtensions,Good,PackedEmbed,Pointwise,PackedForward,Prior,premises}=l;
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  const family=(f,d,h)=>[Ord(d),Graph(f,d),Range(f,d,h),Forward(f,d)];
  const packed=(f,d,h)=>[Ord(d),Graph(f,d),Range(f,d,h),Pointwise(f,d),PackedForward(f,d)];
  return {formulas:{
    prefix_range:f(3,Range),at:f(4,At),embedding:f(4,Embed),indexed_local:f(2,IndexedLocal),indexed_transitive:f(2,IndexedTrans),
    forward:f(2,Forward),indexed_extensions:f(4,IndexedExtensions),local:f(1,Local),local_transitive:f(1,LocalTrans),
    directed:f(1,Directed),extends:f(1,Extends),limit_state:f(3,State),all_extensions:f(3,AllExtensions),well_order:f(2,W),transitive:f(1,Trans),
    good:f(1,Good),packed_embed:f(2,PackedEmbed),packed_pointwise:f(2,Pointwise),packed_forward:f(2,PackedForward),packed_prior:f(3,Prior),limit_value:f(2,Value)
  },proofs:{
    indexed_ordinal_member:g(2,(d,i)=>I(Ord(d),I(M(i,d),Ord(i)))),
    indexed_ordinal_comparison:A(a=>I(Ord(a),A(b=>I(Ord(b),O(M(a,b),O(Q(a,b),M(b,a)))))))(0),
    indexed_coordinates_unique:g(7,(f,d,i,a,r,b,s)=>premises([Graph(f,d),M(i,d),At(f,i,a,r),At(f,i,b,s)],C(Q(a,b),Q(r,s)))),
    indexed_family_local:g(3,(f,d,h)=>premises([Range(f,d,h),IndexedLocal(f,d)],Local(h))),
    indexed_family_transitive:g(3,(f,d,h)=>premises([Range(f,d,h),IndexedTrans(f,d)],LocalTrans(h))),
    indexed_family_directed:g(3,(f,d,h)=>premises(family(f,d,h),Directed(h))),
    indexed_family_extends:g(3,(f,d,h)=>premises(family(f,d,h),Extends(h))),
    indexed_family_extensions:g(5,(f,d,h,b,t)=>premises([Range(f,d,h),AllExtensions(h,b,t)],IndexedExtensions(f,d,b,t))),
    packed_indexed_local:g(2,(f,d)=>I(Pointwise(f,d),IndexedLocal(f,d))),
    packed_indexed_transitive:g(2,(f,d)=>I(Pointwise(f,d),IndexedTrans(f,d))),
    packed_indexed_forward:g(2,(f,d)=>I(PackedForward(f,d),Forward(f,d))),
    indexed_canonical_limit_complete:g(3,(f,d,h)=>premises([Ord(d),Graph(f,d),Range(f,d,h),IndexedLocal(f,d),IndexedTrans(f,d),Forward(f,d)],
      E(b=>E(t=>C(State(h,b,t),C(C(Trans(b),W(b,t)),IndexedExtensions(f,d,b,t))))))),
    packed_indexed_limit_properties:g(4,(f,d,h,p)=>premises([...packed(f,d,h),Value(h,p)],C(Good(p),Prior(f,d,p)))),
    packed_indexed_limit_complete:g(3,(f,d,h)=>premises(packed(f,d,h),E(p=>C(Value(h,p),C(Good(p),Prior(f,d,p))))))
  }};
}

function runIndexedOrderFamily() {
  const defs=definition('v',true),expected=expectedIndexedOrderFamily(defs),actual=buildIndexedOrderFamily(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas))throw Error('independent indexed-family interfaces');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('indexed-family proof coverage');
  const checks=[],controls=[],axioms=new Map(),verified=new Map();let logic=0,kernelControls=0,contractControls=0;
  const reject=(id,fn,type='kernel')=>{if(!rejects(fn))throw Error('negative control accepted: '+id);controls.push(id);if(type==='kernel')kernelControls++;else contractControls++;};
  const exact=(got,want)=>{if(!same(got,want))throw Error('indexed-family exact target');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const q of p)if(Array.isArray(q))walk(q,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent indexed-family target '+id);
    let got;
    try {got=kernel(0,[],p.proof,false,'ZF');} catch(error) {throw new Error('indexed-family kernel '+id+': '+error.message,{cause:error});}
    exact(got.goal,expected.proofs[id]);verified.set(id,got.goal);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation'].includes(n)))throw Error('unexpected indexed-family axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(got.goal,['E',expected.proofs[id][1]]),'contract');
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(kernel(0,[],p.proof,false,'CL').goal,p.goal);logic++;}
  }
  for(const [id,binders,count] of [['indexed_coordinates_unique',7,4],['indexed_family_local',3,2],['indexed_family_transitive',3,2],
    ['indexed_family_directed',3,4],['indexed_family_extends',3,4],['indexed_canonical_limit_complete',3,6],
    ['packed_indexed_limit_properties',4,6],['packed_indexed_limit_complete',3,5]]) {
    for(let k=0;k<count;k++) {
      const changed=structuredClone(expected.proofs[id]);let p=changed;
      for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<k;i++)p=p[2];p.splice(0,p.length,...p[2]);
      reject(id+':omitted_premise_'+k,()=>exact(verified.get(id),changed),'contract');
    }
  }
  const broken=structuredClone(actual.proofs.indexed_family_extends.proof);let hit=false;
  walk(broken,n=>{if(!hit&&n[0]==='eqS'){n[1]=['=',0,0];hit=true;}});
  if(!hit)throw Error('missing same-index equality transport');
  reject('indexed_family_extends:corrupt_coordinate_transport',()=>kernel(0,[],broken,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  // A single index with two incompatible values satisfies vacuous forward
  // conditions; Graph is needed to exclude this case.
  const carriers=[[0],[1]],subset=(a,b)=>a.every(x=>b.includes(x));
  const directed=carriers.every(a=>carriers.every(b=>carriers.some(c=>subset(a,c)&&subset(b,c))));
  if(directed)throw Error('multivalued graph counterexample unexpectedly directed');
  return {experiment:'ACE-03X',part:'indexed_order_family_adapter',checks,
    checked_modules:checks.length,new_statement_checks:checks.length-2,reproved_existing_statement_checks:2,
    existing_statements:{indexed_ordinal_member:'stage_recursion.ordinal_member',indexed_ordinal_comparison:'constructible_power.ordinal_comparison'},
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    logic_only_checks:logic,negative_controls:controls.length,kernel_rejection_controls:kernelControls,contract_rejection_controls:contractControls,controls,
    packed_limit_quantifiers:['f','d','H','r'],packed_limit_premises:['Ord(d)','Graph(f,d)','Range(f,d,H)','PointwiseGood(f,d)','ForwardEmbeddings(f,d)','Value(H,r)'],
    packed_limit_conclusion:'Good(r) and forall i in d forall p (Val(f,i,p) implies Embed(p,r))',
    same_index_requires_graph_functionality:true,multivalued_single_index_control:{carrier_count:2,forward_vacuous:true,directed:false},
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,ambient_choice_used:false,
    scope:'indexed ordinal histories with pointwise good states and forward initial embeddings yield canonical directed initial-segment limits; unrelated relation members are excluded by exact limit membership'};
}

export {indexedOrderFamilyExpectedLanguage,expectedIndexedOrderFamily,runIndexedOrderFamily};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runIndexedOrderFamily(),null,2));
