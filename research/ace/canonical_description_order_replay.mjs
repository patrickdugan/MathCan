// ACE-03X. Independently rebuild the exact canonical raw-description recipe.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildCanonicalDescriptionOrder} from './canonical_description_order.mjs';
import {codeOrderExpectedLanguage,expectedPairProductOrder} from './pair_product_order_replay.mjs';
import {expectedFiniteSequenceCarrier} from './finite_sequence_carrier_replay.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function expectedCanonicalDescriptionOrder(defs) {
  const l=codeOrderExpectedLanguage(defs);
  const {M,Q,I,C,A,E,some,quant,apply,free,Pair,Omega,iff,product,tripleCarrier,W,exact}=l;
  const sequence=expectedFiniteSequenceCarrier(defs).formulas;
  const lex=expectedPairProductOrder(defs).formulas.lexicographic;
  const seq=(s,w,a)=>apply(sequence.finite_tuple_carrier,s,w,a);
  const shortlex=(o,s,w,a,r)=>apply(sequence.exact_order,o,s,w,a,r);
  const nat=(r,w)=>exact([w],(ps,x,y)=>C(C(M(x,ps[0]),M(y,ps[0])),M(x,y)),r);
  const lexOrder=(t,a,b,c,r,s)=>exact([a,b,c,r,s],(ps,x,y)=>apply(lex,x,y,...ps),t);
  const finite=(g,w,a)=>some(w,m=>apply(defs.tuple,g,m,a));
  const description=(d,n,g,b)=>E(p=>C(Pair(p,g,b),Pair(d,n,p)));
  const member=(d,w,i,a)=>some(w,n=>E(g=>C(finite(g,w,i),E(b=>C(finite(b,w,a),description(d,n,g,b))))));
  const raw=(c,w,i,a)=>A(d=>iff(M(d,c),member(d,w,i,a)));
  const conjunction=xs=>xs.reduce(C);
  const facts=(w,a,r,v)=>conjunction([
    nat(v[0],w),product(w,w,v[1]),lexOrder(v[2],w,w,v[1],v[0],v[0]),
    product(w,v[1],v[3]),lexOrder(v[4],w,v[1],v[3],v[0],v[2]),
    seq(v[5],w,v[3]),shortlex(v[6],v[5],w,v[3],v[4]),
    seq(v[7],w,a),shortlex(v[8],v[7],w,a,r),
    product(v[5],v[7],v[9]),lexOrder(v[10],v[5],v[7],v[9],v[6],v[8]),
    product(w,v[9],v[11]),lexOrder(v[12],w,v[9],v[11],v[0],v[10])
  ]);
  const exs=(n,fn,vs=[])=>vs.length===n?fn(...vs):E(x=>exs(n,fn,[...vs,x]));
  const recipe=(w,a,r,i,c,t)=>exs(10,(rw,p,rp,ri,sg,rg,sb,rb,q,rq)=>facts(w,a,r,[rw,p,rp,i,ri,sg,rg,sb,rb,q,rq,c,t]));
  const construction=(w,a,r,i,c,t)=>C(recipe(w,a,r,i,c,t),C(C(tripleCarrier(i,w),raw(c,w,i,a)),W(c,t)));
  const uniques=phi=>quant(9,(w,a,r,i,c,t,j,d,u)=>I(phi(w,a,r,i,c,t),I(phi(w,a,r,j,d,u),C(C(Q(j,i),Q(d,c)),Q(u,t)))))(0);
  const f=Array.from({length:16},(_,i)=>free(i));
  return {formulas:{
    recipe:recipe(...f.slice(0,6))(0),
    construction:construction(...f.slice(0,6))(0),
    exact_recipe_facts:facts(...f.slice(0,3),f.slice(3))(0),
    triple_carrier:tripleCarrier(f[0],f[1])(0),
    raw_carrier:raw(...f.slice(0,4))(0),
    well_order:W(f[0],f[1])(0),
    product:product(...f.slice(0,3))(0),
    natural_exact_order:nat(f[0],f[1])(0),
    product_exact_order:lexOrder(...f.slice(0,6))(0),
    finite_tuple_carrier:sequence.finite_tuple_carrier,
    sequence_exact_order:sequence.exact_order
  },proofs:{
    canonical_description_auxiliaries_unique:quant(29,(w,a,r,...rest)=>{
      const left=rest.slice(0,13),right=rest.slice(13);
      return I(facts(w,a,r,left),I(facts(w,a,r,right),conjunction(right.map((v,i)=>Q(v,left[i])))));
    })(0),
    canonical_description_recipe_unique:uniques(recipe),
    canonical_description_order_unique:uniques(construction),
    canonical_description_order_exists:quant(3,(w,a,r)=>I(Omega(w),I(W(a,r),E(i=>E(c=>E(t=>construction(w,a,r,i,c,t)))))))(0)
  }};
}

function runCanonicalDescriptionOrder() {
  const defs=definition('v',true),expected=expectedCanonicalDescriptionOrder(defs),built=buildCanonicalDescriptionOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(built.formulas,expected.formulas))throw Error('independent canonical-description formula interfaces');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('canonical-description theorem coverage');
  if(!same(built.auxiliary_order,['rw','p','rp','I','ri','sg','rg','sb','rb','q','rq','C','T']))throw Error('recipe output order');
  if(!same(built.hidden_auxiliary_indices,[0,1,2,4,5,6,7,8,9,10]))throw Error('recipe existential order');
  const checks=[],controls=[],axioms=new Map(),logic=[];
  const reject=(id,fn)=>{if(!rejects(fn))throw Error('negative control accepted: '+id);controls.push(id);};
  const exact=(proof,want)=>{if(!same(kernel(0,[],proof,false,'ZF').goal,want))throw Error('wrong exact canonical-description target');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent canonical-description goal '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('canonical-description kernel target '+id);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation'].includes(n)))throw Error('unexpected canonical-description axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let bare=p.proof;while(bare[0]==='uI')bare=bare[1];
    reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('canonical-description pure logic');logic.push(id);}
  }
  function omit(id,binders,index,label) {
    const target=structuredClone(expected.proofs[id]);let p=target;
    for(let j=0;j<binders;j++)p=p[1];for(let j=0;j<index;j++)p=p[2];
    p.splice(0,p.length,...p[2]);reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,target));
  }
  omit('canonical_description_order_exists',3,0,'omega');
  omit('canonical_description_order_exists',3,1,'alphabet_order');
  omit('canonical_description_recipe_unique',9,0,'first_recipe');
  omit('canonical_description_recipe_unique',9,1,'second_recipe');
  // Changing the output order while preserving scope must fail the exact target.
  const changed=structuredClone(expected.proofs.canonical_description_order_unique);let tail=changed;
  for(let j=0;j<9;j++)tail=tail[1];tail=tail[2][2];
  tail[2]=['=',0,3];tail[1][2]=['=',1,5];
  if(same(changed,expected.proofs.canonical_description_order_unique))throw Error('output mutation changed nothing');
  reject('canonical_description_order_unique:wrong_carrier_coordinate',()=>exact(built.proofs.canonical_description_order_unique.proof,changed));
  // Corrupt an active equality substitution, so the checker must reject its derivation.
  const corrupt=structuredClone(built.proofs.canonical_description_auxiliaries_unique.proof);let hit=false;
  walk(corrupt,n=>{if(!hit&&n[0]==='eqS'){n[1]=['=',0,0];hit=true;}});
  if(!hit)throw Error('recipe omitted equality transport');
  reject('canonical_description_auxiliaries_unique:corrupt_equality_transport',()=>kernel(0,[],corrupt,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03X',part:'canonical_raw_description_order',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    logic_only_checks:logic.length,negative_controls:controls.length,controls,
    public_formula_parameters:['w','A','R','I','C','T'],auxiliary_order:built.auxiliary_order,
    hidden_auxiliary_indices:built.hidden_auxiliary_indices,exact_recipe_nodes:13,
    existence_quantifiers:['w','A','R'],existence_premises:['Omega(w)','WO(A,R)'],
    existence_conclusion:'exists I,C,T (Recipe and ((TripleCarrier and RawCarrier) and WO(C,T)))',
    uniqueness_conclusion:'((J=I and D=C) and U=T)',
    all_thirteen_auxiliaries_unique:true,ambient_choice_used:false,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'supplied omega and alphabet order determine a unique exact raw-description carrier and relation through thirteen exact construction steps',
    open_obligations:['uniform successor order on Def(A)','coherent transfinite order histories','internal constructibility of the canonical order','exact relativized Choice import','formal checker soundness']};
}

export {expectedCanonicalDescriptionOrder,runCanonicalDescriptionOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runCanonicalDescriptionOrder(),null,2));
