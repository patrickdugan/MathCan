// ACE-03W. Independent exact finite-tuple carrier and canonical-order targets.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildFiniteSequenceCarrier } from './finite_sequence_carrier.mjs';
import { buildRealization } from './relation_realization.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedFiniteSequenceCarrier(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y);
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const iff=(p,q)=>and(imp(p,q),imp(q,p)),no=p=>imp(p,()=>['F']);
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)],ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const each=(s,fn)=>all(x=>imp(mem(x,s),fn(x))),some=(s,fn)=>ex(x=>and(mem(x,s),fn(x)));
  const free=i=>d=>d+i;
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const apply=(p,...args)=>d=>embed(p,args.map(t=>t(d))),term=(name,...args)=>apply(defs[name],...args);
  const val=(f,i,y)=>term('val',f,i,y),tuple=(f,m,a)=>term('tuple',f,m,a),pair=(p,x,y)=>term('pair',p,x,y);
  const subset=(s,a)=>each(s,x=>mem(x,a)),nonempty=s=>ex(x=>mem(x,s));
  const power=(b,p)=>all(x=>iff(mem(x,p),subset(x,b)));
  const irr=(s,lt)=>each(s,x=>no(lt(x,x)));
  const trans=(s,lt)=>forall(3,(x,y,z)=>imp(mem(x,s),imp(mem(y,s),imp(mem(z,s),imp(lt(x,y),imp(lt(y,z),lt(x,z)))))));
  const total=(s,lt)=>forall(2,(x,y)=>imp(mem(x,s),imp(mem(y,s),or(eq(x,y),or(lt(x,y),lt(y,x))))));
  const minima=(s,lt)=>all(t=>imp(subset(t,s),imp(nonempty(t),ex(x=>and(mem(x,t),each(t,y=>no(lt(y,x))))))));
  const wo=(s,lt)=>and(and(and(irr(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const before=(f,g,k)=>each(k,i=>all(x=>all(y=>imp(val(f,i,x),imp(val(g,i,y),eq(x,y))))));
  const lex=(f,g,m,r)=>some(m,k=>ex(x=>ex(y=>and(and(and(val(f,k,x),val(g,k,y)),val(r,x,y)),before(f,g,k)))));
  const shortlex=(f,g,w,a,r)=>some(w,m=>some(w,n=>and(and(tuple(f,m,a),tuple(g,n,a)),
    or(mem(m,n),and(eq(m,n),lex(f,g,m,r))))));
  const carrier=(s,w,a)=>all(f=>iff(mem(f,s),some(w,m=>tuple(f,m,a))));
  const family=(s,w,a)=>each(s,f=>some(w,m=>tuple(f,m,a)));
  const phi=(s,w,a,r,f,g)=>and(and(mem(f,s),mem(g,s)),shortlex(f,g,w,a,r));
  const exact=(o,s,w,a,r)=>all(p=>iff(mem(p,o),ex(f=>ex(g=>and(pair(p,f,g),phi(s,w,a,r,f,g))))));
  const agree=(o,s,w,a,r)=>all(f=>all(g=>iff(val(o,f,g),phi(s,w,a,r,f,g))));
  const unique=(o,s,w,a,r)=>all(other=>imp(exact(other,s,w,a,r),eq(other,o)));
  const complete=(o,s,w,a,r)=>and(and(and(exact(o,s,w,a,r),agree(o,s,w,a,r)),wo(s,(f,g)=>val(o,f,g))),unique(o,s,w,a,r));
  const orderHyp=(s,w,a,r,conclusion)=>imp(term('omega',w),imp(wo(a,(x,y)=>val(r,x,y)),imp(carrier(s,w,a),conclusion)));
  const proofs={
    tuple_values_belong_to_carrier:forall(5,(f,m,a,i,y)=>imp(tuple(f,m,a),imp(mem(i,m),imp(val(f,i,y),mem(y,a)))))(0),
    tuple_graph_double_power_bound:forall(6,(f,m,a,b,p1,p2)=>imp(subset(m,b),imp(subset(a,b),
      imp(power(b,p1),imp(power(p1,p2),imp(tuple(f,m,a),subset(f,p2)))))))(0),
    finite_sequence_carrier_exists:forall(2,(w,a)=>ex(s=>carrier(s,w,a)))(0),
    finite_sequence_carrier_unique:forall(4,(w,a,s,t)=>imp(carrier(s,w,a),imp(carrier(t,w,a),eq(s,t))))(0),
    finite_sequence_carrier_is_family:forall(3,(s,w,a)=>imp(carrier(s,w,a),family(s,w,a)))(0),
    shortlex_explicit_carrier_guards:forall(4,(s,w,a,r)=>imp(wo(s,(f,g)=>shortlex(f,g,w,a,r)),wo(s,(f,g)=>phi(s,w,a,r,f,g))))(0),
    finite_sequence_carrier_well_order:forall(4,(s,w,a,r)=>orderHyp(s,w,a,r,wo(s,(f,g)=>phi(s,w,a,r,f,g))))(0),
    shortlex_exact_membership_exists:forall(4,(s,w,a,r)=>ex(o=>exact(o,s,w,a,r)))(0),
    shortlex_exact_membership_unique:forall(4,(s,w,a,r)=>all(o=>all(p=>imp(exact(o,s,w,a,r),imp(exact(p,s,w,a,r),eq(p,o))))))(0),
    shortlex_exact_membership_pair_only:forall(4,(s,w,a,r)=>all(o=>imp(exact(o,s,w,a,r),each(o,p=>
      ex(f=>ex(g=>and(and(mem(f,s),mem(g,s)),pair(p,f,g))))))))(0),
    shortlex_exact_membership_implies_agreement:forall(4,(s,w,a,r)=>all(o=>imp(exact(o,s,w,a,r),agree(o,s,w,a,r))))(0),
    shortlex_canonical_unique_relation:forall(4,(s,w,a,r)=>ex(o=>and(exact(o,s,w,a,r),unique(o,s,w,a,r))))(0),
    shortlex_canonical_well_order_realization:forall(4,(s,w,a,r)=>imp(wo(s,(f,g)=>phi(s,w,a,r,f,g)),ex(o=>complete(o,s,w,a,r))))(0),
    shortlex_composed_canonical_well_order:forall(4,(s,w,a,r)=>orderHyp(s,w,a,r,ex(o=>complete(o,s,w,a,r))))(0),
    finite_sequence_carrier_and_canonical_order:forall(3,(w,a,r)=>imp(term('omega',w),imp(wo(a,(x,y)=>val(r,x,y)),
      ex(s=>and(carrier(s,w,a),ex(o=>complete(o,s,w,a,r)))))))(0)
  };
  return {proofs,formulas:{
    finite_tuple_carrier:carrier(free(0),free(1),free(2))(0),
    finite_tuple_family:family(free(0),free(1),free(2))(0),
    guarded_shortlex:phi(free(2),free(3),free(4),free(5),free(0),free(1))(0),
    exact_order:exact(free(0),free(1),free(2),free(3),free(4))(0),
    order_agreement:agree(free(0),free(1),free(2),free(3),free(4))(0),
    unique_order:unique(free(0),free(1),free(2),free(3),free(4))(0),
    complete_order:complete(free(0),free(1),free(2),free(3),free(4))(0)
  }};
}

function runFiniteSequenceCarrier() {
  const defs=definition('v',true),built=buildFiniteSequenceCarrier(defs),expected=expectedFiniteSequenceCarrier(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(built.formulas,expected.formulas))throw Error('independent sequence carrier interfaces');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('sequence carrier theorem coverage');
  if(!same(built.proofs.tuple_values_belong_to_carrier.goal,built.existing_tuple_range.goal))throw Error('existing tuple-range statement identity');
  const sameRangeTree=same(built.proofs.tuple_values_belong_to_carrier.proof,built.existing_tuple_range.proof);
  const checks=[],controls=[],axioms=new Map(),logic=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('wrong exact carrier goal');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent carrier goal '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('carrier kernel goal '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(a=>!['pairing','union','power','separation','extensionality','foundation'].includes(a)))throw Error('unexpected carrier axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort(),
      ...(id==='tuple_values_belong_to_carrier'?{existing_statement:'finite_sequence_order.tuple_value_in_carrier',identical_existing_proof_tree:sameRangeTree}:{})});
    let stripped=p.proof,removed=0;while(stripped[0]==='uI'){stripped=stripped[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],stripped,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('carrier pure-logic target');logic.push(id);}
  }
  function omit(id,binders,index,label) {
    const changed=structuredClone(expected.proofs[id]);let p=changed;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,changed));
  }
  omit('tuple_graph_double_power_bound',6,0,'domain_bound');
  omit('tuple_graph_double_power_bound',6,1,'range_bound');
  omit('finite_sequence_carrier_well_order',4,2,'exact_carrier');
  omit('finite_sequence_carrier_and_canonical_order',3,0,'omega');
  omit('finite_sequence_carrier_and_canonical_order',3,1,'alphabet_well_order');
  omit('shortlex_exact_membership_implies_agreement',5,0,'exact_membership');
  const damaged=structuredClone(built.proofs.finite_sequence_carrier_exists.proof);let hit=false;
  walk(damaged,n=>{
    if(hit||n[0]!=='axiom'||n[1].name!=='separation')return;
    function alter(p){if(hit||!Array.isArray(p))return;if(p[0]==='M'||p[0]==='='){p[0]=p[0]==='M'?'=':'M';hit=true;return;}for(const q of p)alter(q);}
    alter(n[1].body);
  });
  if(!hit)throw Error('missing live carrier separation');
  reject('carrier_exists:corrupt_separation_predicate',()=>kernel(0,[],damaged,false,'ZF'));
  const unguarded=expected.formulas.guarded_shortlex[2];
  reject('realization:omit_carrier_guards',()=>buildRealization(defs,unguarded,4,0));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'exact_finite_sequence_carrier_and_canonical_shortlex',checks,
    checked_modules:checks.length,new_statement_checks:checks.length-1,reused_helper_checks:sameRangeTree?1:0,
    reproved_existing_statement_checks:sameRangeTree?0:1,existing_statement_identity_checks:1,
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),negative_controls:controls.length,controls,pure_logic_checks:logic,
    unconditional_carrier_quantifiers:['w','A'],unconditional_carrier_premises:[],
    carrier_membership:'f in S iff exists m in w Tuple(f,m,A)',
    carrier_bound:'P^3((union w) union A)',
    main_quantifier_order:['w','A','R'],main_premises:['Omega(w)','WO(A,Val(R))'],
    main_conclusion:'exists S (ExactSeq(S,w,A) and exists T (Exact(T) and Agreement(T) and WO(S,Val(T)) and Unique(T)))',
    canonical_order_guards:['f in S','g in S'],
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'unconditional exact tuple-domain carrier existence and uniqueness; supplied omega and alphabet well-order yield a canonical set-coded shortlex well-order on all finite tuples',
    open_obligations:['coding normalized programs and parameter tuples in the description carrier','internal constructibility of code orders','exact relativized Choice import','formal checker soundness']};
}

export { expectedFiniteSequenceCarrier, runFiniteSequenceCarrier };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runFiniteSequenceCarrier(),null,2));
