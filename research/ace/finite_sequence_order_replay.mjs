// ACE-03W. Independent finite-tuple and shortlex theorem interfaces.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildFiniteSequenceOrder } from './finite_sequence_order.mjs';
import { expectedOmegaInduction } from './omega_well_order_replay.mjs';
import { expectedLexicographicPullback } from './lexicographic_pullback_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedFiniteSequenceOrder(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y),bot=()=>['F'];
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const no=p=>imp(p,bot),iff=(p,q)=>and(imp(p,q),imp(q,p));
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
  const apply=(p,...args)=>d=>embed(p,args.map(t=>t(d)));
  const term=(name,...args)=>apply(defs[name],...args);
  const val=(f,i,x)=>term('val',f,i,x),graph=(f,n)=>term('graph',f,n),tuple=(f,n,a)=>term('tuple',f,n,a);
  const succ=(n,d)=>term('successor',n,d),omega=w=>term('omega',w),empty=n=>term('empty',n);
  const subset=(s,a)=>each(s,x=>mem(x,a)),transitive=n=>each(n,k=>subset(k,n));
  const nonempty=s=>ex(x=>mem(x,s));
  const irr=(a,lt)=>each(a,x=>no(lt(x,x)));
  const trans=(a,lt)=>forall(3,(x,y,z)=>imp(mem(x,a),imp(mem(y,a),imp(mem(z,a),imp(lt(x,y),imp(lt(y,z),lt(x,z)))))));
  const total=(a,lt)=>forall(2,(x,y)=>imp(mem(x,a),imp(mem(y,a),or(eq(x,y),or(lt(x,y),lt(y,x))))));
  const minima=(a,lt)=>all(s=>imp(subset(s,a),imp(nonempty(s),ex(x=>and(mem(x,s),each(s,y=>no(lt(y,x))))))));
  const wo=(a,lt)=>and(and(and(irr(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const prefix=(h,f,n)=>and(graph(h,n),each(n,i=>all(x=>iff(val(h,i,x),val(f,i,x)))));
  const before=(f,g,k)=>each(k,i=>all(x=>all(y=>imp(val(f,i,x),imp(val(g,i,y),eq(x,y))))));
  const lex=(f,g,n,r)=>some(n,k=>ex(x=>ex(y=>and(and(and(val(f,k,x),val(g,k,y)),val(r,x,y)),before(f,g,k)))));
  const family=(s,n,a)=>each(s,f=>tuple(f,n,a));
  const good=(n,a,r)=>all(s=>imp(family(s,n,a),wo(s,(f,g)=>lex(f,g,n,r))));
  const finiteFamily=(s,w,a)=>each(s,f=>some(w,n=>tuple(f,n,a)));
  const finiteCarrier=(s,w,a)=>all(f=>iff(mem(f,s),some(w,n=>tuple(f,n,a))));
  const shortlex=(f,g,w,a,r)=>some(w,m=>some(w,n=>and(and(tuple(f,m,a),tuple(g,n,a)),
    or(mem(m,n),and(eq(m,n),lex(f,g,m,r))))));
  const fibre=(t,s,n,a)=>all(f=>iff(mem(f,t),and(mem(f,s),tuple(f,n,a))));
  const fibres=(s,w,a,r)=>each(w,n=>ex(t=>and(fibre(t,s,n,a),wo(t,(f,g)=>lex(f,g,n,r)))));
  const rep=(f,h,x,n)=>and(prefix(h,f,n),val(f,n,x));
  const cover=(s,p,n,a)=>each(s,f=>some(p,h=>some(a,x=>rep(f,h,x,n))));
  const functional=(s,n)=>forall(5,(f,h,x,q,y)=>imp(mem(f,s),imp(rep(f,h,x,n),imp(rep(f,q,y,n),and(eq(h,q),eq(x,y))))));
  const injective=(s,n)=>forall(4,(f,g,h,x)=>imp(mem(f,s),imp(mem(g,s),imp(rep(f,h,x,n),imp(rep(g,h,x,n),eq(f,g))))));
  const forms={
    prefix:prefix(free(0),free(1),free(2))(0),
    before:before(free(0),free(1),free(2))(0),
    lex:lex(free(0),free(1),free(2),free(3))(0),
    tuple_family:family(free(0),free(1),free(2))(0),
    finite_lex_property:good(free(0),free(1),free(2))(0),
    finite_tuple_family:finiteFamily(free(0),free(1),free(2))(0),
    finite_tuple_carrier:finiteCarrier(free(0),free(1),free(2))(0),
    shortlex:shortlex(free(0),free(1),free(2),free(3),free(4))(0),
    tuple_fibre:fibre(free(0),free(1),free(2),free(3))(0),
    ordered_tuple_fibres:fibres(free(0),free(1),free(2),free(3))(0)
  };
  const productSpec={paramCount:5,firstCarrier:4,secondCarrier:1,outputCarrier:3,
    firstOrder:lex(free(0),free(1),free(2),free(4))(0),
    secondOrder:val(free(4),free(0),free(1))(0),
    representation:rep(free(0),free(1),free(2),free(3))(0)};
  const product=expectedLexicographicPullback(defs,productSpec);
  const productLex=(f,g,n,a,r,s,p)=>apply(product.formulas.lexicographic,f,g,n,a,r,s,p);
  const agreement=(s,p,n,d,a,r)=>forall(2,(f,g)=>imp(mem(f,s),imp(mem(g,s),
    iff(productLex(f,g,n,a,r,s,p),lex(f,g,d,r)))));
  const proofs={
    prefix_graph_exists:forall(3,(f,d,n)=>imp(graph(f,d),imp(subset(n,d),
      ex(h=>and(subset(h,f),prefix(h,f,n))))))(0),
    prefix_graph_unique:forall(4,(p,q,f,n)=>imp(prefix(p,f,n),imp(prefix(q,f,n),eq(p,q))))(0),
    prefixes_equal_from_before:forall(5,(p,q,f,g,n)=>imp(prefix(p,f,n),imp(prefix(q,g,n),imp(before(f,g,n),eq(p,q)))))(0),
    tuple_value_in_carrier:forall(5,(f,n,a,i,x)=>imp(tuple(f,n,a),imp(mem(i,n),imp(val(f,i,x),mem(x,a)))))(0),
    prefix_is_tuple:forall(5,(h,f,n,d,a)=>imp(tuple(f,d,a),imp(subset(n,d),imp(prefix(h,f,n),tuple(h,n,a)))))(0),
    prefix_last_value_functional:forall(7,(f,p,q,n,d,x,y)=>imp(succ(n,d),imp(graph(f,d),imp(prefix(p,f,n),
      imp(prefix(q,f,n),imp(val(f,n,x),imp(val(f,n,y),and(eq(p,q),eq(x,y)))))))))(0),
    prefix_last_value_injective:forall(6,(f,g,p,n,d,x)=>imp(succ(n,d),imp(graph(f,d),imp(graph(g,d),
      imp(prefix(p,f,n),imp(prefix(p,g,n),imp(val(f,n,x),imp(val(g,n,x),eq(f,g)))))))))(0),
    successor_lex_prefix_last:forall(9,(f,g,p,q,n,d,r,x,y)=>imp(succ(n,d),imp(transitive(n),
      imp(graph(f,d),imp(graph(g,d),imp(prefix(p,f,n),imp(prefix(q,g,n),imp(val(f,n,x),imp(val(g,n,y),
        iff(lex(f,g,d,r),or(lex(p,q,n,r),and(eq(p,q),val(r,x,y)))))))))))))(0),
    empty_length_lex_well_order:forall(3,(n,a,r)=>imp(empty(n),good(n,a,r)))(0),
    prefix_carrier_exists:forall(4,(s,n,d,a)=>imp(succ(n,d),imp(family(s,d,a),
      ex(p=>and(family(p,n,a),cover(s,p,n,a))))))(0),
    prefix_representation_laws:forall(4,(s,n,d,a)=>imp(succ(n,d),imp(family(s,d,a),and(functional(s,n),injective(s,n)))))(0),
    prefix_lex_agreement:forall(6,(s,p,n,d,a,r)=>imp(succ(n,d),imp(transitive(n),imp(family(s,d,a),
      imp(cover(s,p,n,a),agreement(s,p,n,d,a,r))))))(0),
    prefix_order_agreement_transfer:forall(6,(s,p,n,d,a,r)=>imp(agreement(s,p,n,d,a,r),
      imp(wo(s,(f,g)=>productLex(f,g,n,a,r,s,p)),wo(s,(f,g)=>lex(f,g,d,r)))))(0),
    successor_length_lex_well_order:forall(4,(n,d,a,r)=>imp(succ(n,d),imp(transitive(n),
      imp(wo(a,(x,y)=>val(r,x,y)),imp(good(n,a,r),good(d,a,r))))))(0),
    tuple_length_induction:expectedOmegaInduction(defs,forms.finite_lex_property,2),
    finite_length_lex_well_order:forall(4,(w,a,r,m)=>imp(omega(w),imp(wo(a,(x,y)=>val(r,x,y)),imp(mem(m,w),good(m,a,r)))))(0),
    exact_graph_domain_unique:forall(3,(f,m,n)=>imp(graph(f,m),imp(graph(f,n),eq(m,n))))(0),
    finite_tuple_fibres_well_order:forall(4,(w,a,r,s)=>imp(omega(w),imp(wo(a,(x,y)=>val(r,x,y)),fibres(s,w,a,r))))(0),
    shortlex_from_ordered_fibres:forall(4,(w,a,r,s)=>imp(wo(w,mem),imp(fibres(s,w,a,r),
      imp(finiteFamily(s,w,a),wo(s,(f,g)=>shortlex(f,g,w,a,r))))))(0),
    finite_shortlex_well_order:forall(4,(w,a,r,s)=>imp(omega(w),imp(wo(a,(x,y)=>val(r,x,y)),
      imp(finiteFamily(s,w,a),wo(s,(f,g)=>shortlex(f,g,w,a,r))))))(0)
  };
  return {proofs,formulas:forms,product_specification:productSpec,product_formulas:product.formulas};
}

function runFiniteSequenceOrder() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildFiniteSequenceOrder(defs),expected=expectedFiniteSequenceOrder(defs);
  if(!same(built.formulas,expected.formulas))throw Error('independent finite sequence formulas');
  if(!same(built.product_specification,expected.product_specification))throw Error('independent prefix product specification');
  if(!same(built.product_formulas,expected.product_formulas))throw Error('independent prefix product formulas');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('finite sequence theorem coverage');
  const checks=[],controls=[],axioms=new Map(),logicOnly=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('finite sequence exact contract mismatch');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent sequence goal: '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('kernel sequence goal: '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation'].includes(n)))throw Error('unexpected sequence axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {
      const logical=kernel(0,[],p.proof,false,'CL');
      if(!same(logical.goal,p.goal))throw Error('pure logic sequence target');
      logicOnly.push(id);
    }
  }
  function omit(id,binders,index,label) {
    const target=structuredClone(expected.proofs[id]);let p=target;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,target));
  }
  for(const [label,index] of [['omega',0],['alphabet_well_order',1],['finite_length',2]])
    omit('finite_length_lex_well_order',4,index,label);
  for(const [label,index] of [['successor',0],['prefix_domain_transitivity',1],['alphabet_well_order',2],['preceding_length_theorem',3]])
    omit('successor_length_lex_well_order',4,index,label);
  for(const [label,index] of [['omega',0],['alphabet_well_order',1],['finite_tuple_family',2]])
    omit('finite_shortlex_well_order',4,index,label);
  for(const [label,index] of [['length_well_order',0],['ordered_fibres',1],['finite_tuple_family',2]])
    omit('shortlex_from_ordered_fibres',4,index,label);
  for(const [label,index] of [['first_graph',0],['second_graph',1]])omit('exact_graph_domain_unique',3,index,label);
  for(const [label,index] of [['successor',0],['tuple_family',1]])omit('prefix_carrier_exists',4,index,label);
  for(const [label,index] of [['omega',0],['empty_base',1],['successor_step',2]])omit('tuple_length_induction',3,index,label);

  const damaged=structuredClone(built.proofs.prefix_graph_exists.proof);let changed=false;
  walk(damaged,n=>{
    if(changed||n[0]!=='axiom'||n[1].name!=='separation')return;
    function alter(p){if(!Array.isArray(p)||changed)return;if(p[0]==='M'||p[0]==='='){p[0]=p[0]==='M'?'=':'M';changed=true;return;}for(const x of p)alter(x);}
    alter(n[1].body);
  });
  if(!changed)throw Error('prefix predicate mutation changed nothing');
  reject('prefix_graph_exists:corrupt_restriction_predicate',()=>kernel(0,[],damaged,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03W',part:'uniform_finite_tuple_and_shortlex_well_order',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,reused_helper_checks:0,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:17,independent_product_specification_checks:1,
    pure_logic_checks:logicOnly,negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.name==='separation'?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    fixed_length_quantifier_order:['w','A','R','m'],
    fixed_length_premises:['Omega(w)','WO(A,Val(R))','m in w'],
    fixed_length_conclusion:'every set S consisting of exact Tuple(f,m,A) graphs is well-ordered by first-difference lexicographic order',
    shortlex_quantifier_order:['w','A','R','S'],
    shortlex_premises:['Omega(w)','WO(A,Val(R))','every f in S is Tuple(f,m,A) for some m in w'],
    shortlex_conclusion:'WO(S,shortlex), with length compared by membership before the fixed-length lexicographic order',
    prefix_carrier_bound:'P(union(S))',finite_length_induction_discharged:true,
    external_length_bound:false,tuple_history_premise:false,pinned_L_unchanged:true,
    scope:'uniform well-ordering of every finite tuple length and every set of finite tuples over a supplied well-ordered alphabet; exact prefix and graph-domain lemmas discharge the decomposition',
    outside_this_replay:['connection between decoded instruction fields and finite alphabet tuples','construction of canonical order histories and internal constructibility','formal checker soundness']
  };
}

export { expectedFiniteSequenceOrder, runFiniteSequenceOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runFiniteSequenceOrder(),null,2));
