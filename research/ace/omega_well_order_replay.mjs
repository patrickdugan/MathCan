// ACE-03W. Independent targets for supplied-omega induction and well-ordering.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildOmegaInduction, buildOmegaWellOrder } from './omega_well_order.mjs';
import { buildWellOrder } from './constructible_well_order.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function specification(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y);
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const no=p=>imp(p,()=>['F']);
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
  const subset=(s,a)=>each(s,x=>mem(x,a)),transitive=a=>each(a,x=>subset(x,a));
  const nonempty=s=>ex(x=>mem(x,s));
  const irr=(a,lt)=>each(a,x=>no(lt(x,x)));
  const trans=(a,lt)=>forall(3,(x,y,z)=>imp(mem(x,a),imp(mem(y,a),imp(mem(z,a),imp(lt(x,y),imp(lt(y,z),lt(x,z)))))));
  const total=(a,lt)=>forall(2,(x,y)=>imp(mem(x,a),imp(mem(y,a),or(eq(x,y),or(lt(x,y),lt(y,x))))));
  const minima=(a,lt)=>all(s=>imp(subset(s,a),imp(nonempty(s),ex(x=>and(mem(x,s),each(s,y=>no(lt(y,x))))))));
  const wo=(a,lt)=>and(and(and(irr(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const decomposition=(w,n)=>or(term('empty',n),some(w,k=>term('successor',k,n)));
  return {mem,eq,imp,and,or,no,all,ex,forall,each,some,free,apply,term,subset,transitive,nonempty,irr,trans,total,minima,wo,decomposition};
}

function expectedOmegaInduction(defs,property,paramCount) {
  const {mem,imp,all,forall,each,apply,term}=specification(defs);
  return forall(paramCount,(...ps)=>all(w=>{
    const at=n=>apply(property,n,...ps);
    return imp(term('omega',w),imp(all(z=>imp(term('empty',z),at(z))),
      imp(forall(2,(n,d)=>imp(mem(n,w),imp(term('successor',n,d),imp(at(n),at(d))))),each(w,at))));
  }))(0);
}

function expectedOmegaWellOrder(defs) {
  const {mem,eq,imp,all,forall,each,some,free,term,transitive,nonempty,irr,trans,total,minima,wo,decomposition}=specification(defs);
  const withOmega=fn=>all(w=>imp(term('omega',w),fn(w)))(0);
  return {proofs:{
    successor_set_unique:forall(3,(n,d,e)=>imp(term('successor',n,d),imp(term('successor',n,e),eq(d,e))))(0),
    omega_successor_exists:forall(2,(w,n)=>imp(term('omega',w),imp(mem(n,w),some(w,d=>term('successor',n,d)))))(0),
    omega_successor_membership:forall(3,(w,n,d)=>imp(term('omega',w),imp(mem(n,w),imp(term('successor',n,d),mem(d,w)))))(0),
    omega_transitive:withOmega(transitive),
    omega_members_transitive:withOmega(w=>each(w,transitive)),
    omega_member_transitive:forall(2,(w,n)=>imp(term('omega',w),imp(mem(n,w),transitive(n))))(0),
    omega_zero_or_successor:withOmega(w=>each(w,n=>decomposition(w,n))),
    omega_nonempty_predecessor:forall(2,(w,n)=>imp(term('omega',w),imp(mem(n,w),imp(nonempty(n),some(w,k=>term('successor',k,n))))))(0),
    omega_membership_irreflexive:withOmega(w=>irr(w,mem)),
    omega_membership_transitive:withOmega(w=>trans(w,mem)),
    omega_membership_total:withOmega(w=>total(w,mem)),
    omega_membership_minima:withOmega(w=>minima(w,mem)),
    omega_membership_well_order:withOmega(w=>wo(w,mem)),
    omega_ordinal:withOmega(w=>term('ordinal',w))
  },formulas:{
    transitive:transitive(free(0))(0),
    membership_well_order:wo(free(0),mem)(0),
    zero_or_successor:decomposition(free(0),free(1))(0)
  },set_coded_well_order:wo(free(0),(x,y)=>term('val',free(1),x,y))(0)};
}

function runOmegaWellOrder() {
  const defs=definition('v',true),built=buildOmegaWellOrder(defs),expected=expectedOmegaWellOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(built.formulas,expected.formulas)||!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('independent omega interface');
  if(!same(buildWellOrder(defs).formulas.well_order,expected.set_coded_well_order))throw Error('shared WO conjunction mismatch');
  const unbounded=['A',['>',['M',1,0],['M',2,0]]];
  const instances={
    transitivity_induction:{property:expected.formulas.transitive,paramCount:0},
    unbounded_relation_induction:{property:unbounded,paramCount:1}
  };
  const proofSet={...built.proofs},targets={...expected.proofs};
  for(const [id,{property,paramCount}] of Object.entries(instances)) {
    proofSet[id]=buildOmegaInduction(defs,property,paramCount);
    targets[id]=expectedOmegaInduction(defs,property,paramCount);
  }
  const checks=[],controls=[],axioms=new Map(),logicChecks=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('wrong exact omega target');}
  for(const [id,p] of Object.entries(proofSet)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,targets[id]))throw Error('independent omega theorem '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,targets[id]))throw Error('omega kernel goal '+id);
    const used=new Set();
    walk(p.proof,q=>{if(q[0]==='axiom'){used.add(q[1].name);axioms.set(JSON.stringify(q[1]),q[1]);}});
    if([...used].some(a=>!['extensionality','pairing','foundation','separation'].includes(a)))throw Error('unexpected omega axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let stripped=p.proof;while(stripped[0]==='uI')stripped=stripped[1];
    if(stripped===p.proof)reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    else reject(id+':drop_binders',()=>kernel(0,[],stripped,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'logic').goal,targets[id]))throw Error('pure logic omega goal');logicChecks.push(id);}
  }
  function omit(id,binders,index,label) {
    const changed=structuredClone(targets[id]);let p=changed;
    for(let j=0;j<binders;j++)p=p[1];
    for(let j=0;j<index;j++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject(label,()=>exact(proofSet[id].proof,changed));
  }
  omit('omega_membership_well_order',1,0,'well_order:omit_omega');
  omit('omega_member_transitive',2,1,'member_transitivity:omit_natural_membership');
  omit('omega_successor_membership',3,2,'successor:omit_successor_equation');
  omit('transitivity_induction',1,1,'induction:omit_empty_base');
  omit('transitivity_induction',1,2,'induction:omit_successor_step');
  for(const name of ['foundation','separation','extensionality']) {
    const damaged=structuredClone(built.proofs.omega_membership_well_order.proof);let hit=false;
    function damage(p){if(hit||!Array.isArray(p))return;if(p[0]==='axiom'&&p[1].name===name){p.splice(0,p.length,'h',999999);hit=true;return;}for(const q of p)damage(q);}
    damage(damaged);if(!hit)throw Error('missing live omega dependency '+name);
    reject('well_order:remove_live_'+name,()=>kernel(0,[],damaged,false,'ZF'));
  }
  for(const [label,property,count] of [
    ['escaping_parameter',['M',0,1],0],['negative_parameter_count',['=',0,0],-1],
    ['fractional_parameter_count',['=',0,0],0.5],['too_many_parameters',['=',0,0],33]
  ])reject('induction:'+label,()=>buildOmegaInduction(defs,property,count));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'omega_membership_well_order_and_induction',checks,
    checked_modules:checks.length,well_order_family_checks:Object.keys(built.proofs).length,
    fixed_induction_instance_checks:Object.keys(instances).length,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:Object.keys(expected.formulas).length,shared_well_order_layout_checks:1,
    pure_logic_checks:logicChecks,negative_controls:controls.length,controls,
    induction_contract:{property_free_order:['n','...parameters'],quantifier_order:['...parameters','w'],
      premises:['Omega(w)','forall z (Empty(z) -> P(z))','forall n,d (n in w -> Succ(n,d) -> P(n) -> P(d))'],
      conclusion:'forall m (m in w -> P(m))'},
    main_quantifier_order:['w'],main_premises:['Omega(w)'],
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'membership is a strict well-order on a supplied set satisfying the exact pinned Omega definition; natural predecessor, successor, transitivity and fixed-formula induction theorems',
    open_obligations:['set realization of the membership relation when a coded order is required','order and carrier constructions for finite program codes','internal constructibility of orders','formal checker soundness']};
}

export { expectedOmegaInduction, expectedOmegaWellOrder, runOmegaWellOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runOmegaWellOrder(),null,2));
