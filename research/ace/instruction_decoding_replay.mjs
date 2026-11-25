// ACE-03V. Independent exact contracts for tagged-program field decoding.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildInstructionDecoding } from './instruction_decoding.mjs';
import { expectedInstructionWitnesses } from './instruction_witnesses_replay.mjs';
import { expectedInstructionTags } from './instruction_tags_replay.mjs';
import { expectedSyntaxTraceAdequacy } from './syntax_trace_adequacy_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

// Direct de Bruijn construction. Terms depend on the ambient binder depth;
// no named formula or proof conclusion from the generator is reused here.
function expectedInstructionDecoding(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y),bot=()=>['F'];
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q);
  const iff=(p,q)=>and(imp(p,q),imp(q,p));
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)];
  const ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const every=(s,fn)=>all(x=>imp(mem(x,s),fn(x)));
  const some=(s,fn)=>ex(x=>and(mem(x,s),fn(x)));
  const ands=xs=>xs.reduce(and);
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const exists=(n,fn,vs=[])=>vs.length===n?fn(vs):ex(x=>exists(n,fn,[...vs,x]));
  const free=i=>d=>d+i;
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const apply=(formula,...args)=>d=>embed(formula,args.map(v=>v(d)));
  const term=(name,...args)=>apply(defs[name],...args);
  const val=(g,k,c)=>term('val',g,k,c),pair=(p,x,y)=>term('pair',p,x,y);
  const graph=(g,m)=>term('graph',g,m);
  const union=(b,u)=>all(x=>iff(mem(x,u),ex(y=>and(mem(y,b),mem(x,y)))));
  const wf=expectedInstructionWitnesses(defs).formulas;
  const tf=expectedInstructionTags(defs).formulas;
  const sf=expectedSyntaxTraceAdequacy(defs).formulas;
  const tagged=(g,f,m,n,a,tags)=>apply(wf.tagged_program,g,f,m,n,a,...tags);
  const distinct=tags=>apply(tf.distinct,...tags);
  const syntax=(fields,m,n)=>apply(sf.syntax,m,n,...fields);
  const trace=(fields,f,m,n,a)=>apply(sf.trace,f,m,n,a,...fields);
  const choices=(fields,k,n)=>apply(sf.choices,k,n,...fields);
  const rules=(fields,f,k,r,n,a)=>apply(sf.rules,f,k,r,n,a,...fields);
  const decoded=(g,t,k,d)=>ex(c=>and(val(g,k,c),pair(c,t,d)));
  const member=(g,t,p)=>ex(k=>ex(d=>and(pair(p,k,d),decoded(g,t,k,d))));
  const exact=(h,g,t)=>all(p=>iff(mem(p,h),member(g,t,p)));
  const agreement=(h,g,t)=>all(k=>all(d=>iff(val(h,k,d),decoded(g,t,k,d))));
  const exacts=(fields,g,tags)=>ands(fields.map((h,op)=>exact(h,g,tags[op])));
  const agreements=(fields,g,tags)=>ands(fields.map((h,op)=>agreement(h,g,tags[op])));
  function semantic(op,f,r,n,a,i,j) {
    if(op<2)return term(op===0?'relEq':'relMem',r,n,a,i,j);
    if(op===2)return ex(p=>and(val(f,i,p),term('relNeg',r,p,n,a)));
    if(op===3)return ex(p=>ex(q=>and(and(val(f,i,p),val(f,j,q)),term('relAnd',r,p,q))));
    return ex(p=>and(val(f,i,p),term('relEx',r,p,n,a,j)));
  }
  const payload=(op,f,k,d,n,a)=>{
    const sem=(i,j)=>ex(r=>and(val(f,k,r),semantic(op,f,r,n,a,i,j)));
    if(op===2)return and(mem(d,k),sem(d));
    return some(op<2?n:k,i=>some(op===3?k:n,j=>and(pair(d,i,j),sem(i,j))));
  };
  const shapes=(fields,m,n)=>d=>syntax(fields,m,n)(d)[1];
  const everyChoice=(fields,m,n)=>every(m,k=>choices(fields,k,n));
  const everyRule=(fields,f,m,n,a)=>every(m,k=>all(r=>imp(val(f,k,r),rules(fields,f,k,r,n,a))));
  const proofs={
    pair_coordinates_double_union:forall(6,(b,u,v,p,x,y)=>imp(union(b,u),imp(union(u,v),
      imp(mem(p,b),imp(pair(p,x,y),and(mem(x,v),mem(y,v)))))))(0),
    decoded_field_exists:forall(2,(g,t)=>ex(h=>exact(h,g,t)))(0),
    exact_field_value_agreement:forall(3,(h,g,t)=>imp(exact(h,g,t),agreement(h,g,t)))(0),
    graph_values_unique:forall(5,(g,m,k,c,d)=>imp(graph(g,m),imp(mem(k,m),imp(val(g,k,c),imp(val(g,k,d),eq(c,d))))))(0),
    graph_value_in_domain:forall(4,(g,m,k,c)=>imp(graph(g,m),imp(val(g,k,c),mem(k,m))))(0)
  };
  const ops=['eq','mem','neg','and','exists'];
  for(let op=0;op<5;op++)proofs[ops[op]+'_decoded_payload']=forall(12,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),[k,d]=rest.slice(5);
    return imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),imp(mem(k,m),
      imp(decoded(g,tags[op],k,d),payload(op,f,k,d,n,a)))));
  })(0);
  proofs.decoded_fields_have_shape=forall(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),imp(exacts(fields,g,tags),shapes(fields,m,n))));
  })(0);
  proofs.decoded_fields_have_choices=forall(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),imp(agreements(fields,g,tags),everyChoice(fields,m,n))));
  })(0);
  proofs.decoded_fields_follow_rules=forall(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return imp(graph(f,m),imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),
      imp(agreements(fields,g,tags),everyRule(fields,f,m,n,a)))));
  })(0);
  proofs.decoded_fields_syntax_and_trace=forall(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return imp(graph(f,m),imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),
      imp(exacts(fields,g,tags),and(syntax(fields,m,n),trace(fields,f,m,n,a))))));
  })(0);
  proofs.tagged_program_has_decoded_syntax=forall(10,(g,f,m,n,a,...tags)=>
    imp(graph(f,m),imp(distinct(tags),imp(tagged(g,f,m,n,a,tags),
      exists(5,fields=>and(syntax(fields,m,n),trace(fields,f,m,n,a)))))))(0);
  const tags=[1,2,3,4,5].map(free),fields=[6,7,8,9,10].map(free);
  return {proofs,formulas:{
    decoded:decoded(free(0),free(1),free(2),free(3))(0),
    exact_field:exact(free(0),free(1),free(2))(0),
    field_agreement:agreement(free(0),free(1),free(2))(0),
    exact_fields:exacts(fields,free(0),tags)(0),
    field_agreements:agreements(fields,free(0),tags)(0),
    payloads:ops.map((_,op)=>payload(op,free(0),free(1),free(2),free(3),free(4))(0)),
    distinct:tf.distinct,syntax:sf.syntax,trace:sf.trace,tagged_program:wf.tagged_program
  }};
}

function runInstructionDecoding() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildInstructionDecoding(defs),expected=expectedInstructionDecoding(defs);
  if(!same(built.formulas,expected.formulas))throw Error('independent decoding interfaces');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('decoding theorem coverage');
  const previousDomain=buildF(defs,'relations').value_in_domain;
  if(!same(built.proofs.graph_value_in_domain.goal,previousDomain.goal))throw Error('existing domain statement identity');
  if(same(built.proofs.graph_value_in_domain.proof,previousDomain.proof))throw Error('domain helper must be independently reproved');
  const checks=[],controls=[],axioms=new Map(),logicOnly=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('decoding exact contract mismatch');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent decoding goal: '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('kernel decoding goal: '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['pairing','union','power','separation'].includes(n)))throw Error('unexpected decoding axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort(),
      ...(id==='graph_value_in_domain'?{independently_reproved_existing_statement:'finite_witnesses.value_in_domain'}:{})});
    let bare=p.proof,removed=0;
    while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed===0)throw Error('binder control would make no mutation');
    reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {
      const gotLogic=kernel(0,[],p.proof,false,'CL');
      if(!same(gotLogic.goal,p.goal))throw Error('logical decoding goal');
      logicOnly.push(id);
    }
  }
  function withoutPremise(id,binderCount,index,label) {
    const changed=structuredClone(expected.proofs[id]);
    let g=changed;for(let i=0;i<binderCount;i++)g=g[1];for(let i=0;i<index;i++)g=g[2];
    g.splice(0,g.length,...g[2]);
    reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,changed));
  }
  for(const [label,index] of [['semantic_graph',0],['distinct_tags',1],['tagged_selection',2]])
    withoutPremise('tagged_program_has_decoded_syntax',10,index,label);
  withoutPremise('decoded_fields_have_shape',15,2,'exact_raw_field_membership');
  withoutPremise('decoded_fields_have_choices',15,1,'tagged_selection');
  withoutPremise('decoded_fields_follow_rules',15,0,'semantic_graph');
  for(const id of ['eq','mem','neg','and','exists'])withoutPremise(id+'_decoded_payload',12,0,'distinct_tags');

  // Change the actual Separation predicate while preserving a well-scoped
  // schema. The proof must fail when it attempts to recover exact membership.
  const damaged=structuredClone(built.proofs.decoded_field_exists.proof);
  let changed=false;
  walk(damaged,n=>{
    if(changed||n[0]!=='axiom'||n[1].name!=='separation')return;
    function alter(p){
      if(!Array.isArray(p)||changed)return;
      if(p[0]==='M'||p[0]==='='){p[0]=p[0]==='M'?'=':'M';changed=true;return;}
      for(const child of p)alter(child);
    }
    alter(n[1].body);
  });
  if(!changed)throw Error('field-predicate mutation changed nothing');
  reject('decoded_field_exists:corrupt_exact_separation_predicate',()=>kernel(0,[],damaged,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03V',part:'exact_tagged_program_decoding',checks,
    checked_modules:checks.length,new_statement_checks:checks.length-1,
    reproved_existing_statement_checks:1,reused_helper_checks:0,existing_statement_identity_checks:1,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:14,pure_logic_checks:logicOnly,
    negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.name==='separation'?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    main_quantifier_order:['g','f','m','n','A','tag0','tag1','tag2','tag3','tag4'],
    main_premises:['Graph(f,m)','Distinct(tag0,...,tag4)','Tagged(g,f,m,n,A,tags)'],
    field_order:['eq','mem','neg','and','exists'],
    field_membership:'p in Field(tag) iff exists k,d,c (Pair(p,k,d) and Val(g,k,c) and Pair(c,tag,d))',
    field_bound:'P(P(U^2(g) union U^4(g)))',
    transitive_domain_required:false,finite_domain_required:false,pinned_L_unchanged:true,
    scope:'a supplied exact tagged selection graph and a semantic graph yield five actual exact syntax fields with the original Syntax and Trace formulas; no Choice axiom is used',
    open_obligations:['single-natural-number program coding','execution existence for every well-formed program','canonical order history and internal constructibility','formal checker soundness']
  };
}

export { expectedInstructionDecoding, runInstructionDecoding };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runInstructionDecoding(),null,2));
