// ACE-03U. Independent de Bruijn interfaces for decoded instruction traces.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

// Terms are functions of binder depth. This builder emits de Bruijn trees
// directly; it does not use the proof generator's named syntax or conclusions.
function expectedSyntaxTraceAdequacy(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y),bot=()=>['F'];
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const not=p=>imp(p,bot),iff=(p,q)=>and(imp(p,q),imp(q,p));
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)];
  const ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const every=(s,fn)=>all(x=>imp(mem(x,s),fn(x)));
  const some=(s,fn)=>ex(x=>and(mem(x,s),fn(x)));
  const ands=xs=>xs.reduce(and),ors=xs=>xs.reduce(or);
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const free=i=>d=>d+i;
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const term=(name,...args)=>d=>embed(defs[name],args.map(v=>v(d)));
  const val=(f,k,r)=>term('val',f,k,r),pair=(p,i,j)=>term('pair',p,i,j);
  const graph=(f,m)=>term('graph',f,m);
  const trans=m=>every(m,k=>every(k,i=>mem(i,m)));
  const instr=(tag,fields,k,i,j)=>tag===2?val(fields[tag],k,i):
    ex(p=>and(val(fields[tag],k,p),pair(p,i,j)));
  const bound=(tag,k,n)=>tag<2?[n,n]:tag===3?[k,k]:[k,n];
  function forbidden(tag,fields,k) {
    return tag===2?all(i=>not(instr(tag,fields,k,i))):
      all(i=>all(j=>not(instr(tag,fields,k,i,j))));
  }
  function unique(tag,fields,k,i,j) {
    const self=tag===2?all(u=>imp(instr(tag,fields,k,u),eq(u,i))):
      all(u=>all(v=>imp(instr(tag,fields,k,u,v),and(eq(u,i),eq(v,j)))));
    return ands([self,...[0,1,2,3,4].filter(q=>q!==tag).map(q=>forbidden(q,fields,k))]);
  }
  function arm(tag,fields,k,n) {
    if(tag===2)return some(k,i=>and(instr(tag,fields,k,i),unique(tag,fields,k,i)));
    const [a,b]=bound(tag,k,n);
    return some(a,i=>some(b,j=>and(instr(tag,fields,k,i,j),unique(tag,fields,k,i,j))));
  }
  const choices=(fields,k,n)=>ors([0,1,2,3,4].map(tag=>arm(tag,fields,k,n)));
  function shape(tag,fields,m,n) {
    return every(fields[tag],p=>some(m,k=>ex(data=>and(pair(p,k,data),
      tag===2?mem(data,k):ex(i=>ex(j=>{
        const [a,b]=bound(tag,k,n);
        return and(and(pair(data,i,j),mem(i,a)),mem(j,b));
      }))))));
  }
  const syntax=(fields,m,n)=>and(ands([0,1,2,3,4].map(tag=>shape(tag,fields,m,n))),
    every(m,k=>choices(fields,k,n)));
  function rule(tag,fields,f,k,r,n,a) {
    if(tag===0||tag===1)return all(i=>all(j=>imp(instr(tag,fields,k,i,j),
      term(tag===0?'relEq':'relMem',r,n,a,i,j))));
    if(tag===2)return all(i=>imp(instr(tag,fields,k,i),
      ex(p=>and(val(f,i,p),term('relNeg',r,p,n,a)))));
    if(tag===3)return all(i=>all(j=>imp(instr(tag,fields,k,i,j),
      ex(p=>ex(q=>and(and(val(f,i,p),val(f,j,q)),term('relAnd',r,p,q)))))));
    return all(i=>all(j=>imp(instr(tag,fields,k,i,j),
      ex(p=>and(val(f,i,p),term('relEx',r,p,n,a,j))))));
  }
  const rules=(fields,f,k,r,n,a)=>ands([0,1,2,3,4].map(tag=>rule(tag,fields,f,k,r,n,a)));
  const trace=(fields,f,m,n,a)=>and(graph(f,m),every(m,k=>all(r=>imp(val(f,k,r),rules(fields,f,k,r,n,a)))));
  const agreeAt=(f,g,k)=>all(r=>all(s=>imp(val(f,k,r),imp(val(g,k,s),eq(r,s)))));
  const agree=(f,g,m)=>every(m,k=>agreeAt(f,g,k));
  const proofs={};
  for(const [id,name,arity] of [
    ['eq_relation_unique','relEq',5],['mem_relation_unique','relMem',5],
    ['neg_relation_unique','relNeg',4],['and_relation_unique','relAnd',3],
    ['exists_relation_unique','relEx',5],['slice_unique','slice',6]
  ])proofs[id]=forall(arity+1,(r,s,...args)=>imp(term(name,r,...args),imp(term(name,s,...args),eq(r,s))))(0);
  proofs.instruction_execution_entry=forall(10,(f,k,r,n,a,...fields)=>
    imp(choices(fields,k,n),imp(rules(fields,f,k,r,n,a),term('entry',f,k,r,n,a))))(0);
  proofs.syntax_trace_is_valid_program=forall(9,(f,m,n,a,...fields)=>
    imp(syntax(fields,m,n),imp(trace(fields,f,m,n,a),term('validProgram',f,m,n,a))))(0);
  proofs.trace_value_induction=forall(3,(f,g,m)=>imp(trans(m),
    imp(every(m,k=>imp(every(k,i=>agreeAt(f,g,i)),agreeAt(f,g,k))),agree(f,g,m))))(0);
  const wrap=(conclusion)=>forall(10,(m,n,a,f,g,...fields)=>imp(trans(m),
    imp(syntax(fields,m,n),imp(trace(fields,f,m,n,a),imp(trace(fields,g,m,n,a),conclusion(m,n,a,f,g,fields))))))(0);
  proofs.common_program_trace_values_unique=wrap((m,n,a,f,g)=>agree(f,g,m));
  proofs.exact_graph_extensionality=forall(3,(f,g,m)=>imp(graph(f,m),imp(graph(g,m),
    imp(every(m,k=>all(r=>iff(val(f,k,r),val(g,k,r)))),eq(f,g)))))(0);
  proofs.common_program_trace_graphs_equal=wrap((m,n,a,f,g)=>eq(f,g));
  proofs.common_program_slice_agreement=wrap((m,n,a,f,g)=>every(m,k=>
    forall(6,(r,s,x,y,z,b)=>imp(val(f,k,r),imp(val(g,k,s),
      imp(term('slice',x,r,a,n,z,b),imp(term('slice',y,s,a,n,z,b),eq(x,y))))))));
  const fs=[2,3,4,5,6].map(free),trfs=[4,5,6,7,8].map(free),rfs=[5,6,7,8,9].map(free);
  return {proofs,formulas:{
    syntax:syntax(fs,free(0),free(1))(0),
    trace:trace(trfs,free(0),free(1),free(2),free(3))(0),
    choices:choices(fs,free(0),free(1))(0),
    rules:rules(rfs,free(0),free(1),free(2),free(3),free(4))(0),
    values_agree:agree(free(0),free(1),free(2))(0)
  }};
}

function runSyntaxTraceAdequacy() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildSyntaxTraceAdequacy(defs),expected=expectedSyntaxTraceAdequacy(defs);
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('theorem coverage');
  if(!same(built.formulas,expected.formulas))throw Error('independent syntax/trace interfaces');
  if(!same(built.proofs.exact_graph_extensionality,buildE(defs,true).graph_extensionality))
    throw Error('existing graph helper changed');
  const checks=[],controls=[],axioms=new Map(); let logicOnly=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function checkTarget(proof,goal){const checked=kernel(0,[],proof,false,'ZF');if(!same(checked.goal,goal))throw Error('exact contract mismatch');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent exact goal: '+id);
    const checked=kernel(0,[],p.proof,false,'ZF');
    if(!same(checked.goal,expected.proofs[id]))throw Error('kernel conclusion: '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','foundation','separation'].includes(n)))throw Error('unexpected axiom');
    checks.push({id,nodes:checked.visits,goal_bytes:JSON.stringify(checked.goal).length,
      ambient_axioms:[...used].sort(),reused_existing_helper:id==='exact_graph_extensionality'});
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {const checkedLogic=kernel(0,[],p.proof,false,'CL');if(!same(checkedLogic.goal,p.goal))throw Error('logic goal');logicOnly++;}
  }
  for(const [label,index] of [['transitive_domain',0],['common_syntax',1],['first_trace',2],['second_trace',3]]) {
    const goal=structuredClone(expected.proofs.common_program_trace_values_unique);
    let g=goal;for(let i=0;i<10;i++)g=g[1];for(let i=0;i<index;i++)g=g[2];
    g.splice(0,g.length,...g[2]);
    reject('trace_uniqueness:omit_'+label,()=>checkTarget(built.proofs.common_program_trace_values_unique.proof,goal));
  }
  // Change one live semantic equality atom in one output hypothesis. The
  // unchanged proof must fail when it tries to identify the two extensions.
  for(const id of ['eq_relation_unique','mem_relation_unique','neg_relation_unique','and_relation_unique','exists_relation_unique','slice_unique']) {
    const p=structuredClone(built.proofs[id].proof);let q=p;while(q[0]==='uI')q=q[1];
    const hyp=q[2][1];let changed=false;
    function damage(n){if(!Array.isArray(n)||changed)return;if(n[0]==='='){n[0]='M';changed=true;return;}for(const x of n)damage(x);}
    damage(hyp);
    if(!changed) {
      // Intersection has no equality atoms; change one input-membership atom.
      function alter(n){if(!Array.isArray(n)||changed)return;if(n[0]==='M'){n[0]='=';changed=true;return;}for(const x of n)alter(x);}
      alter(hyp);
    }
    if(!changed)throw Error('mutation did not touch an atom');
    reject(id+':mismatched_semantic_extension',()=>kernel(0,[],p,false,'ZF'));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03U',part:'uniform_decoded_syntax_trace_adequacy',checks,
    checked_modules:checks.length,new_statement_checks:checks.length-1,reused_helper_checks:1,
    kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:5,existing_helper_identity_checks:1,logic_only_checks:logicOnly,
    negative_controls:controls.length,controls,
    ambient_schema_instances:[...axioms.values()].map(s=>({name:s.name,...(s.name==='separation'?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'uniform object-language operation functionality, exact decoded syntax-to-validProgram implication, trace equality and slice agreement over arbitrary transitive instruction domains',
    open_obligations:['existence of semantic traces for every well-formed syntax program',
      'uniform semantic-trace decoration existence','single-natural-number program encoding adequacy',
      'full pinned Def equivalence to the canonical code system','formal checker soundness']
  };
}
export { expectedSyntaxTraceAdequacy, runSyntaxTraceAdequacy };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runSyntaxTraceAdequacy(),null,2));
