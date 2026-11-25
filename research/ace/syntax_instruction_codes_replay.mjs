// ACE-03W. Independent normalized syntax-code and canonical-tag contracts.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildSyntaxInstructionCodes } from './syntax_instruction_codes.mjs';
import { expectedSyntaxTraceAdequacy } from './syntax_trace_adequacy_replay.mjs';
import { expectedFiniteSelection } from './finite_witness_selection_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedSyntaxInstructionCodes(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y);
  const bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const iff=(p,q)=>and(imp(p,q),imp(q,p)),no=p=>imp(p,()=>['F']);
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)],ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const exists=(n,fn,vs=[])=>vs.length===n?fn(vs):ex(x=>exists(n,fn,[...vs,x]));
  const each=(s,fn)=>all(x=>imp(mem(x,s),fn(x))),some=(s,fn)=>ex(x=>and(mem(x,s),fn(x)));
  const free=i=>d=>d+i,ands=ps=>ps.reduce(and),ors=ps=>ps.reduce(or);
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const apply=(p,...args)=>d=>embed(p,args.map(t=>t(d))),term=(name,...args)=>apply(defs[name],...args);
  const previous=expectedSyntaxTraceAdequacy(defs).formulas;
  const pair=(p,x,y)=>term('pair',p,x,y),val=(g,k,c)=>term('val',g,k,c);
  const triple=(c,t,i,j)=>ex(d=>and(pair(d,i,j),pair(c,t,d)));
  const instr=(op,ps,k,i,j)=>op===2?val(ps[op],k,i):ex(d=>and(val(ps[op],k,d),pair(d,i,j)));
  const syntax=(ps,m,n)=>apply(previous.syntax,m,n,...ps);
  const row=(ps,ts,k,c)=>ors(Array.from({length:5},(_,op)=>op===2?
    ex(i=>and(instr(op,ps,k,i),triple(c,ts[op],i,i))):
    ex(i=>ex(j=>and(instr(op,ps,k,i,j),triple(c,ts[op],i,j))))));
  const encodes=(g,m,ps,ts)=>and(term('graph',g,m),each(m,k=>all(c=>iff(val(g,k,c),row(ps,ts,k,c)))));
  const selected=(g,m,ps,ts)=>and(term('graph',g,m),each(m,k=>all(c=>imp(val(g,k,c),row(ps,ts,k,c)))));
  const carrier=(a,w)=>all(c=>iff(mem(c,a),some(w,t=>some(w,i=>some(w,j=>triple(c,t,i,j))))));
  const members=(w,ts)=>ands(ts.map(t=>mem(t,w)));
  const first=ts=>and(term('empty',ts[0]),ands(ts.slice(0,4).map((t,i)=>term('successor',t,ts[i+1]))));
  const distinct=ts=>ands(ts.flatMap((t,i)=>ts.slice(i+1).map(u=>no(eq(t,u)))));
  const agreement=(ps,qs,m)=>each(m,k=>ands(Array.from({length:5},(_,op)=>op===2?
    all(i=>iff(instr(op,ps,k,i),instr(op,qs,k,i))):
    all(i=>all(j=>iff(instr(op,ps,k,i,j),instr(op,qs,k,i,j)))))));
  const ps=Array.from({length:5},(_,i)=>free(i+2)),ts=Array.from({length:5},(_,i)=>free(i+7));
  const forms={
    triple:triple(free(0),free(1),free(2),free(3))(0),
    triple_carrier:carrier(free(0),free(1))(0),row:row(ps,ts,free(0),free(1))(0),
    encodes:encodes(free(0),free(1),ps,ts)(0),
    first_five:first(Array.from({length:5},(_,i)=>free(i)))(0),
    tag_members:members(free(0),Array.from({length:5},(_,i)=>free(i+1)))(0),
    distinct:distinct(Array.from({length:5},(_,i)=>free(i)))(0)
  };
  const proofs={
    canonical_first_five_exist:all(w=>imp(term('omega',w),exists(5,ts=>and(and(first(ts),members(w,ts)),distinct(ts)))))(0),
    canonical_first_five_unique:forall(10,(...vs)=>{
      const ts=vs.slice(0,5),us=vs.slice(5);
      return imp(first(ts),imp(first(us),ands(ts.map((t,i)=>eq(t,us[i])))));
    })(0),
    normalized_triple_exists:forall(3,(t,i,j)=>ex(c=>triple(c,t,i,j)))(0),
    normalized_triple_unique:forall(5,(c,d,t,i,j)=>imp(triple(c,t,i,j),imp(triple(d,t,i,j),eq(c,d))))(0),
    normalized_triple_injective:forall(7,(c,t,i,j,s,u,v)=>imp(triple(c,t,i,j),imp(triple(c,s,u,v),and(and(eq(t,s),eq(i,u)),eq(j,v)))))(0),
    syntax_row_code_total:forall(12,(m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(syntax(ps,m,n),each(m,k=>ex(c=>row(ps,ts,k,c))));
    })(0),
    syntax_row_code_functional:forall(12,(m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(syntax(ps,m,n),each(m,k=>forall(2,(c,d)=>imp(row(ps,ts,k,c),imp(row(ps,ts,k,d),eq(c,d))))));
    })(0)
  };
  for(const [name,p] of Object.entries(expectedFiniteSelection(defs,forms.row,10)))proofs['syntax_'+name]=p;
  Object.assign(proofs,{
    selected_syntax_rows_are_exact:forall(13,(g,m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(syntax(ps,m,n),imp(selected(g,m,ps,ts),encodes(g,m,ps,ts)));
    })(0),
    finite_syntax_has_normalized_code:forall(13,(w,m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(term('omega',w),imp(mem(m,w),imp(syntax(ps,m,n),ex(g=>encodes(g,m,ps,ts)))));
    })(0),
    normalized_code_is_triple_tuple:forall(15,(w,a,g,m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(term('omega',w),imp(mem(n,w),imp(mem(m,w),imp(members(w,ts),imp(carrier(a,w),
        imp(syntax(ps,m,n),imp(encodes(g,m,ps,ts),term('tuple',g,m,a))))))));
    })(0),
    finite_syntax_code_tuple_exists:forall(14,(w,a,m,n,...vs)=>{
      const ps=vs.slice(0,5),ts=vs.slice(5);
      return imp(term('omega',w),imp(mem(n,w),imp(mem(m,w),imp(members(w,ts),imp(carrier(a,w),
        imp(syntax(ps,m,n),ex(g=>and(encodes(g,m,ps,ts),term('tuple',g,m,a)))))))));
    })(0),
    normalized_graph_instruction_agreement:forall(17,(g,m,...vs)=>{
      const ps=vs.slice(0,5),qs=vs.slice(5,10),ts=vs.slice(10);
      return imp(distinct(ts),imp(encodes(g,m,ps,ts),imp(encodes(g,m,qs,ts),agreement(ps,qs,m))));
    })(0),
    normalized_graph_determines_syntax_fields:forall(18,(g,m,n,...vs)=>{
      const ps=vs.slice(0,5),qs=vs.slice(5,10),ts=vs.slice(10);
      return imp(distinct(ts),imp(syntax(ps,m,n),imp(syntax(qs,m,n),imp(encodes(g,m,ps,ts),
        imp(encodes(g,m,qs,ts),ands(ps.map((p,i)=>eq(p,qs[i]))))))));
    })(0)
  });
  return {proofs,formulas:forms};
}

function runSyntaxInstructionCodes() {
  const defs=definition('v',true),built=buildSyntaxInstructionCodes(defs),expected=expectedSyntaxInstructionCodes(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(built.formulas,expected.formulas)||!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('normalized syntax interfaces');
  const checks=[],controls=[],axioms=new Map(),pureLogic=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('wrong normalized syntax target');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent normalized syntax theorem '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('normalized syntax kernel goal '+id);
    const used=new Set();
    walk(p.proof,q=>{if(q[0]==='axiom'){used.add(q[1].name);axioms.set(JSON.stringify(q[1]),q[1]);}});
    if([...used].some(a=>!['extensionality','pairing','union','foundation','separation'].includes(a)))throw Error('unexpected normalized syntax axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'logic').goal,expected.proofs[id]))throw Error('pure normalized syntax goal');pureLogic.push(id);}
  }
  function omit(id,binders,index,label) {
    const changed=structuredClone(expected.proofs[id]);let p=changed;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);reject(label,()=>exact(built.proofs[id].proof,changed));
  }
  for(const [name,index] of [['omega',0],['finite_width',1],['finite_length',2],['tag_membership',3],['triple_carrier',4],['syntax',5]])
    omit('finite_syntax_code_tuple_exists',14,index,'code_tuple:omit_'+name);
  for(const [name,index] of [['distinct_tags',0],['left_syntax',1],['right_syntax',2],['left_encoding',3],['right_encoding',4]])
    omit('normalized_graph_determines_syntax_fields',18,index,'fields_injection:omit_'+name);
  omit('canonical_first_five_unique',10,0,'canonical_tags:omit_first_bank');
  omit('canonical_first_five_unique',10,1,'canonical_tags:omit_second_bank');
  for(const [id,axiomName] of [['finite_syntax_code_tuple_exists','separation'],['normalized_graph_determines_syntax_fields','extensionality'],['normalized_triple_exists','pairing']]) {
    const damaged=structuredClone(built.proofs[id].proof);let hit=false;
    function damage(p){if(hit||!Array.isArray(p))return;if(p[0]==='axiom'&&p[1].name===axiomName){p.splice(0,p.length,'h',999999);hit=true;return;}for(const q of p)damage(q);}
    damage(damaged);if(!hit)throw Error('missing live normalized syntax dependency');
    reject(id+':remove_live_'+axiomName,()=>kernel(0,[],damaged,false,'ZF'));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'normalized_instruction_codes_and_canonical_tags',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    pure_logic_checks:pureLogic,negative_controls:controls.length,controls,
    formula_argument_orders:{triple:['c','tag','i','j'],triple_carrier:['C','w'],
      row:['k','c','P0','P1','P2','P3','P4','t0','t1','t2','t3','t4'],
      encodes:['g','m','P0','P1','P2','P3','P4','t0','t1','t2','t3','t4'],
      first_five:['t0','t1','t2','t3','t4'],tag_members:['w','t0','t1','t2','t3','t4']},
    encoding:'Kuratowski <tag,<i,j>>; negation uses <tag2,<i,i>>',selector_parameter_count:10,
    main_quantifier_order:['w','C','m','n','P0','P1','P2','P3','P4','t0','t1','t2','t3','t4'],
    main_premises:['Omega(w)','n in w','m in w','all five shared tags in w','TripleCarrier(C,w)','Syntax(P,m,n)'],
    main_conclusion:'exists g (Encodes(g,m,P,tags) and Tuple(g,m,C))',
    field_injectivity_premises:['Distinct(tags)','Syntax(P,m,n)','Syntax(Q,m,n)','Encodes(g,m,P,tags)','Encodes(g,m,Q,tags)'],
    canonical_tags:'FirstFive = Empty(t0) and the left-associated conjunction of Succ(ti,t{i+1}); existence retains membership in w and pairwise distinctness',
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'exact finite normalized syntax graph over shared fixed tags, carrier-bounded tuple coverage, and equality of all five exact syntax fields from a shared code graph',
    open_obligations:['partial evaluation with the encoded full base tuple','single-natural-number coding','execution existence for arbitrary syntax','internal constructibility of canonical orders','formal checker soundness']};
}

export { expectedSyntaxInstructionCodes, runSyntaxInstructionCodes };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runSyntaxInstructionCodes(),null,2));
