// ACE-03W. Exact independent contracts for partial description evaluation.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildDescriptionEvaluation } from './description_evaluation.mjs';
import { expectedSyntaxTraceAdequacy } from './syntax_trace_adequacy_replay.mjs';
import { expectedSyntaxInstructionCodes } from './syntax_instruction_codes_replay.mjs';
import { expectedDescriptionCarrier } from './description_carrier_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedDescriptionEvaluation(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),eq=(x,y)=>atom('=',x,y);
  const bin=(op,p,q)=>d=>[op,p(d),q(d)],imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const iff=(p,q)=>and(imp(p,q),imp(q,p));
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)],ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const exists=(n,fn,vs=[])=>vs.length===n?fn(vs):ex(x=>exists(n,fn,[...vs,x]));
  const each=(s,fn)=>all(x=>imp(mem(x,s),fn(x))),some=(s,fn)=>ex(x=>and(mem(x,s),fn(x))),free=i=>d=>d+i;
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const apply=(p,...args)=>d=>embed(p,args.map(t=>t(d))),term=(name,...args)=>apply(defs[name],...args);
  const sf=expectedSyntaxTraceAdequacy(defs).formulas,cf=expectedSyntaxInstructionCodes(defs).formulas,df=expectedDescriptionCarrier(defs).formulas;
  const syntax=(ps,m,n)=>apply(sf.syntax,m,n,...ps),trace=(ps,f,m,n,a)=>apply(sf.trace,f,m,n,a,...ps);
  const encodes=(g,m,ps,ts)=>apply(cf.encodes,g,m,...ps,...ts),distinct=ts=>apply(cf.distinct,...ts);
  const bank=(w,ts)=>apply(df.canonical_tag_bank,w,...ts),alphabet=(i,w)=>apply(cf.triple_carrier,i,w);
  const description=(d,n,g,b)=>apply(df.description,d,n,g,b),raw=(c,w,i,a)=>apply(df.raw_carrier,c,w,i,a);
  const nonempty=n=>ex(x=>mem(x,n)),trans=m=>each(m,x=>each(x,y=>mem(y,m)));
  const last=(f,m,n,a,b,x)=>some(m,k=>and(term('successor',k,m),ex(r=>and(term('val',f,k,r),
    some(n,z=>and(term('empty',z),term('slice',x,r,a,n,z,b)))))));
  function positive(d,x,a,w,ts,looseBase=false) {
    return some(w,n=>some(w,m=>and(and(nonempty(n),nonempty(m)),ex(g=>ex(b=>
      and(and(description(d,n,g,b),term('tuple',b,n,a)),exists(5,ps=>ex(f=>
        and(and(and(syntax(ps,m,n),encodes(g,m,ps,ts)),trace(ps,f,m,n,a)),
          looseBase?ex(q=>last(f,m,n,a,q,x)):last(f,m,n,a,b,x))
      )))
    )))));
  }
  const output=(a,x,w,c,ts)=>or(term('empty',x),some(c,d=>positive(d,x,a,w,ts)));
  const outputSet=(a,b,w,c,ts)=>all(x=>iff(mem(x,b),output(a,x,w,c,ts)));
  const emptyCode=d=>ex(z=>and(term('empty',z),description(d,z,z,z)));
  const evaluation=(d,x,a,w,ts)=>or(and(emptyCode(d),term('empty',x)),positive(d,x,a,w,ts));
  const evaluated=(a,x,w,c,ts)=>some(c,d=>evaluation(d,x,a,w,ts));
  const imps=(ps,goal)=>ps.reduceRight((q,p)=>imp(p,q),goal);
  const functional=predicate=>forall(10,(w,a,...vs)=>{
    const ts=vs.slice(0,5),[d,x,y]=vs.slice(5);
    return imps([term('omega',w),distinct(ts),predicate(d,x,a,w,ts),predicate(d,y,a,w,ts)],eq(x,y));
  })(0);
  const proofs={
    omega_set_unique:forall(2,(w,v)=>imps([term('omega',w),term('omega',v)],eq(w,v)))(0),
    last_at_base_is_last_slice:forall(6,(f,m,n,a,b,x)=>imps([term('tuple',b,n,a),last(f,m,n,a,b,x)],term('lastSlice',f,m,n,a,x)))(0),
    last_slice_has_base_tuple:forall(5,(f,m,n,a,x)=>imp(term('lastSlice',f,m,n,a,x),ex(b=>and(term('tuple',b,n,a),last(f,m,n,a,b,x)))))(0),
    common_program_last_at_base_unique:forall(13,(m,n,a,b,f,h,x,y,...ps)=>imps([
      trans(m),syntax(ps,m,n),trace(ps,f,m,n,a),trace(ps,h,m,n,a),last(f,m,n,a,b,x),last(h,m,n,a,b,y)],eq(x,y)))(0),
    positive_evaluation_functional:functional(positive),
    positive_evaluation_is_definable:forall(9,(w,a,...vs)=>{
      const ts=vs.slice(0,5),[d,x]=vs.slice(5);
      return imps([term('omega',w),positive(d,x,a,w,ts)],term('definable',a,x));
    })(0),
    definable_has_positive_description:forall(10,(w,a,i,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),bank(w,ts),alphabet(i,w),raw(c,w,i,a),term('definable',a,x)],output(a,x,w,c,ts));
    })(0),
    positive_description_is_definable:forall(9,(w,a,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),output(a,x,w,c,ts)],term('definable',a,x));
    })(0),
    definable_iff_positive_description:forall(10,(w,a,i,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),bank(w,ts),alphabet(i,w),raw(c,w,i,a)],iff(term('definable',a,x),output(a,x,w,c,ts)));
    })(0),
    empty_description_in_raw_carrier:forall(4,(w,i,a,c)=>imps([term('omega',w),raw(c,w,i,a)],some(c,emptyCode)))(0),
    empty_code_excludes_positive_evaluation:forall(9,(w,a,...vs)=>{
      const ts=vs.slice(0,5),[d,x]=vs.slice(5);
      return imps([emptyCode(d),positive(d,x,a,w,ts)],()=>['F']);
    })(0),
    evaluation_functional:functional(evaluation),
    definable_has_description_evaluation:forall(10,(w,a,i,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),bank(w,ts),alphabet(i,w),raw(c,w,i,a),term('definable',a,x)],evaluated(a,x,w,c,ts));
    })(0),
    description_evaluation_is_definable:forall(9,(w,a,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),evaluated(a,x,w,c,ts)],term('definable',a,x));
    })(0),
    definable_iff_description_evaluation:forall(10,(w,a,i,c,...vs)=>{
      const ts=vs.slice(0,5),x=vs[5];
      return imps([term('omega',w),bank(w,ts),alphabet(i,w),raw(c,w,i,a)],iff(term('definable',a,x),evaluated(a,x,w,c,ts)));
    })(0)
  };
  const ts=Array.from({length:5},(_,i)=>free(i+4));
  return {proofs,formulas:{
    last_at_base:last(free(0),free(1),free(2),free(3),free(4),free(5))(0),
    positive_evaluation:positive(free(0),free(1),free(2),free(3),ts)(0),
    decoded_definable:output(free(0),free(1),free(2),free(3),ts)(0),
    decoded_Def:outputSet(free(0),free(1),free(2),free(3),ts)(0),
    canonical_bank:bank(free(0),Array.from({length:5},(_,i)=>free(i+1)))(0),
    empty_code:emptyCode(free(0))(0),evaluation:evaluation(free(0),free(1),free(2),free(3),ts)(0),
    evaluated_definable:evaluated(free(0),free(1),free(2),free(3),ts)(0)
  },loose_base_functionality:functional((d,x,a,w,ts)=>positive(d,x,a,w,ts,true))};
}

function runDescriptionEvaluation() {
  const defs=definition('v',true),built=buildDescriptionEvaluation(defs),expected=expectedDescriptionEvaluation(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(built.formulas,expected.formulas)||!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('description evaluation interfaces');
  const checks=[],controls=[],axioms=new Map(),pureLogic=[],checkedGoals=new Map();
  let kernelRejects=0,interfaceRejects=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn,kind='kernel'){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);if(kind==='kernel')kernelRejects++;else interfaceRejects++;}
  function exactChecked(id,want){if(!same(checkedGoals.get(id),want))throw Error('wrong exact evaluation target');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent evaluation theorem '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('evaluation kernel goal '+id);
    checkedGoals.set(id,got.goal);
    const used=new Set();
    walk(p.proof,q=>{if(q[0]==='axiom'){used.add(q[1].name);axioms.set(JSON.stringify(q[1]),q[1]);}});
    if([...used].some(a=>!['extensionality','pairing','union','power','foundation','separation'].includes(a)))throw Error('unexpected evaluation axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let bare=p.proof;while(bare[0]==='uI')bare=bare[1];
    if(bare===p.proof)reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    else reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'logic').goal,expected.proofs[id]))throw Error('pure evaluation goal');pureLogic.push(id);}
  }
  function omit(id,binders,index,label) {
    const changed=structuredClone(expected.proofs[id]);let p=changed;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject(label,()=>exactChecked(id,changed),'interface');
  }
  for(const [name,index] of [['omega',0],['canonical_bank',1],['alphabet',2],['raw_carrier',3]])
    omit('definable_iff_description_evaluation',10,index,'coverage_interface:omit_'+name);
  for(const [name,index] of [['omega',0],['distinct_tags',1]])
    omit('evaluation_functional',10,index,'functionality_interface:omit_'+name);
  omit('last_at_base_is_last_slice',6,0,'last_slice_interface:omit_full_base_tuple');
  reject('functionality_interface:replace_encoded_base_with_fresh_witness',()=>
    exactChecked('positive_evaluation_functional',expected.loose_base_functionality),'interface');
  for(const [id,name] of [['positive_evaluation_functional','extensionality'],['definable_has_positive_description','separation'],['empty_description_in_raw_carrier','pairing']]) {
    const damaged=structuredClone(built.proofs[id].proof);let hit=false;
    function damage(p){if(hit||!Array.isArray(p))return;if(p[0]==='axiom'&&p[1].name===name){p.splice(0,p.length,'h',999999);hit=true;return;}for(const q of p)damage(q);}
    damage(damaged);if(!hit)throw Error('missing live evaluation dependency');
    reject(id+':remove_live_'+name,()=>kernel(0,[],damaged,false,'ZF'));
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'partial_description_evaluation_and_exact_definability',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:Object.keys(expected.formulas).length,pure_logic_checks:pureLogic,
    negative_controls:controls.length,kernel_rejection_controls:kernelRejects,exact_interface_rejection_controls:interfaceRejects,controls,
    formula_argument_orders:{last_at_base:['f','m','n','A','b','X'],positive_evaluation:['d','X','A','w','t0','t1','t2','t3','t4'],
      evaluation:['d','X','A','w','t0','t1','t2','t3','t4'],canonical_bank:['w','t0','t1','t2','t3','t4'],empty_code:['d']},
    functionality_quantifier_order:['w','A','t0','t1','t2','t3','t4','d','X','Y'],functionality_premises:['Omega(w)','Distinct(tags)','Evaluation(d,X)','Evaluation(d,Y)'],
    equivalence_quantifier_order:['w','A','I','C','t0','t1','t2','t3','t4','X'],
    equivalence_premises:['Omega(w)','CanonicalBank(w,tags)','TripleCarrier(I,w)','RawCarrier(C,w,I,A)'],
    equivalence:'definable(A,X) iff exists d in C Evaluation(d,X)',
    empty_code:'exists z (Empty(z) and Description(d,z,z,z))',fixed_encoded_base_tuple:true,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'single-valued partial evaluation of raw descriptions, exact coverage of the pinned definable predicate, and a reserved empty-output description',
    outside_this_replay:['total execution for arbitrary supplied syntax','single-natural-number coding','internal constructibility of canonical orders','formal checker soundness']};
}

export { expectedDescriptionEvaluation, runDescriptionEvaluation };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runDescriptionEvaluation(),null,2));
