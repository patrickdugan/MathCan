// ACE-03W. Independent exact raw-description carrier and coverage targets.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildDescriptionCarrier } from './description_carrier.mjs';
import { codeOrderExpectedLanguage } from './pair_product_order_replay.mjs';
import { expectedSyntaxInstructionCodes } from './syntax_instruction_codes_replay.mjs';
import { expectedSyntaxTraceAdequacy } from './syntax_trace_adequacy_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedDescriptionCarrier(defs) {
  const {M,Q,I,C,A,E,some,quant,apply,free,Pair,Omega,iff,product,W,tripleCarrier}=codeOrderExpectedLanguage(defs);
  const instructions=expectedSyntaxInstructionCodes(defs).formulas;
  const sf=expectedSyntaxTraceAdequacy(defs).formulas;
  const Tuple=(g,m,a)=>apply(defs.tuple,g,m,a);
  const Finite=(g,w,a)=>some(w,m=>Tuple(g,m,a));
  const Description=(d,n,g,b)=>E(p=>C(Pair(p,g,b),Pair(d,n,p)));
  const Member=(d,w,i,a)=>some(w,n=>E(g=>C(Finite(g,w,i),E(b=>C(Finite(b,w,a),Description(d,n,g,b))))));
  const Raw=(c,w,i,a)=>A(d=>iff(M(d,c),Member(d,w,i,a)));
  const Seq=(s,w,a)=>A(g=>iff(M(g,s),Finite(g,w,a)));
  const Syntax=(ps,m,n)=>apply(sf.syntax,m,n,...ps);
  const Encodes=(g,m,ps,ts)=>apply(instructions.encodes,g,m,...ps,...ts);
  const Members=(w,ts)=>apply(instructions.tag_members,w,...ts);
  const Bank=(w,ts)=>C(C(apply(instructions.first_five,...ts),Members(w,ts)),apply(instructions.distinct,...ts));
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const Canonical=(g,m,w,ps)=>exs(5,ts=>C(Bank(w,ts),Encodes(g,m,ps,ts)));
  const imps=(ps,q)=>ps.reduceRight((goal,p)=>I(p,goal),q);
  const EncodedMember=(g,d,w,i,a,c,m,n,b,ps,ts)=>C(C(C(Encodes(g,m,ps,ts),Tuple(g,m,i)),Description(d,n,g,b)),M(d,c));
  const CanonicalMember=(g,d,w,i,a,c,m,n,b,ps)=>C(C(C(Canonical(g,m,w,ps),Tuple(g,m,i)),Description(d,n,g,b)),M(d,c));
  const proofs={
    description_packing_exists:quant(3,(n,g,b)=>E(d=>Description(d,n,g,b)))(0),
    nested_products_are_raw_carrier:quant(7,(w,i,a,sg,sb,p,c)=>imps([
      Seq(sg,w,i),Seq(sb,w,a),product(sg,sb,p),product(w,p,c)],Raw(c,w,i,a)))(0),
    raw_carrier_unique:quant(5,(c,d,w,i,a)=>imps([Raw(c,w,i,a),Raw(d,w,i,a)],Q(c,d)))(0),
    ordered_description_from_components:quant(6,(w,i,a,rw,ri,ra)=>imps([
      Omega(w),W(w,rw),W(i,ri),W(a,ra)],E(c=>E(r=>C(Raw(c,w,i,a),W(c,r))))))(0),
    raw_description_well_order_exists:quant(3,(w,a,r)=>imps([Omega(w),W(a,r)],
      E(i=>E(c=>E(t=>C(tripleCarrier(i,w),C(Raw(c,w,i,a),W(c,t))))))))(0),
    sequence_description_member:quant(7,(w,i,a,c,n,g,b)=>imps([
      Raw(c,w,i,a),M(n,w),Finite(g,w,i),Finite(b,w,a)],E(d=>C(M(d,c),Description(d,n,g,b)))))(0),
    syntax_description_with_tags:quant(17,(w,i,a,c,m,n,b,...rest)=>{
      const ps=rest.slice(0,5),ts=rest.slice(5);
      return imps([Omega(w),M(n,w),M(m,w),Members(w,ts),tripleCarrier(i,w),Raw(c,w,i,a),Syntax(ps,m,n),Tuple(b,n,a)],
        E(g=>E(d=>EncodedMember(g,d,w,i,a,c,m,n,b,ps,ts))));
    })(0),
    syntax_description_exists:quant(12,(w,i,a,c,m,n,b,...ps)=>imps([
      Omega(w),M(n,w),M(m,w),tripleCarrier(i,w),Raw(c,w,i,a),Syntax(ps,m,n),Tuple(b,n,a)],
      E(g=>E(d=>CanonicalMember(g,d,w,i,a,c,m,n,b,ps)))))(0)
  };
  const ps=[3,4,5,6,7].map(free),ts=[1,2,3,4,5].map(free);
  return {proofs,formulas:{
    description:Description(free(0),free(1),free(2),free(3))(0),
    finite_sequence:Finite(free(0),free(1),free(2))(0),
    raw_member:Member(free(0),free(1),free(2),free(3))(0),
    raw_carrier:Raw(free(0),free(1),free(2),free(3))(0),
    canonical_encodes:Canonical(free(0),free(1),free(2),ps)(0),
    canonical_tag_bank:Bank(free(0),ts)(0),
    triple_carrier:instructions.triple_carrier,encodes:instructions.encodes,tag_members:instructions.tag_members,
    syntax:sf.syntax
  }};
}

function runDescriptionCarrier() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildDescriptionCarrier(defs),expected=expectedDescriptionCarrier(defs);
  if(!same(built.formulas,expected.formulas))throw Error('independent description formulas');
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('description theorem coverage');
  const checks=[],controls=[],axioms=new Map(),logicOnly=[];
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('description exact contract mismatch');}
  for(const [id,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent description goal: '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[id]))throw Error('kernel description goal: '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>!['extensionality','pairing','union','power','separation','foundation'].includes(n)))throw Error('unexpected description axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    let bare=p.proof,removed=0;while(bare[0]==='uI'){bare=bare[1];removed++;}
    if(removed)reject(id+':drop_binders',()=>kernel(0,[],bare,false,'ZF'));
    else reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('logical description goal');logicOnly.push(id);}
  }
  function omit(id,binders,index,label) {
    const target=structuredClone(expected.proofs[id]);let p=target;
    for(let i=0;i<binders;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];
    p.splice(0,p.length,...p[2]);
    reject(id+':omit_'+label,()=>exact(built.proofs[id].proof,target));
  }
  for(const [label,index] of [['omega',0],['alphabet_well_order',1]])omit('raw_description_well_order_exists',3,index,label);
  for(const [label,index] of [['omega',0],['natural_well_order',1],['instruction_well_order',2],['parameter_well_order',3]])
    omit('ordered_description_from_components',6,index,label);
  for(const [label,index] of [['raw_carrier',0],['width_membership',1],['finite_program',2],['finite_base',3]])
    omit('sequence_description_member',7,index,label);
  for(const [index,label] of ['omega','width_membership','length_membership','tag_membership','triple_carrier','raw_carrier','syntax','specific_base_tuple'].entries())
    omit('syntax_description_with_tags',17,index,label);
  for(const [index,label] of ['omega','width_membership','length_membership','triple_carrier','raw_carrier','syntax','specific_base_tuple'].entries())
    omit('syntax_description_exists',12,index,label);

  // Keep the target scoped while replacing the encoded base tuple by the
  // program graph. Exact comparison must reject this changed coverage claim.
  const wrongBase=structuredClone(expected.proofs.syntax_description_with_tags);
  let endpoint=wrongBase;for(let i=0;i<17;i++)endpoint=endpoint[1];
  for(let i=0;i<8;i++)endpoint=endpoint[2];
  endpoint=endpoint[1][1];
  const described=endpoint[1][2];
  function replaceFree(p,from,to,depth=0) {
    if(!Array.isArray(p))return;
    if(p[0]==='A'||p[0]==='E'){replaceFree(p[1],from,to,depth+1);return;}
    if(p[0]==='M'||p[0]==='='){
      for(let i=1;i<=2;i++)if(p[i]===from+depth)p[i]=to+depth;
      return;
    }
    for(const child of p)replaceFree(child,from,to,depth);
  }
  replaceFree(described,12,1);
  if(same(wrongBase,expected.proofs.syntax_description_with_tags))throw Error('base mutation changed nothing');
  reject('syntax_description_with_tags:replace_specific_base_by_program',()=>exact(built.proofs.syntax_description_with_tags.proof,wrongBase));

  const damaged=structuredClone(built.proofs.description_packing_exists.proof);let changed=false;
  walk(damaged,n=>{if(!changed&&n[0]==='axiom'&&n[1].name==='pairing'){n[1]={name:'union'};changed=true;}});
  if(!changed)throw Error('packing axiom mutation changed nothing');
  reject('description_packing_exists:replace_pairing_with_union',()=>kernel(0,[],damaged,false,'ZF'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03W',part:'actual_raw_description_carrier_and_syntax_coverage',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,reused_helper_checks:0,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:10,pure_logic_checks:logicOnly,negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.name==='separation'?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    raw_carrier:'w x (Seq(w,I) x Seq(w,A))',description_shape:'<n,<g,b>>',
    order_quantifier_order:['w','A','R'],order_premises:['Omega(w)','WO(A,R)'],
    order_conclusion:'exists I,C,T [TripleCarrier(I,w) and (RawCarrier(C,w,I,A) and WO(C,T))]',
    supplied_tag_coverage_quantifier_order:['w','I','A','C','m','n','b','P0','P1','P2','P3','P4','t0','t1','t2','t3','t4'],
    supplied_tag_coverage_premises:['Omega(w)','n in w','m in w','Members(w,tags)','TripleCarrier(I,w)','RawCarrier(C,w,I,A)','Syntax(fields,m,n)','Tuple(b,n,A)'],
    supplied_base_tuple_preserved:true,canonical_tag_bank_exists:true,external_length_bound:false,pinned_L_unchanged:true,
    scope:'actual raw-description carrier and actual well-order, exact carrier uniqueness, arbitrary sequence packaging, and syntax coverage preserving the supplied base tuple',
    outside_this_replay:['evaluation adequacy and functional decoding for the raw carrier','internal constructibility and canonical order history','formal checker soundness']
  };
}

export { expectedDescriptionCarrier, runDescriptionCarrier };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runDescriptionCarrier(),null,2));
