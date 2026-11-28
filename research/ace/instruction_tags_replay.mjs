import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildInstructionTags } from './instruction_tags.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedInstructionTags(defs) {
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q];
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],N=p=>I(p,['F']);
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){
      const v=i=>i<d?i:indices[i-d]+d;
      return [op,v(a),v(b)];
    }
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const together=xs=>xs.reduce(C);
  function distinct(ts) {
    const clauses=[];
    for(let i=0;i<ts.length;i++)for(let j=i+1;j<ts.length;j++)clauses.push(N(Q(ts[i],ts[j])));
    return together(clauses);
  }
  const chain=ts=>together(ts.slice(0,-1).map((t,i)=>embed(defs.successor,[t,ts[i+1]])));
  const wrap=(op,n,p)=>n===0?p:[op,wrap(op,n-1,p)];
  const ts=[4,3,2,1,0];
  return {proofs:{
    successor_chain_tags_distinct:wrap('A',5,I(chain(ts),distinct(ts))),
    five_distinct_omega_tags:A(I(embed(defs.omega,[0]),
      wrap('E',5,C(together(ts.map(t=>M(t,5))),distinct(ts)))))
  },formulas:{distinct:distinct([0,1,2,3,4]),successor_chain:chain([0,1,2,3,4])}};
}

function runInstructionTags() {
  const defs=definition('v',true),actual=buildInstructionTags(defs),expected=expectedInstructionTags(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas))throw Error('independent tag formulas');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('tag proof coverage');
  const checks=[],controls=[],axioms=new Set();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('wrong exact goal');}
  for(const [name,p] of Object.entries(actual.proofs)) {
    const want=expected.proofs[name];
    if(!scoped(p.goal,0,false)||!same(p.goal,want))throw Error('tag theorem interface '+name);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,want))throw Error('tag kernel conclusion');
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.add(n[1].name);}});
    if([...used].some(a=>!['pairing','foundation'].includes(a)))throw Error('unexpected tag axiom');
    checks.push({id:name,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(name+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    reject(name+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    reject(name+':changed_outer_binder',()=>exact(p.proof,['E',want[1]]));
  }
  const chainTarget=structuredClone(expected.proofs.successor_chain_tags_distinct);
  let chainBody=chainTarget;for(let i=0;i<5;i++)chainBody=chainBody[1];
  chainBody[1]=chainBody[1][1];
  reject('chain:omit_last_successor',()=>exact(actual.proofs.successor_chain_tags_distinct.proof,chainTarget));
  const withoutOmega=structuredClone(expected.proofs.five_distinct_omega_tags);
  withoutOmega[1]=withoutOmega[1][2];
  reject('tags:omit_omega',()=>exact(actual.proofs.five_distinct_omega_tags.proof,withoutOmega));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03V',part:'five_distinct_instruction_tags',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,reused_helper_checks:0,
    independent_exact_goals:checks.length,independent_formula_interfaces:2,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),negative_controls:controls.length,controls,
    ambient_axioms:[...axioms].sort(),pinned_L_unchanged:true,
    scope:'five pairwise distinct tags belonging to each supplied omega set; all tag-existence premises discharged using its successor closure'};
}

export { expectedInstructionTags, runInstructionTags };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runInstructionTags(),null,2));
