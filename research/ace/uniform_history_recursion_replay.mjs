// ACE-03X. Independent interfaces for a pure-formula transfinite recursion schema.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { definition } from './constructible_definition.mjs';
import { buildUniformHistoryRecursion } from './uniform_history_recursion.mjs';
import { buildUniformHistoryExample } from './uniform_history_example.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedUniformHistoryRecursion(defs,step,n=0){
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q];
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],B=(p,q)=>C(I(p,q),I(q,p));
  const up=(ps,k)=>ps.map(x=>x+k);
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const V=(f,i,r)=>embed(defs.val,[f,i,r]),G=(f,d)=>embed(defs.graph,[f,d]);
  const Ord=i=>embed(defs.ordinal,[i]),Succ=(a,b)=>embed(defs.successor,[a,b]);
  const Empty=d=>embed(defs.empty,[d]),Pair=(p,a,b)=>embed(defs.pair,[p,a,b]);
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const Step=(f,i,r,ps)=>embed(step,[f,i,r,...ps]);
  const H=(f,d,ps)=>C(G(f,d),A(I(M(0,d+1),E(C(V(f+2,1,0),Step(f+2,1,0,up(ps,2)))))));
  const Eq=(f,g,d)=>A(I(M(0,d+1),A(B(V(f+2,1,0),V(g+2,1,0)))));
  const Total=ps=>A(A(I(Ord(0),I(H(1,0,up(ps,2)),E(Step(2,1,0,up(ps,3)))))));
  const GT=ps=>A(A(I(G(1,0),E(Step(2,1,0,up(ps,3))))));
  const Fun=ps=>A(A(A(A(I(H(3,2,up(ps,4)),I(Step(3,2,1,up(ps,4)),I(Step(3,2,0,up(ps,4)),Q(1,0))))))));
  const Local=ps=>A(A(A(A(I(Eq(3,2,1),I(Step(3,1,0,up(ps,4)),Step(2,1,0,up(ps,4))))))));
  const Restr=(h,f,e)=>A(B(M(0,h+1),C(M(0,f+1),E(C(M(0,e+2),E(Pair(2,1,0)))))));
  const Good=(h,e,d,ps)=>C(C(Ord(e),sub(e,d)),H(h,e,ps));
  const GF=(h,d,ps)=>A(I(M(0,h+1),E(Good(1,0,d+2,up(ps,2)))));
  const CF=(h,d,ps)=>A(I(M(0,d+1),E(C(M(0,h+2),E(C(Good(1,0,d+3,up(ps,3)),M(2,0)))))));
  const Union=(f,h)=>A(B(M(0,f+1),E(C(M(0,h+2),M(1,0)))));
  const SH=(i,h,ps)=>E(C(Succ(i+1,0),H(h+1,0,up(ps,1))));
  const Witness=(b,r,ps)=>E(C(Succ(b+1,0),E(C(H(0,1,up(ps,2)),V(0,b+2,r+2)))));
  const Agreement=(f,g,d,e)=>A(I(M(0,d+1),I(M(0,e+1),A(I(V(f+2,1,0),A(I(V(g+3,2,0),Q(1,0))))))));
  const ExUnique=(d,ps)=>E(C(H(0,d+1,up(ps,1)),A(I(H(0,d+2,up(ps,2)),Q(0,1)))));
  const all=(k,p)=>k?A(all(k-1,p)):p;
  const ps=Array.from({length:n},(_,i)=>n-1-i),p0=Array.from({length:n},(_,i)=>i);
  const p3=up(ps,3),p4=up(ps,4),p2=up(ps,2),p1=up(ps,1);
  const contracts=(target,{total=false,fun=false,local=false,graph=false}={})=>{
    if(local)target=I(Local(ps),target);
    if(fun)target=I(Fun(ps),target);
    if(total)target=I(Total(ps),target);
    if(graph)target=I(GT(ps),target);
    return all(n,target);
  };
  const allContracts={total:true,fun:true,local:true},determinism={fun:true,local:true};
  const proofs={
    history_restriction_exact:contracts(all(3,I(trans(0),I(sub(0,1),I(H(2,1,p3),E(C(H(0,1,p4),C(Eq(0,3,1),Restr(0,3,1)))))))),{local:true}),
    ordinal_successor:all(n,all(2,I(Ord(1),I(Succ(1,0),Ord(0))))),
    history_coherence:contracts(all(4,I(Ord(1),I(Ord(0),I(H(3,1,p4),I(H(2,0,p4),Agreement(3,2,1,0)))))),determinism),
    history_unique:contracts(all(3,I(Ord(0),I(H(2,0,p3),I(H(1,0,p3),Q(2,1))))),determinism),
    history_extension:contracts(all(3,I(Ord(1),I(Succ(1,0),I(H(2,1,p3),E(H(0,1,p4)))))),{total:true,local:true}),
    empty_history_exists:all(n,A(I(Empty(0),E(H(0,1,p2))))),
    compatible_history_union_exact:contracts(all(2,I(GF(1,0,p2),I(CF(1,0,p2),E(C(H(0,1,p3),Union(0,2)))))),determinism),
    successor_history_unique:contracts(all(3,I(Ord(2),I(SH(2,1,p3),I(SH(2,0,p3),Q(1,0))))),determinism),
    successor_history_exists:contracts(A(I(Ord(0),E(SH(1,0,p2)))),allContracts),
    ordinal_history_exists:contracts(A(I(Ord(0),E(H(0,1,p2)))),allContracts),
    ordinal_history_exists_unique:contracts(A(I(Ord(0),ExUnique(0,p1))),allContracts),
    graph_total_implies_history_total:all(n,I(GT(ps),Total(ps))),
    graph_total_ordinal_history_exists_unique:contracts(A(I(Ord(0),ExUnique(0,p1))),{graph:true,fun:true,local:true}),
    ordinal_value_exists:contracts(A(I(Ord(0),E(Witness(1,0,p2)))),allContracts),
    ordinal_value_unique:contracts(all(3,I(Ord(2),I(Witness(2,1,p3),I(Witness(2,0,p3),Q(1,0))))),determinism)
  };
  return {proofs,formulas:{
    step,history:H(0,1,up(p0,2)),total:Total(p0),graph_total:GT(p0),functional:Fun(p0),local:Local(p0),
    value_agreement:Eq(0,1,2),restriction:Restr(0,1,2),good_family:GF(0,1,up(p0,2)),
    cover_family:CF(0,1,up(p0,2)),union_graph:Union(0,1),successor_history:SH(0,1,up(p0,2)),value_witness:Witness(0,1,up(p0,2))
  }};
}

// r is the value range below i with two seeds adjoined. Free layout [f,i,r,a,b].
function seededRangeStep(defs){
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q];
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b];
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const rhs=O(O(Q(0,4),Q(0,5)),E(C(M(0,3),embed(defs.val,[2,0,1]))));
  return A(C(I(M(0,3),rhs),I(rhs,M(0,3))));
}

function runUniformHistoryRecursion(){
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const step=seededRangeStep(defs),built=buildUniformHistoryRecursion(defs,step,2),expected=expectedUniformHistoryRecursion(defs,step,2);
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs)))throw Error('uniform recursion proof interface');
  if(!same(built.formulas,expected.formulas)){
    for(const name of Object.keys(expected.formulas))if(!same(built.formulas[name],expected.formulas[name]))throw Error('uniform recursion formula interface: '+name);
    throw Error('uniform recursion formula interface');
  }
  const checks=[],controls=[],axioms=new Map(),hash=x=>createHash('sha256').update(JSON.stringify(x)).digest('hex');
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('changed uniform recursion goal');}
  for(const [name,p] of Object.entries(built.proofs)){
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[name]))throw Error('exact uniform recursion theorem: '+name);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,expected.proofs[name]))throw Error('kernel uniform recursion conclusion: '+name);
    const used=new Set();
    walk(p.proof,q=>{if(q[0]==='axiom'){used.add(q[1].name);axioms.set(JSON.stringify(q[1]),q[1]);}});
    const allowed=['extensionality','empty','pairing','union','separation','replacement','foundation'];
    if([...used].some(x=>!allowed.includes(x)))throw Error('unexpected recursion axiom: '+name);
    checks.push({id:name,nodes:got.visits,goal_bytes:JSON.stringify(p.goal).length,ambient_axioms:[...used].sort(),goal_sha256:hash(p.goal)});
    let raw=p.proof;while(raw[0]==='uI')raw=raw[1];
    reject(name+':drop_binders',()=>exact(raw,expected.proofs[name]));
  }
  for(const [contract,index] of [['totality',0],['functionality',1],['prefix_locality',2]]){
    const want=structuredClone(expected.proofs.ordinal_history_exists_unique);let q=want[1][1];
    for(let i=0;i<index;i++)q=q[2];q.splice(0,q.length,...q[2]);
    reject('history_exists_unique:omit_'+contract,()=>exact(built.proofs.ordinal_history_exists_unique.proof,want));
  }
  for(const name of ['history_restriction_exact','history_coherence','ordinal_history_exists_unique'])
    reject(name+':forbid_set_axioms',()=>kernel(0,[],built.proofs[name].proof,false,'CL'));
  reject('step:class_predicate',()=>buildUniformHistoryRecursion(defs,['G',0],0));
  reject('step:unbound_parameter',()=>buildUniformHistoryRecursion(defs,['=',2,3],0));
  reject('step:negative_parameter_count',()=>buildUniformHistoryRecursion(defs,['=',2,2],-1));
  const specs=[...axioms.values()].map(s=>({name:s.name,params:s.params,body_sha256:s.body?hash(s.body):undefined}));
  return {experiment:'ACE-03X',part:'uniform_history_recursion',checks,checked_modules:checks.length,
    kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:Object.keys(expected.formulas).length,negative_controls:controls.length,controls,
    ambient_schema_instances:specs,pinned_L_unchanged:true,step_parameters:2,
    step_free_layout:['history','index','value','seed_a','seed_b'],step_sha256:hash(step),
    scope:'ZF pure-formula transfinite recursion with explicit totality on ordinal histories, functionality on exact prefix histories, and prefix locality; exact restrictions and compatible unions',
    open_obligations:['discharge the contracts for the canonical constructible order step','internal constructibility of the canonical order','relativized Choice import','formal checker soundness']};
}

function runUniformHistoryExample(){
  const defs=definition('v',true),step=seededRangeStep(defs),built=buildUniformHistoryExample(defs);
  const expected=expectedUniformHistoryRecursion(defs,step,2);
  if(!same(built.step,step)||!same(built.formulas,expected.formulas))throw Error('seeded example formula interface');
  function swapParameters(p,d=0){
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,swapParameters(a,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:d+1-(i-d);return [op,v(a),v(b)];}
    return [op,swapParameters(a,d),swapParameters(b,d)];
  }
  const close=p=>['A',['A',swapParameters(p)]];
  const discharge=p=>['A',['A',p[1][1][2][2][2]]];
  const goals={
    seeded_graph_total:close(expected.formulas.graph_total),seeded_history_total:close(expected.formulas.total),
    seeded_functional:close(expected.formulas.functional),seeded_prefix_local:close(expected.formulas.local),
    seeded_ordinal_history_exists_unique:discharge(expected.proofs.ordinal_history_exists_unique),
    seeded_ordinal_value_exists:discharge(expected.proofs.ordinal_value_exists)
  };
  const checks=[],controls=[],axioms=new Set();let logicOnly=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('seeded control accepted: '+name);controls.push(name);}
  for(const [name,p] of Object.entries(built.proofs)){
    if(!scoped(p.goal,0,false)||!same(p.goal,goals[name]))throw Error('seeded exact goal: '+name);
    const got=kernel(0,[],p.proof,false,'ZF');if(!same(got.goal,goals[name]))throw Error('seeded kernel conclusion: '+name);
    const used=new Set();walk(p.proof,q=>{if(q[0]==='axiom'){used.add(q[1].name);axioms.add(q[1].name);}});
    if(!used.size){kernel(0,[],p.proof,false,'CL');logicOnly++;}
    checks.push({id:name,nodes:got.visits,goal_bytes:JSON.stringify(p.goal).length,ambient_axioms:[...used].sort()});
    reject(name+':unbound_hypothesis',()=>kernel(0,[],['iE',p.proof,['h',0]],false,'ZF'));
    const changed=structuredClone(goals[name]);changed[1][1]=['F'];
    reject(name+':changed_conclusion',()=>{const q=kernel(0,[],p.proof,false,'ZF');if(!same(q.goal,changed))throw Error('changed seeded goal');});
  }
  for(const name of ['seeded_graph_total','seeded_functional','seeded_ordinal_history_exists_unique'])
    reject(name+':forbid_set_axioms',()=>kernel(0,[],built.proofs[name].proof,false,'CL'));
  return {experiment:'ACE-03X',part:'seeded_uniform_history_example',checks,checked_modules:checks.length,
    kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:Object.keys(expected.formulas).length,negative_controls:controls.length,controls,
    logic_only_checks:logicOnly,ambient_axioms:[...axioms].sort(),step_parameters:2,
    pinned_L_unchanged:same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))),
    scope:'closed ZF transfinite history existence and uniqueness for the prior-value range with two arbitrary seeds adjoined; every generic recursion contract is proved',
    open_obligations:['canonical constructible order step instantiation','formal checker soundness']};
}

export { expectedUniformHistoryRecursion, seededRangeStep, runUniformHistoryRecursion, runUniformHistoryExample };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(process.argv.includes('--example')?runUniformHistoryExample():runUniformHistoryRecursion(),null,2));
