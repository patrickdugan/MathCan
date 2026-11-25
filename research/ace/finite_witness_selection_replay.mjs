// ACE-03U. Finite witness selection with independent exact target formulas.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildFiniteWitnessSelection, buildFiniteSelectionInstances } from './finite_witness_selection.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedFiniteSelection(defs,relation,paramCount) {
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],M=(i,j)=>['M',i,j];
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const Val=(g,i,c)=>embed(defs.val,[g,i,c]),Graph=(g,m)=>embed(defs.graph,[g,m]);
  const Empty=z=>embed(defs.empty,[z]),Omega=w=>embed(defs.omega,[w]),Succ=(n,d)=>embed(defs.successor,[n,d]);
  const inc=(ps,d)=>ps.map(i=>i+d),Cand=(ps,i,c)=>embed(relation,[i,c,...ps]);
  const total=(ps,m)=>A(I(M(0,m+1),E(Cand(inc(ps,2),1,0))));
  const preserves=(ps,g,m)=>A(I(M(0,m+1),A(I(Val(g+2,1,0),Cand(inc(ps,2),1,0)))));
  const selected=(ps,m)=>E(C(Graph(0,m+1),preserves(inc(ps,1),0,m+1)));
  const good=(ps,m)=>I(total(ps,m),selected(ps,m));
  const wrap=(n,p)=>n?A(wrap(n-1,p)):p;
  const ps=Array.from({length:paramCount},(_,i)=>paramCount-1-i),next=inc(ps,1),next2=inc(ps,2);
  return {
    empty_domain_selection:wrap(paramCount,A(I(Empty(0),selected(next,0)))),
    successor_domain_selection:wrap(paramCount,A(A(I(Succ(1,0),I(good(next2,1),good(next2,0)))))),
    omega_finite_selection_induction:wrap(paramCount,A(I(Omega(0),A(I(M(0,1),good(next2,0)))))),
    finite_witness_selection:wrap(paramCount,A(A(I(Omega(1),I(M(0,1),I(total(next2,0),selected(next2,0)))))))
  };
}

function finiteSelectionRelations(defs) {
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  return {
    candidate_graph:{relation:embed(defs.val,[2,0,1]),params:1},
    unbounded_formula:{relation:['A',['>',['M',1,0],['M',2,0]]],params:0}
  };
}

function runFiniteWitnessSelection() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildFiniteSelectionInstances(defs),relations=finiteSelectionRelations(defs);
  const checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('finite theorem interface changed');}
  for(const kind of ['candidate_graph','unbounded_formula']) {
    const source=built[kind],fixture=relations[kind];
    const expected=expectedFiniteSelection(defs,fixture.relation,fixture.params);
    if(!same(source.relation,fixture.relation)||source.paramCount!==fixture.params||!same(Object.keys(source.proofs),Object.keys(expected)))throw Error('finite selection coverage');
    for(const [name,p] of Object.entries(source.proofs)) {
      if(!scoped(p.goal,0,false)||!same(p.goal,expected[name]))throw Error('independent finite target '+kind+'.'+name);
      const got=kernel(0,[],p.proof,false,'ZF');
      if(!same(got.goal,expected[name]))throw Error('kernel finite target');
      const used=new Set();
      walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
      if([...used].some(x=>!['pairing','union','foundation','separation'].includes(x)))throw Error('unexpected finite axiom');
      checks.push({id:kind+'.'+name,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
      let p0=p.proof;
      while(p0[0]==='uI')p0=p0[1];
      reject(kind+'.'+name+':drop_binders',()=>kernel(0,[],p0,false,'ZF'));
    }
    for(const name of ['successor_domain_selection','omega_finite_selection_induction','finite_witness_selection'])
      reject(kind+'.'+name+':forbid_set_axioms',()=>kernel(0,[],source.proofs[name].proof,false,'CL'));
    for(const [label,index] of [['omega',0],['finite_membership',1],['all_rows_inhabited',2]]) {
      const changed=structuredClone(expected.finite_witness_selection);
      let p=changed;
      for(let i=0;i<fixture.params+2;i++)p=p[1];
      for(let i=0;i<index;i++)p=p[2];
      p.splice(0,p.length,...p[2]);
      reject(kind+':omit_'+label,()=>exact(source.proofs.finite_witness_selection.proof,changed));
    }
  }
  for(const [name,relation,params] of [
    ['free_index_out_of_scope',['M',0,2],0],
    ['class_guard_in_pure_candidate',['G',0],0],
    ['noninteger_parameter_count',['=',0,1],0.5],
    ['parameter_count_beyond_schema_limit',['=',0,1],33],
    ['unknown_candidate_connective',['choice',0,1],0]
  ])reject(name,()=>buildFiniteWitnessSelection(defs,relation,params));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03U',part:'finite_witness_selection_without_candidate_functionality',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    candidate_instances:[
      {id:'candidate_graph',formula:'Val(E,i,c)',parameters:1,functionality_required:false},
      {id:'unbounded_formula',formula:'forall z (i in z -> c in z)',parameters:0,functionality_required:false}
    ],
    negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'finite graph selection for each supplied m in omega from row-wise existential witnesses; no functional-candidate or Choice premise',
    open_obligations:['per-instruction syntax-code witnesses for pinned Def','full syntax-code adequacy','coherent transfinite order history','internal constructibility of canonical order sets','relativized Choice import','formal checker soundness']
  };
}

export { expectedFiniteSelection, finiteSelectionRelations, runFiniteWitnessSelection };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runFiniteWitnessSelection(),null,2));
