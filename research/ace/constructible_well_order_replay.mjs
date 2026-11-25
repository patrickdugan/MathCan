// Independent interfaces and executable-kernel replay for ACE-03T.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildWellOrder } from './constructible_well_order.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

// This interface builder uses de Bruijn indices directly. It does not call
// the proof generator's named-formula constructors or read its conclusions.
function expectedWellOrder(defs) {
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q];
  const O=(p,q)=>['|',p,q],Q=(a,b)=>['=',a,b],M=(a,b)=>['M',a,b],N=p=>I(p,['F']);
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const V=(r,x,y)=>embed(defs.val,[r,x,y]);
  const sub=(s,a)=>A(I(M(0,s+1),M(0,a+1)));
  const irr=(a,lt)=>A(I(M(0,a+1),N(lt(0,0,1))));
  const trans=(a,lt)=>A(A(A(I(M(2,a+3),I(M(1,a+3),I(M(0,a+3),I(lt(2,1,3),I(lt(1,0,3),lt(2,0,3)))))))));
  const total=(a,lt)=>A(A(I(M(1,a+2),I(M(0,a+2),O(Q(1,0),O(lt(1,0,2),lt(0,1,2)))))));
  const minima=(a,lt)=>A(I(sub(0,a+1),I(E(M(0,1)),E(C(M(0,1),A(I(M(0,2),N(lt(0,1,3)))))))));
  const WO=(a,lt)=>C(C(C(irr(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const R=r=>(x,y,d)=>V(r+d,x,y);
  const min=(a,r,f,x,c)=>C(C(M(c,a),V(f,c,x)),A(I(M(0,a+1),I(V(f+1,0,x+1),N(V(r+1,0,c+1))))));
  const func=(a,f)=>A(A(A(I(M(2,a+3),I(V(f+3,2,1),I(V(f+3,2,0),Q(1,0)))))));
  const surj=(a,b,f)=>A(I(M(0,b+1),E(C(M(0,a+2),V(f+2,0,1)))));
  const minTotal=(a,b,r,f)=>A(I(M(0,b+1),E(min(a+2,r+2,f+2,1,0))));
  const minimum=(s,r,x)=>C(M(x,s),A(I(M(0,s+1),N(V(r+1,0,x+1)))));
  const out=(a,b,r,f,x,y)=>C(C(M(x,b),M(y,b)),E(E(C(C(min(a+2,r+2,f+2,x+2,1),min(a+2,r+2,f+2,y+2,0)),V(r+2,1,0)))));
  const T=(a,b,r,f)=>(x,y,d)=>out(a+d,b+d,r+d,f+d,x,y);
  const all4=p=>A(A(A(A(p))));
  const wo=WO(3,R(1)),fun=func(3,0),onto=surj(3,2,0),mt=minTotal(3,2,1,0),lt=T(3,2,1,0);
  const sourceChoice=kernel(0,[],['axiom',{name:'choice'}],false,'ZFC').goal;
  // This embeds the exact axiom antecedent and selected-set body from the
  // independent source-schema encoder, so binder/guard drift is detected.
  const choiceAntecedent=a=>embed(sourceChoice[1][1],[a]);
  const choiceSelected=a=>embed(sourceChoice[1][2],[a]);
  return {
    least_code_total:all4(I(wo,I(onto,mt))),
    least_code_unique:A(A(A(I(total(2,R(1)),A(A(A(I(min(5,4,3,2,1),I(min(5,4,3,2,0),Q(0,1)))))))))),
    least_code_injective:A(A(A(I(func(2,0),A(A(A(I(min(5,4,3,2,0),I(min(5,4,3,1,0),Q(2,1)))))))))),
    induced_irreflexive:all4(I(wo,irr(2,lt))),
    induced_transitive:all4(I(wo,trans(2,lt))),
    induced_total:all4(I(wo,I(fun,I(mt,total(2,lt))))),
    induced_minima:all4(I(wo,I(mt,minima(2,lt)))),
    induced_well_order:all4(I(wo,I(fun,I(onto,WO(2,lt))))),
    well_order_minimum_unique:A(A(A(I(total(2,R(1)),I(sub(0,2),A(A(I(minimum(2,3,1),I(minimum(2,3,0),Q(0,1)))))))))),
    choice_from_carrier_well_order:A(A(A(I(WO(1,R(0)),I(A(I(M(0,3),sub(0,2))),I(choiceAntecedent(2),choiceSelected(2)))))))
  };
}

function runWellOrder() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildWellOrder(defs),expected=expectedWellOrder(defs);
  if(!same(Object.keys(built.proofs),Object.keys(expected)))throw Error('theorem coverage');
  const checks=[],axioms=new Map(),controls=[];
  function walk(p,visit){if(!Array.isArray(p))return;visit(p);for(const x of p)if(Array.isArray(x))walk(x,visit);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  for(const [name,p] of Object.entries(built.proofs)) {
    if(!scoped(expected[name],0,false)||!same(p.goal,expected[name]))throw Error('independent interface: '+name);
    const checked=kernel(0,[],p.proof,false,'ZF');
    if(!same(checked.goal,expected[name]))throw Error('kernel conclusion: '+name);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(n=>n!=='separation'))throw Error('unexpected axiom: '+name);
    checks.push({id:name,nodes:checked.visits,goal_bytes:JSON.stringify(checked.goal).length,ambient_axioms:[...used].sort()});
    // Dropping the four/three universal binders exposes unbound terms and
    // cannot make a closed theorem; this checks actual proof scope rejection.
    let openProof=p.proof;
    while(openProof[0]==='uI')openProof=openProof[1];
    reject(name+':drop_binders',()=>kernel(0,[],openProof,false,'ZF'));
  }
  for(const name of ['least_code_total','induced_minima','induced_well_order','choice_from_carrier_well_order'])
    reject(name+':forbid_separation',()=>kernel(0,[],built.proofs[name].proof,false,'CL'));
  // Replace the final functionality application in the injection proof with
  // an unavailable hypothesis. This must be rejected by the
  // unchanged kernel, independently of any expected-goal comparison.
  const damaged=structuredClone(built.proofs.least_code_injective.proof);
  let q=damaged;
  while(q[0]==='uI'||q[0]==='iI')q=q[q[0]==='uI'?1:2];
  q.splice(0,q.length,'h',1000000);
  reject('injection:unavailable_hypothesis',()=>kernel(0,[],damaged,false,'ZF'));
  reject('source_choice_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  const sourceChoice=kernel(0,[],['axiom',{name:'choice'}],false,'ZFC').goal;
  if(!same(built.formulas.choice_antecedent,sourceChoice[1][1])||
     !same(built.formulas.selected_set,sourceChoice[1][2]))throw Error('exact Choice source body mismatch');
  function expectGoal(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('exact theorem interface mismatch');}
  // The implication premises form part of the certified theorem. A caller
  // cannot advertise the same proof under a conclusion that omits one.
  for(const [label,index] of [['carrier',1],['well_order',0],['family',2]]) {
    const altered=structuredClone(expected.choice_from_carrier_well_order);
    let q=altered;
    for(let i=0;i<3;i++)q=q[1];
    for(let i=0;i<index;i++)q=q[2];
    q.splice(0,q.length,...q[2]);
    reject('choice:omit_'+label+'_premise',()=>expectGoal(built.proofs.choice_from_carrier_well_order.proof,altered));
  }
  for(const [label,keep] of [['disjointness',1],['nonemptiness',2]]) {
    const altered=structuredClone(expected.choice_from_carrier_well_order);
    const premise=altered[1][1][1][2][2];
    premise[1]=premise[1][keep];
    reject('choice:omit_'+label,()=>expectGoal(built.proofs.choice_from_carrier_well_order.proof,altered));
  }
  const uniqueSpecs=[...axioms.values()].map(s=>({name:s.name,params:s.params,body_bytes:JSON.stringify(s.body).length}));
  return {
    experiment:'ACE-03T',part:'least_code_and_induced_order',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),
    independent_exact_goals:checks.length,exact_choice_source_comparisons:2,negative_controls:controls.length,controls,
    ambient_schema_instances:uniqueSpecs,pinned_L_unchanged:true,
    scope:'conditional ZF theorems for arbitrary set-coded code order and evaluation; formula-level induced well-order; ambient Choice body from a well-ordered carrier',
    set_realization_verified_by:'relation_realization_replay.mjs',
    open_obligations:['pinned Def syntax-code adequacy','coherent constructible recursion','internal constructibility of the canonical order','relativized Choice import','formal checker soundness']
  };
}

export { expectedWellOrder, runWellOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runWellOrder(),null,2));
