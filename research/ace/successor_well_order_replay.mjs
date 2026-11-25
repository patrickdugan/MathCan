// ACE-03T: exact interfaces for retaining an old order as an initial segment.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildSuccessorWellOrder } from './successor_well_order.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedSuccessorWellOrder(defs) {
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
  const T=(a,b,r,s,x,y)=>C(C(M(x,b),M(y,b)),O(
    C(C(M(x,a),M(y,a)),V(r,x,y)),
    O(C(M(x,a),N(M(y,a))),C(C(N(M(x,a)),N(M(y,a))),V(s,x,y)))
  ));
  const R=r=>(x,y,d)=>V(r+d,x,y);
  const sum=(a,b,r,s)=>(x,y,d)=>T(a+d,b+d,r+d,s+d,x,y);
  const all4=p=>A(A(A(A(p))));
  const ab=sub(3,2),wa=WO(3,R(1)),wb=WO(2,R(0)),lt=sum(3,2,1,0);
  const wrap=p=>all4(I(ab,I(wa,I(wb,p))));
  const tx=T(5,4,3,2,1,0),rr=V(3,1,0);
  return {
    proofs:{
      successor_irreflexive:wrap(irr(2,lt)),
      successor_transitive:wrap(trans(2,lt)),
      successor_total:wrap(total(2,lt)),
      successor_minima:wrap(minima(2,lt)),
      successor_well_order:wrap(WO(2,lt)),
      successor_restriction:all4(I(ab,A(A(I(M(1,5),I(M(0,5),C(I(tx,rr),I(rr,tx)))))))),
      successor_initial_segment:all4(A(A(I(M(1,5),I(M(0,4),I(T(5,4,3,2,0,1),M(0,5)))))))
    },
    formulas:{successor_order:T(0,1,2,3,4,5),well_order:WO(0,R(1))}
  };
}

function runSuccessorWellOrder() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildSuccessorWellOrder(defs),expected=expectedSuccessorWellOrder(defs);
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs))||!same(built.formulas,expected.formulas))throw Error('independent successor interfaces');
  const checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  for(const [name,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[name]))throw Error('exact successor theorem: '+name);
    const checked=kernel(0,[],p.proof,false,'ZF');
    if(!same(checked.goal,expected.proofs[name]))throw Error('kernel successor conclusion: '+name);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>x!=='separation'))throw Error('unexpected successor axiom');
    checks.push({id:name,nodes:checked.visits,goal_bytes:JSON.stringify(checked.goal).length,ambient_axioms:[...used].sort()});
    let p0=p.proof;
    while(p0[0]==='uI')p0=p0[1];
    reject(name+':drop_binders',()=>kernel(0,[],p0,false,'ZF'));
  }
  for(const name of ['successor_minima','successor_well_order'])
    reject(name+':forbid_separation',()=>kernel(0,[],built.proofs[name].proof,false,'CL'));
  function checkGoal(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('exact successor contract mismatch');}
  for(const [label,index] of [['inclusion',0],['old_well_order',1],['new_well_order',2]]) {
    const changed=structuredClone(expected.proofs.successor_well_order);
    let q=changed[1][1][1][1];
    for(let i=0;i<index;i++)q=q[2];
    q.splice(0,q.length,...q[2]);
    reject('successor:omit_'+label,()=>checkGoal(built.proofs.successor_well_order.proof,changed));
  }
  for(const [name,depth] of [['successor_restriction',4],['successor_initial_segment',6]]) {
    const changed=structuredClone(expected.proofs[name]);
    let q=changed;
    for(let i=0;i<depth;i++)q=q[1];
    q.splice(0,q.length,...q[2]);
    reject(name+':omit_guard',()=>checkGoal(built.proofs[name].proof,changed));
  }
  return {
    experiment:'ACE-03T',part:'successor_initial_segment_order',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    negative_controls:controls.length,controls,
    ambient_schema_instances:[...axioms.values()].map(s=>({name:s.name,params:s.params,body:s.body})),
    pinned_L_unchanged:true,
    scope:'conditional ZF ordered-sum theorem preserving the old order and initial-segment property; successor relation remains a formula',
    set_realization_verified_by:'relation_realization_replay.mjs',
    open_obligations:['syntax-code adequacy for pinned Def','existence of the coherent transfinite history','internal constructibility of the canonical order','relativized Choice import','formal checker soundness']
  };
}

export { expectedSuccessorWellOrder, runSuccessorWellOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runSuccessorWellOrder(),null,2));
