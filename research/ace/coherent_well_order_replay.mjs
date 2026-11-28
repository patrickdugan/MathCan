// ACE-03T: independently specified directed initial-segment limit transfer.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildCoherentWellOrder } from './coherent_well_order.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedCoherentWellOrder(defs) {
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
  const irr=(a,r)=>A(I(M(0,a+1),N(V(r+1,0,0))));
  const trans=(a,r)=>A(A(A(I(M(2,a+3),I(M(1,a+3),I(M(0,a+3),I(V(r+3,2,1),I(V(r+3,1,0),V(r+3,2,0)))))))));
  const total=(a,r)=>A(A(I(M(1,a+2),I(M(0,a+2),O(Q(1,0),O(V(r+2,1,0),V(r+2,0,1)))))));
  const minima=(a,r)=>A(I(sub(0,a+1),I(E(M(0,1)),E(C(M(0,1),A(I(M(0,2),N(V(r+3,0,1)))))))));
  const WO=(a,r)=>C(C(C(irr(a,r),trans(a,r)),total(a,r)),minima(a,r));
  const capture=(b,h)=>A(A(A(I(M(2,b+3),I(M(1,b+3),I(M(0,b+3),E(C(M(0,h+4),C(C(M(3,0),M(2,0)),M(1,0))))))))));
  const local=(b,h,r)=>A(I(M(0,h+1),C(sub(0,b+1),WO(0,r+1))));
  const initial=(b,h,r)=>A(I(M(0,h+1),A(I(M(0,1),A(I(M(0,b+3),I(V(r+3,0,1),M(0,2))))))));
  const wrap=p=>A(A(A(p))),cap=capture(2,1),loc=local(2,1,0),ini=initial(2,1,0);
  return {
    proofs:{
      directed_irreflexive:wrap(I(cap,I(loc,irr(2,0)))),
      directed_transitive:wrap(I(cap,I(loc,trans(2,0)))),
      directed_total:wrap(I(cap,I(loc,total(2,0)))),
      initial_segment_minima:wrap(I(cap,I(loc,I(ini,minima(2,0))))),
      directed_initial_segment_well_order:wrap(I(cap,I(loc,I(ini,WO(2,0)))))
    },
    formulas:{capture:capture(0,1),local:local(0,1,2),initial:initial(0,1,2),well_order:WO(0,1)}
  };
}

function runCoherentWellOrder() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildCoherentWellOrder(defs),expected=expectedCoherentWellOrder(defs);
  if(!same(Object.keys(built.proofs),Object.keys(expected.proofs))||!same(built.formulas,expected.formulas))throw Error('independent limit interfaces');
  const checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  for(const [name,p] of Object.entries(built.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[name]))throw Error('exact limit theorem: '+name);
    const checked=kernel(0,[],p.proof,false,'ZF');
    if(!same(checked.goal,expected.proofs[name]))throw Error('kernel limit conclusion: '+name);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>x!=='separation'))throw Error('unexpected limit axiom');
    checks.push({id:name,nodes:checked.visits,goal_bytes:JSON.stringify(checked.goal).length,ambient_axioms:[...used].sort()});
    let p0=p.proof;
    while(p0[0]==='uI')p0=p0[1];
    reject(name+':drop_binders',()=>kernel(0,[],p0,false,'ZF'));
  }
  for(const name of ['initial_segment_minima','directed_initial_segment_well_order'])
    reject(name+':forbid_separation',()=>kernel(0,[],built.proofs[name].proof,false,'CL'));
  function checkGoal(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('exact limit contract mismatch');}
  for(const [label,index] of [['triple_capture',0],['local_well_orders',1],['initial_segments',2]]) {
    const changed=structuredClone(expected.proofs.directed_initial_segment_well_order);
    let q=changed[1][1][1];
    for(let i=0;i<index;i++)q=q[2];
    q.splice(0,q.length,...q[2]);
    reject('limit:omit_'+label,()=>checkGoal(built.proofs.directed_initial_segment_well_order.proof,changed));
  }
  return {
    experiment:'ACE-03T',part:'directed_initial_segment_limit',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    negative_controls:controls.length,controls,
    ambient_schema_instances:[...axioms.values()].map(s=>({name:s.name,params:s.params,body:s.body})),
    pinned_L_unchanged:true,
    scope:'conditional ZF well-order transfer from a triple-covering family of initial segments of one set-coded relation',
    open_obligations:['existence of a coherent stage history and union relation','syntax-code adequacy for pinned Def','internal constructibility of the canonical order','relativized Choice import','formal checker soundness']
  };
}

export { expectedCoherentWellOrder, runCoherentWellOrder };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runCoherentWellOrder(),null,2));
