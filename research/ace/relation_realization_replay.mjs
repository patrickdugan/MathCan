// ACE-03T. Independent set-realization interfaces and unchanged-kernel replay.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildOrderRealizations, buildRealization } from './relation_realization.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function expectedOrderRealizations(defs) {
  const A=p=>['A',p],E=p=>['E',p],I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q];
  const O=(p,q)=>['|',p,q],Q=(a,b)=>['=',a,b],M=(a,b)=>['M',a,b],N=p=>I(p,['F']);
  const B=(p,q)=>C(I(p,q),I(q,p));
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const V=(r,x,y)=>embed(defs.val,[r,x,y]),Pair=(p,x,y)=>embed(defs.pair,[p,x,y]);
  const sub=(s,a)=>A(I(M(0,s+1),M(0,a+1)));
  const Power=(a,p)=>A(B(M(0,p+1),sub(0,a+1)));
  const irr=(a,lt)=>A(I(M(0,a+1),N(lt(0,0,1))));
  const trans=(a,lt)=>A(A(A(I(M(2,a+3),I(M(1,a+3),I(M(0,a+3),I(lt(2,1,3),I(lt(1,0,3),lt(2,0,3)))))))));
  const total=(a,lt)=>A(A(I(M(1,a+2),I(M(0,a+2),O(Q(1,0),O(lt(1,0,2),lt(0,1,2)))))));
  const minima=(a,lt)=>A(I(sub(0,a+1),I(E(M(0,1)),E(C(M(0,1),A(I(M(0,2),N(lt(0,1,3)))))))));
  const WO=(a,lt)=>C(C(C(irr(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const R=r=>(x,y,d)=>V(r+d,x,y);
  const min=(a,r,f,x,c)=>C(C(M(c,a),V(f,c,x)),A(I(M(0,a+1),I(V(f+1,0,x+1),N(V(r+1,0,c+1))))));
  const func=(a,f)=>A(A(A(I(M(2,a+3),I(V(f+3,2,1),I(V(f+3,2,0),Q(1,0)))))));
  const surj=(a,b,f)=>A(I(M(0,b+1),E(C(M(0,a+2),V(f+2,0,1)))));
  const out=(a,b,r,f,x,y)=>C(C(M(x,b),M(y,b)),E(E(C(C(min(a+2,r+2,f+2,x+2,1),min(a+2,r+2,f+2,y+2,0)),V(r+2,1,0)))));
  const succ=(a,b,r,s,x,y)=>C(C(M(x,b),M(y,b)),O(C(C(M(x,a),M(y,a)),V(r,x,y)),O(C(M(x,a),N(M(y,a))),C(C(N(M(x,a)),N(M(y,a))),V(s,x,y)))));
  const all=(n,p)=>n?A(all(n-1,p)):p;
  const common={
    ordered_pair_exists:all(2,E(Pair(0,2,1))),
    ordered_pair_injective:all(5,I(Pair(4,3,2),I(Pair(4,1,0),C(Q(3,1),Q(2,0))))),
    ordered_pair_double_power_bound:all(6,I(Power(5,4),I(Power(4,3),I(M(1,5),I(M(0,5),I(Pair(2,1,0),M(2,3)))))))
  };
  const groups={};
  for(const [kind,phi] of [['induced',out],['successor',succ]]) {
    const ps=[3,2,1,0],next=ps.map(x=>x+1);
    const pred=qs=>(x,y,d)=>phi(...qs.map(q=>q+d),x,y);
    const agreement=(qs,r)=>A(A(B(V(r+2,1,0),phi(...qs.map(q=>q+2),1,0))));
    const witness=E(C(agreement(next,0),WO(3,R(0))));
    const premises=kind==='induced'?[WO(3,R(1)),func(3,0),surj(3,2,0)]:[sub(3,2),WO(3,R(1)),WO(2,R(0))];
    groups[kind]={
      formula:phi(2,3,4,5,0,1),
      proofs:{
        exact_relation_realization:all(4,E(agreement(next,0))),
        well_order_agreement_transfer:all(4,A(I(agreement(next,0),I(WO(3,pred(next)),WO(3,R(0)))))),
        well_order_set_realization:all(4,I(WO(2,pred(ps)),witness)),
        composed_well_order_realization:all(4,premises.reduceRight((p,h)=>I(h,p),witness))
      }
    };
  }
  return {common,groups};
}

function runOrderRealizations() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildOrderRealizations(defs),expected=expectedOrderRealizations(defs);
  const commonNames=Object.keys(expected.common),checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function check(id,p,want,reused=false) {
    if(!scoped(want,0,false)||!same(p.goal,want))throw Error('independent realization goal: '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,want))throw Error('kernel realization goal: '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>!['pairing','power','separation'].includes(x)))throw Error('unexpected realization axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort(),reused_existing_helper:reused});
    let p0=p.proof;
    while(p0[0]==='uI')p0=p0[1];
    reject(id+':drop_binders',()=>kernel(0,[],p0,false,'ZF'));
  }
  // The three shared helper trees are identical across the two builds.
  // Count and kernel-check them once; two were already proved in ACE-03F.
  for(const name of commonNames) {
    if(!same(built.induced.proofs[name],built.successor.proofs[name]))throw Error('shared pair helper mismatch');
    check(name,built.induced.proofs[name],expected.common[name],name!=='ordered_pair_double_power_bound');
  }
  for(const kind of ['induced','successor']) {
    const source=built[kind],want=expected.groups[kind];
    if(!same(source.formula,want.formula))throw Error('independent '+kind+' predicate mismatch');
    if(!same(Object.keys(source.proofs),[...commonNames,...Object.keys(want.proofs)]))throw Error('realization theorem coverage');
    for(const [name,goal] of Object.entries(want.proofs))check(kind+'.'+name,source.proofs[name],goal);
    for(const name of ['exact_relation_realization','well_order_set_realization','composed_well_order_realization'])
      reject(kind+'.'+name+':forbid_set_axioms',()=>kernel(0,[],source.proofs[name].proof,false,'CL'));
    reject(kind+':remove_explicit_carrier_guards',()=>buildRealization(defs,want.formula[2],4,1));
    for(let index=0;index<3;index++) {
      const changed=structuredClone(want.proofs.composed_well_order_realization);
      let p=changed[1][1][1][1];
      for(let i=0;i<index;i++)p=p[2];
      p.splice(0,p.length,...p[2]);
      reject(kind+':omit_source_premise_'+index,()=>{
        const got=kernel(0,[],source.proofs.composed_well_order_realization.proof,false,'ZF');
        if(!same(got.goal,changed))throw Error('source premise omitted');
      });
    }
  }
  reject('pair_exists:forbid_pairing',()=>kernel(0,[],built.induced.proofs.ordered_pair_exists.proof,false,'CL'));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {
    experiment:'ACE-03T',part:'ambient_order_relation_set_realization',checks,
    checked_modules:checks.length,new_statement_checks:checks.filter(x=>!x.reused_existing_helper).length,
    reused_helper_checks:checks.filter(x=>x.reused_existing_helper).length,
    kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    independent_order_predicates:2,shared_helper_identity_checks:commonNames.length,
    negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'actual ambient set relations for both exact order predicates, with pointwise equivalence and composed well-order proofs under the original premises',
    open_obligations:['syntax-code adequacy for pinned Def','existence of the coherent transfinite history','internal constructibility of the realized order sets','relativized Choice import','formal checker soundness']
  };
}

export { expectedOrderRealizations, runOrderRealizations };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runOrderRealizations(),null,2));
