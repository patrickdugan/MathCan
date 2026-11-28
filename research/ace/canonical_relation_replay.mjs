// ACE-03U. Exact pair-membership, uniqueness and well-order composition.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildCanonicalRelation, buildCanonicalRelations } from './canonical_relation.mjs';
import { expectedOrderRealizations } from './relation_realization_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

// Uses the preceding independent order-predicate interfaces, then builds
// every new contract directly with de Bruijn indices. No generated proof
// conclusion supplies an expected formula.
function expectedCanonicalRelations(defs) {
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
  const irr=(a,lt)=>A(I(M(0,a+1),N(lt(0,0,1))));
  const trans=(a,lt)=>A(A(A(I(M(2,a+3),I(M(1,a+3),I(M(0,a+3),I(lt(2,1,3),I(lt(1,0,3),lt(2,0,3)))))))));
  const total=(a,lt)=>A(A(I(M(1,a+2),I(M(0,a+2),O(Q(1,0),O(lt(1,0,2),lt(0,1,2)))))));
  const minima=(a,lt)=>A(I(sub(0,a+1),I(E(M(0,1)),E(C(M(0,1),A(I(M(0,2),N(lt(0,1,3)))))))));
  const WO=(a,lt)=>C(C(C(irr(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const R=r=>(x,y,d)=>V(r+d,x,y),all4=p=>A(A(A(A(p))));
  const prior=expectedOrderRealizations(defs),groups={};
  for(const kind of ['induced','successor']) {
    const formula=prior.groups[kind].formula,ps=[3,2,1,0],next=ps.map(x=>x+1),next2=ps.map(x=>x+2);
    const phi=(qs,x,y)=>embed(formula,[x,y,...qs]);
    const pred=qs=>(x,y,d)=>phi(qs.map(q=>q+d),x,y);
    const PairPredicate=(qs,p)=>E(E(C(Pair(p+2,1,0),phi(qs.map(q=>q+2),1,0))));
    const Exact=(qs,r)=>A(B(M(0,r+1),PairPredicate(qs.map(q=>q+1),0)));
    const PairOnly=(b,r)=>A(I(M(0,r+1),E(E(C(C(M(1,b+3),M(0,b+3)),Pair(2,1,0))))));
    const Agreement=(qs,r)=>A(A(B(V(r+2,1,0),phi(qs.map(q=>q+2),1,0))));
    const Unique=(qs,r)=>A(I(Exact(qs.map(q=>q+1),0),Q(0,r+1)));
    const Complete=(qs,r)=>C(C(C(Exact(qs,r),Agreement(qs,r)),WO(qs[1],R(r))),Unique(qs,r));
    const witness=E(Complete(next,0));
    let old=prior.groups[kind].proofs.composed_well_order_realization;
    for(let i=0;i<4;i++)old=old[1];
    const premises=[];
    while(old[0]==='>'){premises.push(old[1]);old=old[2];}
    if(premises.length!==3)throw Error('prior order interface changed');
    groups[kind]={formula,proofs:{
      exact_membership_exists:all4(E(Exact(next,0))),
      exact_membership_unique:all4(A(A(I(Exact(next2,1),I(Exact(next2,0),Q(0,1)))))),
      exact_membership_pair_only:all4(A(I(Exact(next,0),PairOnly(3,0)))),
      exact_membership_implies_agreement:all4(A(I(Exact(next,0),Agreement(next,0)))),
      canonical_unique_relation:all4(E(C(Exact(next,0),Unique(next,0)))),
      canonical_well_order_realization:all4(I(WO(2,pred(ps)),witness)),
      composed_canonical_well_order:all4(premises.reduceRight((p,h)=>I(h,p),witness))
    },false_Val_only_uniqueness:all4(A(A(I(Agreement(next2,1),I(Agreement(next2,0),Q(0,1))))))};
  }
  return groups;
}

// Concrete HF relation fixtures expose the failure of Val-only uniqueness.
// These finite objects are not presented as finite models of ZF.
function junkFixtures() {
  const fixtures=[];
  for(const populated of [false,true]) {
    const sets=[],ids=new Map();
    function set(xs) {
      const members=[...new Set(xs)].sort((a,b)=>a-b),key=JSON.stringify(members);
      if(ids.has(key))return ids.get(key);
      const id=sets.length;sets.push(members);ids.set(key,id);return id;
    }
    const zero=set([]),one=set([zero]);
    const pair=(x,y)=>set([set([x]),set([x,y])]);
    const p=pair(zero,one),good=set(populated?[p]:[]),bad=set([...(populated?[p]:[]),zero]);
    const domain=Array.from({length:sets.length},(_,i)=>i),wanted=new Set(populated?[p]:[]);
    let comparisons=0;
    for(const x of domain)for(const y of domain) {
      const q=pair(x,y),left=sets[good].includes(q),right=sets[bad].includes(q);
      if(left!==right)throw Error('junk altered the induced binary relation');
      const phi=populated&&x===zero&&y===one;
      if(left!==phi)throw Error('fixture relation mismatch');
      comparisons++;
    }
    const exact=r=>domain.every(q=>sets[r].includes(q)===wanted.has(q));
    if(good===bad||!exact(good)||exact(bad)||wanted.has(zero))throw Error('junk membership control failed');
    fixtures.push({name:populated?'nonempty_relation':'empty_relation',coordinate_comparisons:comparisons,
      same_Val:true,distinct_sets:true,clean_exact_membership:true,junk_exact_membership:false,
      offending_member:'empty set, which is not a Kuratowski pair'});
  }
  return fixtures;
}

function runCanonicalRelations() {
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const built=buildCanonicalRelations(defs),expected=expectedCanonicalRelations(defs);
  const checks=[],controls=[],axioms=new Map();
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function checkGoal(p,want){const got=kernel(0,[],p,false,'ZF');if(!same(got.goal,want))throw Error('exact canonical interface mismatch');}
  for(const kind of ['induced','successor']) {
    const source=built[kind],want=expected[kind];
    if(!same(source.formula,want.formula)||!same(Object.keys(source.proofs),Object.keys(want.proofs)))throw Error('canonical coverage or predicate');
    for(const [name,p] of Object.entries(source.proofs)) {
      if(!scoped(p.goal,0,false)||!same(p.goal,want.proofs[name]))throw Error('independent canonical goal '+kind+'.'+name);
      const got=kernel(0,[],p.proof,false,'ZF');
      if(!same(got.goal,want.proofs[name]))throw Error('kernel canonical goal');
      const used=new Set();
      walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
      if([...used].some(x=>!['pairing','power','separation','extensionality'].includes(x)))throw Error('unexpected canonical axiom');
      checks.push({id:kind+'.'+name,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
      let open=p.proof;
      while(open[0]==='uI')open=open[1];
      reject(kind+'.'+name+':drop_binders',()=>kernel(0,[],open,false,'ZF'));
    }
    for(const [name,reason] of [['exact_membership_exists','set_axioms'],['exact_membership_unique','extensionality'],['exact_membership_implies_agreement','pairing']])
      reject(kind+'.'+name+':forbid_'+reason,()=>kernel(0,[],source.proofs[name].proof,false,'CL'));
    reject(kind+':remove_carrier_guard',()=>buildCanonicalRelation(defs,want.formula[2],4,1,null,null));
    reject(kind+':replace_exact_by_Val_only',()=>checkGoal(source.proofs.exact_membership_unique.proof,want.false_Val_only_uniqueness));
    for(let index=0;index<3;index++) {
      const changed=structuredClone(want.proofs.composed_canonical_well_order);
      let p=changed[1][1][1][1];
      for(let i=0;i<index;i++)p=p[2];
      p.splice(0,p.length,...p[2]);
      reject(kind+':omit_order_premise_'+index,()=>checkGoal(source.proofs.composed_canonical_well_order.proof,changed));
    }
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  const fixtures=junkFixtures();
  for(const fixture of fixtures)controls.push('junk:'+fixture.name+':rejected_by_exact_membership');
  return {
    experiment:'ACE-03U',part:'canonical_relation_membership_and_uniqueness',checks,
    checked_modules:checks.length,kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),
    independent_exact_goals:checks.length,independent_order_predicates:2,
    negative_controls:controls.length,controls,junk_fixtures:fixtures,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'unique ambient relation sets defined by exact pair membership, with pair-only shape and composed well-order proofs',
    open_obligations:['syntax-code adequacy for pinned Def','existence of the coherent transfinite history','internal constructibility of the unique relation sets','relativized Choice import','formal checker soundness']
  };
}

export { expectedCanonicalRelations, junkFixtures, runCanonicalRelations };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runCanonicalRelations(),null,2));
