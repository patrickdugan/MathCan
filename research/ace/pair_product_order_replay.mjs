// ACE-03W. Independent exact targets for Cartesian product order construction.
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildPairProductOrder} from './pair_product_order.mjs';
import {expectedLexicographicPullback} from './lexicographic_pullback_replay.mjs';
import {buildWellOrder} from './constructible_well_order.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function codeOrderExpectedLanguage(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)],M=(x,y)=>atom('M',x,y),Q=(x,y)=>atom('=',x,y);
  const bin=(op,p,q)=>d=>[op,p(d),q(d)],I=(p,q)=>bin('>',p,q),C=(p,q)=>bin('&',p,q),O=(p,q)=>bin('|',p,q);
  const N=p=>I(p,()=>['F']),A=fn=>d=>['A',fn(e=>e-d-1)(d+1)],E=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const every=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const quant=(n,fn,vs=[])=>vs.length===n?fn(...vs):A(x=>quant(n,fn,[...vs,x]));
  function embed(p,ix,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,ix,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:ix[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,ix,d),embed(b,ix,d)];
  }
  const apply=(p,...vs)=>d=>embed(p,vs.map(v=>v(d))),free=i=>d=>i+d;
  const Pair=(p,x,y)=>apply(defs.pair,p,x,y),Val=(r,x,y)=>apply(defs.val,r,x,y),Omega=w=>apply(defs.omega,w);
  const iff=(p,q)=>C(I(p,q),I(q,p)),subset=(s,a)=>every(s,x=>M(x,a));
  const product=(a,b,c)=>A(p=>iff(M(p,c),some(a,x=>some(b,y=>Pair(p,x,y)))));
  const triple=(c,t,i,j)=>E(d=>C(Pair(d,i,j),Pair(c,t,d)));
  const tripleCarrier=(c,w)=>A(p=>iff(M(p,c),some(w,t=>some(w,i=>some(w,j=>triple(p,t,i,j))))));
  const irref=(s,lt)=>every(s,x=>N(lt(x,x)));
  const trans=(s,lt)=>quant(3,(x,y,z)=>I(M(x,s),I(M(y,s),I(M(z,s),I(lt(x,y),I(lt(y,z),lt(x,z)))))));
  const total=(s,lt)=>quant(2,(x,y)=>I(M(x,s),I(M(y,s),O(Q(x,y),O(lt(x,y),lt(y,x))))));
  const minima=(s,lt)=>A(t=>I(subset(t,s),I(E(x=>M(x,t)),E(x=>C(M(x,t),every(t,y=>N(lt(y,x))))))));
  const wo=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const W=(s,r)=>wo(s,(x,y)=>Val(r,x,y));
  const pairPredicate=(ps,phi,p)=>E(x=>E(y=>C(Pair(p,x,y),phi(ps,x,y))));
  const exact=(ps,phi,r)=>A(p=>iff(M(p,r),pairPredicate(ps,phi,p)));
  const agreement=(ps,phi,r)=>A(x=>A(y=>iff(Val(r,x,y),phi(ps,x,y))));
  const unique=(ps,phi,r)=>A(s=>I(exact(ps,phi,s),Q(s,r)));
  const complete=(ps,b,phi,r)=>C(C(C(exact(ps,phi,r),agreement(ps,phi,r)),W(b,r)),unique(ps,phi,r));
  return {M,Q,I,C,O,N,A,E,every,some,quant,embed,apply,free,Pair,Val,Omega,iff,subset,product,triple,tripleCarrier,wo,W,exact,agreement,unique,complete};
}

function expectedPairProductOrder(defs) {
  const L=codeOrderExpectedLanguage(defs),{M,Q,I,C,A,E,every,some,quant,embed,apply,free,Pair,product,wo,W,complete}=L;
  const spec={paramCount:5,firstCarrier:0,secondCarrier:1,outputCarrier:2,
    firstOrder:embed(defs.val,[5,0,1]),secondOrder:embed(defs.val,[6,0,1]),representation:defs.pair};
  const lex=expectedLexicographicPullback(defs,spec).formulas.lexicographic;
  const phi=(ps,x,y)=>apply(lex,x,y,...ps);
  const cover=(a,b,c)=>every(c,p=>some(a,x=>some(b,y=>Pair(p,x,y))));
  const functional=c=>quant(5,(p,a,b,d,e)=>I(M(p,c),I(Pair(p,a,b),I(Pair(p,d,e),C(Q(a,d),Q(b,e))))));
  const injection=c=>quant(4,(p,q,a,b)=>I(M(p,c),I(M(q,c),I(Pair(p,a,b),I(Pair(q,a,b),Q(p,q))))));
  return {spec,formulas:{product:product(free(0),free(1),free(2))(0),cover:cover(free(0),free(1),free(2))(0),
    coordinate_functionality:functional(free(0))(0),joint_injection:injection(free(0))(0),
    lexicographic:lex,well_order:W(free(0),free(1))(0)},proofs:{
    pair_product_exists:quant(2,(a,b)=>E(c=>product(a,b,c)))(0),
    pair_product_unique:quant(4,(a,b,c,d)=>I(product(a,b,c),I(product(a,b,d),Q(c,d))))(0),
    pair_product_covers:quant(3,(a,b,c)=>I(product(a,b,c),cover(a,b,c)))(0),
    pair_product_coordinate_functionality:A(c=>functional(c))(0),
    pair_product_joint_injection:A(c=>injection(c))(0),
    pair_product_lexicographic_well_order:quant(5,(...ps)=>I(W(ps[0],ps[3]),I(W(ps[1],ps[4]),I(product(...ps.slice(0,3)),
      wo(ps[2],(x,y)=>phi(ps,x,y))))))(0),
    pair_product_canonical_well_order:quant(5,(...ps)=>I(W(ps[0],ps[3]),I(W(ps[1],ps[4]),I(product(...ps.slice(0,3)),
      E(r=>complete(ps,ps[2],phi,r))))))(0),
    ordered_product_exists:quant(4,(a,b,r,s)=>I(W(a,r),I(W(b,s),E(c=>E(t=>C(product(a,b,c),W(c,t)))))))(0)
  }};
}

function runPairProductOrder() {
  const defs=definition('v',true),actual=buildPairProductOrder(defs),expected=expectedPairProductOrder(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(actual.formulas,expected.formulas)||!same(actual.spec,expected.spec))throw Error('product formula interface');
  if(!same(actual.formulas.well_order,buildWellOrder(defs).formulas.well_order))throw Error('well-order layout');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('proof coverage');
  const checks=[],controls=[],schemas=new Map();let logic=0;
  const reject=(id,fn)=>{if(!rejects(fn))throw Error('negative control accepted '+id);controls.push(id);};
  const exact=(proof,want)=>{if(!same(kernel(0,[],proof,false,'ZF').goal,want))throw Error('goal mismatch');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent product target '+id);
    const got=kernel(0,[],p.proof,false,'ZF');if(!same(got.goal,p.goal))throw Error('kernel goal '+id);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);schemas.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(x=>!['pairing','union','power','separation','extensionality'].includes(x)))throw Error('product axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(p.proof,['E',p.goal[1]]));
    reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,p.goal))throw Error('pure logic');logic++;}
  }
  for(const [id,binders,count] of [['pair_product_lexicographic_well_order',5,3],['ordered_product_exists',4,2]]) {
    for(let k=0;k<count;k++) {
      const changed=structuredClone(expected.proofs[id]);let n=changed;
      for(let i=0;i<binders;i++)n=n[1];for(let i=0;i<k;i++)n=n[2];n.splice(0,n.length,...n[2]);
      reject(id+':omitted_premise_'+k,()=>exact(actual.proofs[id].proof,changed));
    }
  }
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'exact_pair_product_and_canonical_order',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:Object.keys(expected.formulas).length,
    shared_well_order_layout_checks:1,logic_only_checks:logic,negative_controls:controls.length,controls,
    ambient_axiom_instances:[...schemas.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,scope:'exact Cartesian-product sets, canonical lexicographic relation sets, and well-order existence from supplied component orders'};
}
export {codeOrderExpectedLanguage,expectedPairProductOrder,runPairProductOrder};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runPairProductOrder(),null,2));
