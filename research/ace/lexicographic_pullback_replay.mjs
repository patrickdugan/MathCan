import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
import {definition} from './constructible_definition.mjs';
import {buildWellOrder} from './constructible_well_order.mjs';
import {buildLexicographicPullback,pairLexicographicSpecification} from './lexicographic_pullback.mjs';
import {kernel,same,scoped,rejects} from './zf_interface.mjs';

function expectedLexicographicPullback(defs,spec) {
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
  const first=(ps,x,y)=>apply(spec.firstOrder,x,y,...ps),second=(ps,x,y)=>apply(spec.secondOrder,x,y,...ps);
  const rep=(ps,p,a,b)=>apply(spec.representation,p,a,b,...ps);
  const carrier=(ps,k)=>ps[spec[k+'Carrier']];
  const irref=(s,lt)=>every(s,x=>N(lt(x,x)));
  const trans=(s,lt)=>quant(3,(x,y,z)=>I(M(x,s),I(M(y,s),I(M(z,s),I(lt(x,y),I(lt(y,z),lt(x,z)))))));
  const total=(s,lt)=>quant(2,(x,y)=>I(M(x,s),I(M(y,s),O(Q(x,y),O(lt(x,y),lt(y,x))))));
  const minima=(s,lt)=>A(t=>I(every(t,x=>M(x,s)),I(E(x=>M(x,t)),
    E(x=>C(M(x,t),every(t,y=>N(lt(y,x))))))));
  const wo=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const cover=ps=>every(carrier(ps,'output'),p=>some(carrier(ps,'first'),a=>some(carrier(ps,'second'),b=>rep(ps,p,a,b))));
  const func=ps=>quant(5,(p,a,b,c,d)=>I(M(p,carrier(ps,'output')),I(rep(ps,p,a,b),I(rep(ps,p,c,d),C(Q(a,c),Q(b,d))))));
  const inj=ps=>quant(4,(p,q,a,b)=>I(M(p,carrier(ps,'output')),I(M(q,carrier(ps,'output')),
    I(rep(ps,p,a,b),I(rep(ps,q,a,b),Q(p,q))))));
  const lex=(ps,p,q)=>{
    const tail=(a,b)=>some(carrier(ps,'first'),c=>some(carrier(ps,'second'),d=>
      C(rep(ps,q,c,d),O(first(ps,a,c),C(Q(a,c),second(ps,b,d))))));
    return C(C(M(p,carrier(ps,'output')),M(q,carrier(ps,'output'))),
      some(carrier(ps,'first'),a=>some(carrier(ps,'second'),b=>C(rep(ps,p,a,b),tail(a,b)))));
  };
  const fw=ps=>wo(carrier(ps,'first'),(x,y)=>first(ps,x,y));
  const sw=ps=>wo(carrier(ps,'second'),(x,y)=>second(ps,x,y));
  const ow=ps=>wo(carrier(ps,'output'),(x,y)=>lex(ps,x,y));
  const hypotheses={first:fw,second:sw,cover,functional:func,injective:inj};
  const make=(keys,result)=>quant(spec.paramCount,(...ps)=>keys.reduceRight((rest,k)=>I(hypotheses[k](ps),rest),result(ps)))(0);
  const ps=Array.from({length:spec.paramCount},(_,i)=>free(i));
  return {proofs:{
    lexicographic_irreflexive:make(['first','second','functional'],ps=>irref(carrier(ps,'output'),(x,y)=>lex(ps,x,y))),
    lexicographic_transitive:make(['first','second','functional'],ps=>trans(carrier(ps,'output'),(x,y)=>lex(ps,x,y))),
    lexicographic_total:make(['first','second','cover','injective'],ps=>total(carrier(ps,'output'),(x,y)=>lex(ps,x,y))),
    lexicographic_minima:make(['first','second','cover','functional'],ps=>minima(carrier(ps,'output'),(x,y)=>lex(ps,x,y))),
    lexicographic_well_order:make(['first','second','cover','functional','injective'],ow)
  },formulas:{cover:cover(ps)(0),functional:func(ps)(0),injective:inj(ps)(0),
    lexicographic:lex(ps.map(p=>d=>p(d)+2),free(0),free(1))(0),
    well_order_first:fw(ps)(0),well_order_second:sw(ps)(0),well_order_output:ow(ps)(0)},embed};
}

function runLexicographicPullback() {
  const defs=definition('v',true),spec=pairLexicographicSpecification(defs);
  const actual=buildLexicographicPullback(defs,spec),expected=expectedLexicographicPullback(defs,spec);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  const independentSpec={paramCount:5,firstCarrier:0,secondCarrier:1,outputCarrier:2,
    firstOrder:expected.embed(defs.val,[5,0,1]),secondOrder:expected.embed(defs.val,[6,0,1]),representation:defs.pair};
  if(!same(spec,independentSpec)||!same(actual.formulas,expected.formulas))throw Error('lex interface');
  if(!same(actual.formulas.well_order_first,expected.embed(buildWellOrder(defs).formulas.well_order,[0,3])))throw Error('shared well-order layout');
  const checks=[],controls=[],schemas=new Map();let logic=0;
  const reject=(name,fn)=>{if(!rejects(fn))throw Error('negative accepted: '+name);controls.push(name);};
  const exact=(proof,want)=>{if(!same(kernel(0,[],proof,false,'ZF').goal,want))throw Error('target mismatch');};
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  for(const [id,p] of Object.entries(actual.proofs)) {
    if(!scoped(p.goal,0,false)||!same(p.goal,expected.proofs[id]))throw Error('independent target '+id);
    const got=kernel(0,[],p.proof,false,'ZF');if(!same(got.goal,p.goal))throw Error('kernel target');
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);schemas.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(a=>a!=='separation'))throw Error('lex axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used]});
    reject(id+':changed_outer_binder',()=>exact(p.proof,['E',p.goal[1]]));
    reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_separation',()=>kernel(0,[],p.proof,false,'CL'));
    else {exact(p.proof,kernel(0,[],p.proof,false,'CL').goal);logic++;}
  }
  for(const [index,label] of ['first_order','second_order','coverage','coordinate_functionality','joint_injection'].entries()) {
    const changed=structuredClone(expected.proofs.lexicographic_well_order);let p=changed;
    for(let i=0;i<spec.paramCount;i++)p=p[1];for(let i=0;i<index;i++)p=p[2];p.splice(0,p.length,...p[2]);
    reject('well_order:omit_'+label,()=>exact(actual.proofs.lexicographic_well_order.proof,changed));
  }
  for(const [label,change] of [['too_many_parameters',{paramCount:31}],['bad_carrier',{firstCarrier:5}],
    ['free_coordinate',{representation:['=',8,0]}],['class_guard',{firstOrder:['G',0]}]])
    reject('spec:'+label,()=>buildLexicographicPullback(defs,{...spec,...change}));
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03W',part:'lexicographic_pullback_pair_instance',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),
    independent_exact_goals:checks.length,independent_formula_interfaces:7,shared_well_order_layout_checks:1,
    logic_only_checks:logic,negative_controls:controls.length,controls,
    ambient_axiom_instances:[...schemas.values()].map(s=>({name:s.name,params:s.params,body_bytes:JSON.stringify(s.body).length})),
    pinned_L_unchanged:true,
    scope:'lexicographic well-order from two supplied well-orders and total functional jointly injective representation; concrete pair instance checked here'};
}
export {expectedLexicographicPullback,runLexicographicPullback};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)console.log(JSON.stringify(runLexicographicPullback(),null,2));
