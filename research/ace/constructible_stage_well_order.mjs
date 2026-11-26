// ACE-03X. Coherent ordinal order histories project to the pinned L hierarchy.
// This final link proves ambient well-orderability of each constructible set.
// Membership of the resulting order relation in L remains a separate goal.
import { kernel } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildUniformHistoryRecursion } from './uniform_history_recursion.mjs';
import { constructibleOrderHistoryFormulas, buildConstructibleOrderHistory } from './constructible_order_history.mjs';
import { carrierHistoryProjectionFormulas, buildCarrierHistoryProjection } from './carrier_history_projection.mjs';
import { restrictedWellOrderFormulas, buildRestrictedWellOrder } from './restricted_well_order.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`sc${serial++}`;
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],F=['F'];
  const I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q],N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh();return [op,x,fn(x)];};
  const A=fn=>bind('A',fn),E=fn=>bind('E',fn);
  function named(p,env) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,env[a],env[b]];
    if(op==='A'||op==='E'){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env=[]) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='='){
      const i=env.indexOf(a),j=env.indexOf(b);
      if(i<0||j<0)throw Error(`unbound ${a} ${b}`);
      return [op,i,j];
    }
    if(op==='A'||op==='E')return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }
  function replace(p,x,y) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,a===x?y:a,b===x?y:b];
    if(op==='A'||op==='E'){
      if(a===x)return p;
      if(a===y){const z=fresh();return [op,z,replace(replace(b,a,z),x,y)];}
      return [op,a,replace(b,x,y)];
    }
    return [op,replace(a,x,y),replace(b,x,y)];
  }
  const P=(goal,emit)=>({goal,emit});
  function assume(goal) {
    const id=fresh();return {id,p:P(goal,(_,h)=>{const i=h.indexOf(id);if(i<0)throw Error('unbound hypothesis');return ['h',i];})};
  }
  function ui(fn){const x=fresh(),p=fn(x);return P(['A',x,p.goal],(e,h)=>['uI',p.emit([x,...e],h)]);}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>['iI',db(g,e),p.emit(e,[...h,a.id])]);}
  const al=p=>P(p.goal[1],(e,h)=>['aL',p.emit(e,h)]),ar=p=>P(p.goal[2],(e,h)=>['aR',p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>['aI',p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>['iE',p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>['uE',p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p),app=(p,...qs)=>qs.reduce(ie,p);
  const ref=x=>P(Q(x,x),(e,h)=>['refl',e.indexOf(x)]);
  const dn=p=>P(p.goal[1][1],(e,h)=>['dne',p.emit(e,h)]);
  const fe=(p,g)=>P(g,(e,h)=>['fE',p.emit(e,h),db(g,e)]);
  function ei(g,x,p){return P(g,(e,h)=>['eI',db(g[2],[g[1],...e]),e.indexOf(x),p.emit(e,h)]);}
  function open(p,fn){
    if(p.goal[0]!=='E')throw Error('expected existential');
    const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
    return P(q.goal,(e,h)=>['eE',p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);
  }
  function oe(p,g,left,right){
    const a=assume(p.goal[1]),b=assume(p.goal[2]),l=left(a.p),r=right(b.p);
    return P(g,(e,h)=>['oE',p.emit(e,h),l.emit(e,[...h,a.id]),r.emit(e,[...h,b.id])]);
  }
  const ol=(p,g)=>P(O(p.goal,g),(e,h)=>['oL',p.emit(e,h),db(g,e)]);
  const or=(g,p)=>P(O(g,p.goal),(e,h)=>['oR',db(g,e),p.emit(e,h)]);
  function eqSub(eq,prop,p){const v=fresh(),g=prop(v);return P(replace(g,v,eq.goal[2]),(e,h)=>['eqS',db(g,[v,...e]),eq.emit(e,h),p.emit(e,h)]);}
  const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
  const use=(p,fn)=>ie(ii(p.goal,fn),p);
  const ax=spec=>P(named(kernel(0,[],['axiom',spec],false,'ZF').goal,[]),()=>['axiom',spec]);
  function separation(a,params,predicate) {
    const x=fresh(),spec={name:'separation',params:params.length,body:db(predicate(x),[x,...params])};
    return us(ax(spec),...params.slice().reverse(),a);
  }
  const from=(p,x,px)=>app(al(ue(p,x)),px),into=(p,x,px)=>app(ar(ue(p,x)),px);
  function liftHyp(p,n){if(!Array.isArray(p))return p;if(p[0]==='h')return ['h',p[1]+n];return p.map(x=>liftHyp(x,n));}
  function imported(p){return P(named(p.goal,[]),(_,h)=>h.length===0?p.proof:liftHyp(p.proof,h.length));}
  const form=(name,...args)=>named(defs[name],args);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const subset=(s,a)=>all(s,x=>M(x,a)),Trans=a=>all(a,x=>subset(x,a));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {fresh,M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ie,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled};
}

function finalLanguage(defs) {
  const L=language(defs),{C,A,E,I,M,named,db,all,subset,Trans}=L;
  const hf=constructibleOrderHistoryFormulas(defs),pf=carrierHistoryProjectionFormulas(defs),rf=restrictedWellOrderFormulas(defs);
  const Val=(f,i,a)=>named(defs.val,[f,i,a]),Ord=d=>named(defs.ordinal,[d]);
  const Succ=(a,d)=>named(defs.successor,[a,d]),Pinned=(f,d)=>named(defs.stageGraph,[f,d]);
  const Hist=(f,d)=>named(hf.history,[f,d]),Complete=(f,d,g)=>named(pf.complete,[f,d,g]);
  const GoodCarriers=(g,d)=>named(pf.good_carriers,[g,d]),W=(a,r)=>named(pf.well_order,[a,r]);
  const PairOnly=(s,b)=>named(rf.pair_only,[s,b]);
  const InL=x=>named(defs.L,[x]);
  const Realized=d=>E(f=>E(g=>C(Hist(f,d),C(Complete(f,d,g),GoodCarriers(g,d)))));
  const forms={history:hf.history,projection:pf.complete,good_carriers:pf.good_carriers,
    realized_history:db(Realized('d'),['d']),well_order:pf.well_order,
    subset:db(subset('a','b'),['a','b']),transitive:db(Trans('a'),['a']),pair_only:rf.pair_only,pinned_stage_graph:defs.stageGraph,pinned_L:defs.L};
  return {...L,Val,Ord,Succ,Pinned,Hist,Complete,GoodCarriers,W,PairOnly,InL,Realized,forms};
}

function constructibleStageWellOrderFormulas(defs) {return finalLanguage(defs).forms;}

function buildConstructibleStageWellOrder(defs,part='all',options={}) {
  if(!['subset','projection','stages','all'].includes(part))throw Error('final stage part');
  const {M,Q,C,A,E,replace,ui,ii,al,ar,ai,ue,us,app,ref,ei,open,or,eqSub,sym,use,from,into,imported,subset,Trans,qs,compiled,
    Val,Ord,Succ,Pinned,Hist,Complete,GoodCarriers,W,PairOnly,InL,Realized,forms}=finalLanguage(defs);
  const progress=label=>options.onProgress?.(label);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);progress('saved_'+id);return proofs[id];};
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inside(goal,xs[0]),xs.slice(1),p));
  const project=(p,i,n)=>n===1?p:i===n-1?ar(p):project(al(p),i,n-1);
  const using=(specs,fn)=>use(specs.map(imported).reduce(ai),p=>fn(...specs.map((_,i)=>project(p,i,specs.length))));

  save('well_order_on_subset',qs(3,(a,r,b)=>ii(subset(b,a),ba=>ii(W(a,r),order=>{
    const irr=ui(x=>ii(M(x,b),xb=>app(ue(al(al(al(order))),x),app(ue(ba,x),xb))));
    const trans=qs(3,(x,y,z)=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>
      app(us(ar(al(al(order))),x,y,z),app(ue(ba,x),xb),app(ue(ba,y),yb),app(ue(ba,z),zb))
    ))));
    const total=qs(2,(x,y)=>ii(M(x,b),xb=>ii(M(y,b),yb=>app(us(ar(al(order)),x,y),app(ue(ba,x),xb),app(ue(ba,y),yb)))));
    const minima=ui(s=>ii(subset(s,b),sb=>ii(E(x=>M(x,s)),nonempty=>{
      const sa=ui(x=>ii(M(x,s),xs=>app(ue(ba,x),app(ue(sb,x),xs))));
      return app(ue(ar(order),s),sa,nonempty);
    })));
    return ai(ai(ai(irr,trans),total),minima);
  }))));
  if(part==='subset')return {proofs,formulas:forms};

  progress('before_history');
  const history=buildConstructibleOrderHistory(defs,'existence',{onProgress:label=>progress('history_'+label)});
  if(typeof globalThis.gc==='function')globalThis.gc();
  progress('after_history');
  const projection=buildCarrierHistoryProjection(defs);
  if(typeof globalThis.gc==='function')globalThis.gc();
  progress('after_projection');
  save('ordinal_history_with_pinned_projection',using([
    history.proofs.ordinal_order_history_exists_unique,
    projection.proofs.ordinal_carrier_history_projection,
    projection.proofs.projected_carriers_are_good
  ],(histories,projectHistory,goodCarriers)=>ui(d=>ii(Ord(d),od=>
    open(app(ue(histories,d),od),(f,fp)=>open(app(us(projectHistory,f,d),od,al(fp)),(g,pg)=>{
      const good=app(us(goodCarriers,f,d,g),al(fp),ar(al(pg)));
      return pack(Realized(d),[f,g],ai(al(fp),ai(pg,good)));
    }))
  ))));
  if(part==='projection')return {proofs,formulas:forms};

  const earlier=buildE(defs,true);
  save('all_pinned_stage_values_well_ordered',using([
    proofs.ordinal_history_with_pinned_projection,earlier.stage_graph_coherence
  ],(exists,coherence)=>qs(2,(d,g)=>ii(Ord(d),od=>ii(Pinned(g,d),given=>
    open(app(ue(exists,d),od),(f,fp)=>open(fp,(h,hp)=>{
      const complete=al(ar(hp)),good=ar(ar(hp));
      const agree=app(us(coherence,g,h,d,d),al(od),al(od),given,ar(complete));
      return ui(i=>ii(M(i,d),id=>ui(a=>ii(Val(g,i,a),ga=>
        open(app(ue(ar(al(ar(complete))),i),id),(b,bp)=>{
          const atIndex=app(ue(agree,i),id,id);
          const equal=app(ue(app(ue(atIndex,a),ga),b),al(bp));
          const hasOrder=app(ue(app(ue(good,i),id),b),al(bp));
          return eqSub(sym(equal),x=>E(r=>C(Trans(x),W(x,r))),hasOrder);
        })
      ))));
    }))
  )))));
  if(part==='stages')return {proofs,formulas:forms};

  const ordinalSuccessor=buildUniformHistoryRecursion(defs,['=',2,2],0,{only:['ordinal_successor']}).proofs.ordinal_successor;
  const restricted=buildRestrictedWellOrder(defs);
  save('every_constructible_set_has_ambient_well_order',using([
    proofs.all_pinned_stage_values_well_ordered,restricted.proofs.restricted_well_order_exists,ordinalSuccessor
  ],(stages,restrict,successor)=>ui(x=>ii(InL(x),constructible=>
    open(constructible,(a,ap)=>open(ar(ap),(d,dp)=>open(ar(dp),(g,gp)=>open(ar(gp),(b,bp)=>{
      const od=app(us(successor,a,d),al(ap),al(dp));
      const containsIndex=into(al(dp),a,or(M(a,a),ref(a)));
      const good=app(ue(app(ue(app(us(stages,d,g),od,al(gp)),a),containsIndex),b),al(bp));
      return open(good,(r,rb)=>{
        const included=app(ue(al(rb),x),ar(bp));
        return open(app(us(restrict,b,r,x),included,ar(rb)),(s,ordered)=>
          ei(E(s=>C(W(x,s),PairOnly(s,x))),s,ar(ordered)));
      });
    }))))
  ))));
  return {proofs,formulas:forms};
}

export { constructibleStageWellOrderFormulas, buildConstructibleStageWellOrder };

