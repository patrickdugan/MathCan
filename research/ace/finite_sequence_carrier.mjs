// ACE-03W. Exact carriers of finite tuples and their canonical shortlex order.
// The unrestricted carrier construction bounds indices in union(w), so its
// existence theorem requires no transitivity or omega premise.
import { kernel } from './zf_interface.mjs';
import { buildOrderRealizations, buildRealization } from './relation_realization.mjs';
import { buildCanonicalRelation } from './canonical_relation.mjs';
import { finiteSequenceOrderFormulas, buildFiniteSequenceOrder } from './finite_sequence_order.mjs';

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
  function imported(p){return P(named(p.goal,[]),(_,h)=>liftHyp(p.proof,h.length));}
  const form=(name,...args)=>named(defs[name],args);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const subset=(s,a)=>all(s,x=>M(x,a)),Trans=a=>all(a,x=>subset(x,a));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {fresh,M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ie,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled};
}


function finiteSequenceCarrierFormulas(defs) {
  const {M,Q,I,C,O,N,A,E,named,db,form,all,some,subset}=language(defs);
  const previous=finiteSequenceOrderFormulas(defs);
  const Carrier=(s,w,a)=>named(previous.finite_tuple_carrier,[s,w,a]);
  const Family=(s,w,a)=>named(previous.finite_tuple_family,[s,w,a]);
  const Shortlex=(f,g,w,a,r)=>named(previous.shortlex,[f,g,w,a,r]);
  const Phi=(s,w,a,r,f,g)=>C(C(M(f,s),M(g,s)),Shortlex(f,g,w,a,r));
  const Pair=(p,f,g)=>form('pair',p,f,g),V=(r,f,g)=>form('val',r,f,g);
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const irref=(s,lt)=>all(s,f=>N(lt(f,f)));
  const trans=(s,lt)=>A(f=>A(g=>A(h=>I(M(f,s),I(M(g,s),I(M(h,s),I(lt(f,g),I(lt(g,h),lt(f,h)))))))));
  const total=(s,lt)=>A(f=>A(g=>I(M(f,s),I(M(g,s),O(Q(f,g),O(lt(f,g),lt(g,f)))))));
  const minima=(s,lt)=>A(t=>I(subset(t,s),I(E(f=>M(f,t)),E(f=>C(M(f,t),all(t,g=>N(lt(g,f))))))));
  const WO=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const Exact=(order,s,w,a,r)=>A(p=>iff(M(p,order),E(f=>E(g=>C(Pair(p,f,g),Phi(s,w,a,r,f,g))))));
  const Agree=(order,s,w,a,r)=>A(f=>A(g=>iff(V(order,f,g),Phi(s,w,a,r,f,g))));
  const Unique=(order,s,w,a,r)=>A(other=>I(Exact(other,s,w,a,r),Q(other,order)));
  const Complete=(order,s,w,a,r)=>C(C(C(Exact(order,s,w,a,r),Agree(order,s,w,a,r)),WO(s,(f,g)=>V(order,f,g))),Unique(order,s,w,a,r));
  return {
    finite_tuple_carrier:db(Carrier('s','w','a'),['s','w','a']),
    finite_tuple_family:db(Family('s','w','a'),['s','w','a']),
    guarded_shortlex:db(Phi('s','w','a','r','f','g'),['f','g','s','w','a','r']),
    exact_order:db(Exact('o','s','w','a','r'),['o','s','w','a','r']),
    order_agreement:db(Agree('o','s','w','a','r'),['o','s','w','a','r']),
    unique_order:db(Unique('o','s','w','a','r'),['o','s','w','a','r']),
    complete_order:db(Complete('o','s','w','a','r'),['o','s','w','a','r'])
  };
}

function buildFiniteSequenceCarrierBase(defs) {
  const {M,Q,I,C,O,N,A,E,named,db,ui,ii,al,ar,ai,ue,us,app,ref,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,all,some,subset,qs,compiled}=language(defs);
  const fs=finiteSequenceCarrierFormulas(defs),proofs={};
  const save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const Carrier=(s,w,a)=>named(fs.finite_tuple_carrier,[s,w,a]);
  const Family=(s,w,a)=>named(fs.finite_tuple_family,[s,w,a]);
  const Tuple=(f,m,a)=>form('tuple',f,m,a),V=(f,i,y)=>form('val',f,i,y);
  const Pair=(p,i,y)=>form('pair',p,i,y),iff=(p,q)=>C(I(p,q),I(q,p));
  const Power=(b,p)=>A(x=>iff(M(x,p),subset(x,b)));
  const Union=(b,u)=>A(x=>iff(M(x,u),E(y=>C(M(y,b),M(x,y)))));
  const pairBound=buildOrderRealizations(defs).induced.proofs.ordered_pair_double_power_bound;
  function unionIn(union,x,y,yb,xy) {
    const target=ue(union,x).goal[2][1];
    return into(union,x,ei(target,y,ai(yb,xy)));
  }
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);

  save('tuple_values_belong_to_carrier',qs(5,(f,m,a,i,y)=>ii(Tuple(f,m,a),tuple=>ii(M(i,m),im=>ii(V(f,i,y),value=>
    open(app(ue(ar(tuple),i),im),(z,zp)=>
      open(app(ue(ar(al(tuple)),i),im),(v,vp)=>{
        const yv=app(ue(ar(vp),y),value),zv=app(ue(ar(vp),z),ar(zp));
        return eqSub(sym(chain(yv,sym(zv))),x=>M(x,a),al(zp));
      })
    )
  )))));

  save('tuple_graph_double_power_bound',qs(6,(f,m,a,b,p1,p2)=>
    ii(subset(m,b),mb=>ii(subset(a,b),ab=>ii(Power(b,p1),pow1=>ii(Power(p1,p2),pow2=>
      ii(Tuple(f,m,a),tuple=>use(imported(pairBound),bound=>
      use(imported(proofs.tuple_values_belong_to_carrier),range=>ui(p=>ii(M(p,f),pf=>
        open(app(ue(al(al(tuple)),p),pf),(i,ip)=>open(ar(ip),(y,pair)=>{
          const value=ei(V(f,i,y),p,ai(pf,pair));
          const ya=app(us(range,f,m,a,i,y),tuple,al(ip),value);
          return app(us(bound,b,p1,p2,p,i,y),pow1,pow2,app(ue(mb,i),al(ip)),app(ue(ab,y),ya),pair);
        }))
      )))
      ))
    ))))
  ));

  // For m in w, every index in m belongs to union(w). Range values belong
  // to a, and the exact tuple graph is a subset of the double power bound.
  save('finite_sequence_carrier_exists',qs(2,(w,a)=>
    use(imported(proofs.tuple_graph_double_power_bound),bound=>
    open(ue(ax({name:'union'}),w),(u,wu)=>
    open(us(ax({name:'pairing'}),u,a),(v,vp)=>
    open(ue(ax({name:'union'}),v),(b,vb)=>
    open(ue(ax({name:'power'}),b),(p1,pow1)=>
    open(ue(ax({name:'power'}),p1),(p2,pow2)=>
    open(ue(ax({name:'power'}),p2),(p3,pow3)=>{
      const candidate=f=>some(w,m=>Tuple(f,m,a));
      return open(separation(p3,[w,a],candidate),(s,sep)=>{
        const exact=ui(f=>ai(
          ii(M(f,s),member=>ar(from(sep,f,member))),
          ii(candidate(f),witness=>open(witness,(m,mp)=>{
            const ub=into(vp,u,ol(ref(u),Q(u,a))),ab=into(vp,a,or(Q(a,u),ref(a)));
            const indices=ui(i=>ii(M(i,m),im=>unionIn(vb,i,u,ub,unionIn(wu,i,m,al(mp),im))));
            const range=ui(y=>ii(M(y,a),ya=>unionIn(vb,y,a,ab,ya)));
            const limited=app(us(bound,f,m,a,b,p1,p2),indices,range,pow1,pow2,ar(mp));
            return into(sep,f,ai(into(pow3,f,limited),witness));
          }))
        ));
        return ei(E(s=>Carrier(s,w,a)),s,exact);
      });
    }))
    )))))
  ));

  save('finite_sequence_carrier_unique',qs(4,(w,a,s,t)=>ii(Carrier(s,w,a),sc=>ii(Carrier(t,w,a),tc=>
    app(us(ax({name:'extensionality'}),s,t),ui(f=>ai(
      ii(M(f,s),fs=>into(tc,f,from(sc,f,fs))),
      ii(M(f,t),ft=>into(sc,f,from(tc,f,ft)))
    )))
  ))));
  save('finite_sequence_carrier_is_family',qs(3,(s,w,a)=>ii(Carrier(s,w,a),exact=>
    ui(f=>ii(M(f,s),fs=>from(exact,f,fs)))
  )));
  return {proofs,formulas:fs};
}

function buildFiniteSequenceCarrier(defs) {
  const {M,Q,F,I,C,O,N,A,E,named,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,imported,form,Omega,all,subset,qs,compiled}=language(defs);
  const base=buildFiniteSequenceCarrierBase(defs),proofs={...base.proofs},fs=base.formulas;
  const previous=buildFiniteSequenceOrder(defs),orderForms=previous.formulas;
  const save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const Carrier=(s,w,a)=>named(fs.finite_tuple_carrier,[s,w,a]);
  const Shortlex=(f,g,w,a,r)=>named(orderForms.shortlex,[f,g,w,a,r]);
  const Phi=(s,w,a,r,f,g)=>named(fs.guarded_shortlex,[f,g,s,w,a,r]);
  const Complete=(order,s,w,a,r)=>named(fs.complete_order,[order,s,w,a,r]);
  const V=(r,x,y)=>form('val',r,x,y);
  const irref=(s,lt)=>all(s,f=>N(lt(f,f)));
  const trans=(s,lt)=>A(f=>A(g=>A(h=>I(M(f,s),I(M(g,s),I(M(h,s),I(lt(f,g),I(lt(g,h),lt(f,h)))))))));
  const total=(s,lt)=>A(f=>A(g=>I(M(f,s),I(M(g,s),O(Q(f,g),O(lt(f,g),lt(g,f)))))));
  const minima=(s,lt)=>A(t=>I(subset(t,s),I(E(f=>M(f,t)),E(f=>C(M(f,t),all(t,g=>N(lt(g,f))))))));
  const WO=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));

  save('shortlex_explicit_carrier_guards',qs(4,(s,w,a,r)=>ii(WO(s,(f,g)=>Shortlex(f,g,w,a,r)),old=>{
    const lt=(f,g)=>Phi(s,w,a,r,f,g);
    const irr=ui(f=>ii(M(f,s),fs=>ii(lt(f,f),ff=>app(app(ue(al(al(al(old))),f),fs),ar(ff)))));
    const tr=qs(3,(f,g,h)=>ii(M(f,s),fs=>ii(M(g,s),gs=>ii(M(h,s),hs=>ii(lt(f,g),fg=>ii(lt(g,h),gh=>
      ai(ai(fs,hs),app(us(ar(al(al(old))),f,g,h),fs,gs,hs,ar(fg),ar(gh)))
    ))))));
    const tot=qs(2,(f,g)=>ii(M(f,s),fs=>ii(M(g,s),gs=>{
      const goal=O(Q(f,g),O(lt(f,g),lt(g,f)));
      return oe(app(us(ar(al(old)),f,g),fs,gs),goal,equal=>ol(equal,goal[2]),either=>oe(either,goal,
        fg=>or(Q(f,g),ol(ai(ai(fs,gs),fg),lt(g,f))),
        gf=>or(Q(f,g),or(lt(f,g),ai(ai(gs,fs),gf)))));
    })));
    const mins=ui(t=>ii(subset(t,s),ts=>ii(E(f=>M(f,t)),nonempty=>
      open(app(ue(ar(old),t),ts,nonempty),(f,fp)=>{
        const goal=E(f=>C(M(f,t),all(t,g=>N(lt(g,f)))));
        const minimal=ui(g=>ii(M(g,t),gt=>ii(lt(g,f),gf=>
          app(app(ue(ar(fp),g),gt),ar(gf))
        )));
        return ei(goal,f,ai(al(fp),minimal));
      })
    )));
    return ai(ai(ai(irr,tr),tot),mins);
  })));

  save('finite_sequence_carrier_well_order',qs(4,(s,w,a,r)=>ii(Omega(w),ow=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>ii(Carrier(s,w,a),carrier=>{
      const family=app(us(imported(proofs.finite_sequence_carrier_is_family),s,w,a),carrier);
      const shortlex=app(us(imported(previous.proofs.finite_shortlex_well_order),w,a,r,s),ow,letters,family);
      return app(us(imported(proofs.shortlex_explicit_carrier_guards),s,w,a,r),shortlex);
    }))
  )));

  const realization=buildRealization(defs,fs.guarded_shortlex,4,0,proofs.finite_sequence_carrier_well_order);
  const canonical=buildCanonicalRelation(defs,fs.guarded_shortlex,4,0,realization,proofs.finite_sequence_carrier_well_order);
  for(const [name,p] of Object.entries(canonical.proofs))proofs['shortlex_'+name]=p;

  save('finite_sequence_carrier_and_canonical_order',qs(3,(w,a,r)=>ii(Omega(w),ow=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>
      open(us(imported(proofs.finite_sequence_carrier_exists),w,a),(s,carrier)=>{
        const ordered=app(us(imported(canonical.proofs.composed_canonical_well_order),s,w,a,r),ow,letters,carrier);
        const goal=E(s=>C(Carrier(s,w,a),E(order=>Complete(order,s,w,a,r))));
        return ei(goal,s,ai(carrier,ordered));
      })
    )
  )));
  return {proofs,formulas:fs,existing_tuple_range:previous.proofs.tuple_value_in_carrier};
}

export { finiteSequenceCarrierFormulas, buildFiniteSequenceCarrierBase, buildFiniteSequenceCarrier };
