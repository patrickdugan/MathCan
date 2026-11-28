// ACE-03X. Exact canonical union of a directed initial-segment order family.
// The family H stores pairs <carrier, order> through the pinned Val predicate.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildCoherentWellOrder } from './coherent_well_order.mjs';
import { buildRealization } from './relation_realization.mjs';
import { buildCanonicalRelation } from './canonical_relation.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`t${serial++}`;
  const M=(a,b)=>['M',a,b], Q=(a,b)=>['=',a,b], F=['F'];
  const I=(p,q)=>['>',p,q], C=(p,q)=>['&',p,q], O=(p,q)=>['|',p,q], N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh(); return [op,x,fn(x)];};
  const A=fn=>bind('A',fn), E=fn=>bind('E',fn);
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
    const id=fresh();
    return {id,p:P(goal,(_,h)=>{const i=h.indexOf(id);if(i<0)throw Error('unbound hypothesis');return ['h',i];})};
  }
  function ui(fn){const x=fresh(),p=fn(x);return P(['A',x,p.goal],(e,h)=>['uI',p.emit([x,...e],h)]);}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>['iI',db(g,e),p.emit(e,[...h,a.id])]);}
  const al=p=>P(p.goal[1],(e,h)=>['aL',p.emit(e,h)]);
  const ar=p=>P(p.goal[2],(e,h)=>['aR',p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>['aI',p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>['iE',p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>['uE',p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p), app=(p,...qs)=>qs.reduce(ie,p);
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
  const from=(p,x,px)=>app(al(ue(p,x)),px);
  const into=(p,x,px)=>app(ar(ue(p,x)),px);
  function liftHyp(p,n){if(!Array.isArray(p))return p;if(p[0]==='h')return ['h',p[1]+n];return p.map(x=>liftHyp(x,n));}
  function imported(p){return P(named(p.goal,[]),(_,h)=>liftHyp(p.proof,h.length));}


  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,all,some,qs,compiled};
}

function limitLanguage(defs) {
  const L=language(defs),{M,Q,I,C,O,N,A,E,named,db,all,some}=L;
  const B=(p,q)=>C(I(p,q),I(q,p));
  const Val=(r,x,y)=>named(defs.val,[r,x,y]),Pair=(p,x,y)=>named(defs.pair,[p,x,y]);
  const Sub=(s,a)=>all(s,x=>M(x,a));
  const Trans=a=>all(a,x=>Sub(x,a));
  const LocalTrans=h=>A(a=>A(r=>I(Val(h,a,r),Trans(a))));
  const Union=(h,u)=>A(x=>B(M(x,u),some(h,y=>M(x,y))));
  const CarrierFamily=(h,k)=>A(a=>B(M(a,k),E(r=>Val(h,a,r))));
  const UnionCarrier=(h,b)=>A(x=>B(M(x,b),E(a=>E(r=>C(Val(h,a,r),M(x,a))))));
  const Phi=(h,b,x,y)=>C(C(M(x,b),M(y,b)),E(a=>E(r=>C(C(Val(h,a,r),C(M(x,a),M(y,a))),Val(r,x,y)))));
  const Exact=(h,b,t)=>A(p=>B(M(p,t),E(x=>E(y=>C(Pair(p,x,y),Phi(h,b,x,y))))));
  const Agreement=(h,b,t)=>A(x=>A(y=>B(Val(t,x,y),Phi(h,b,x,y))));
  const Restriction=(a,r,t)=>A(x=>A(y=>I(M(x,a),I(M(y,a),B(Val(t,x,y),Val(r,x,y))))));
  const Initial=(a,b,t)=>A(x=>I(M(x,a),A(y=>I(M(y,b),I(Val(t,y,x),M(y,a))))));
  const irref=(s,r)=>all(s,x=>N(Val(r,x,x)));
  const trans=(s,r)=>A(x=>A(y=>A(z=>I(M(x,s),I(M(y,s),I(M(z,s),I(Val(r,x,y),I(Val(r,y,z),Val(r,x,z)))))))));
  const total=(s,r)=>A(x=>A(y=>I(M(x,s),I(M(y,s),O(Q(x,y),O(Val(r,x,y),Val(r,y,x)))))));
  const minima=(s,r)=>A(v=>I(Sub(v,s),I(E(x=>M(x,v)),E(x=>C(M(x,v),all(v,y=>N(Val(r,y,x))))))));
  const WO=(s,r)=>C(C(C(irref(s,r),trans(s,r)),total(s,r)),minima(s,r));
  const Local=h=>A(a=>A(r=>I(Val(h,a,r),WO(a,r))));
  const Directed=h=>A(a=>A(r=>A(b=>A(s=>I(Val(h,a,r),I(Val(h,b,s),E(c=>E(t=>C(Val(h,c,t),C(Sub(a,c),Sub(b,c)))))))))));
  const Extends=h=>A(a=>A(r=>A(b=>A(s=>I(Val(h,a,r),I(Val(h,b,s),I(Sub(a,b),C(Restriction(a,r,s),Initial(a,b,s)))))))));
  const State=(h,b,t)=>C(UnionCarrier(h,b),Exact(h,b,t));
  const Value=(h,p)=>E(b=>E(t=>C(Pair(p,b,t),State(h,b,t))));
  const AllExtensions=(h,b,t)=>A(a=>A(r=>I(Val(h,a,r),C(Sub(a,b),C(Restriction(a,r,t),Initial(a,b,t))))));
  const forms={
    carrier_family:db(CarrierFamily('h','k'),['h','k']),union_carrier:db(UnionCarrier('h','b'),['h','b']),
    order_predicate:db(Phi('h','b','x','y'),['x','y','h','b']),exact_order:db(Exact('h','b','t'),['h','b','t']),
    agreement:db(Agreement('h','b','t'),['h','b','t']),restriction:db(Restriction('a','r','t'),['a','r','t']),
    initial:db(Initial('a','b','t'),['a','b','t']),local:db(Local('h'),['h']),directed:db(Directed('h'),['h']),
    extends:db(Extends('h'),['h']),state:db(State('h','b','t'),['h','b','t']),value:db(Value('h','p'),['h','p']),
    all_extensions:db(AllExtensions('h','b','t'),['h','b','t']),well_order:db(WO('a','r'),['a','r']),
    transitive:db(Trans('a'),['a']),local_transitive:db(LocalTrans('h'),['h'])
  };
  return {...L,B,Val,Pair,Sub,Trans,LocalTrans,Union,CarrierFamily,UnionCarrier,Phi,Exact,Agreement,Restriction,Initial,WO,Local,Directed,Extends,State,Value,AllExtensions,forms};
}

function canonicalLimitOrderFormulas(defs) {return limitLanguage(defs).forms;}

function buildCanonicalLimitOrder(defs) {
  const {M,Q,F,I,C,N,A,E,named,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,all,some,qs,compiled,
    Val,Pair,Sub,Trans,LocalTrans,Union,CarrierFamily,UnionCarrier,Phi,Exact,Agreement,Restriction,Initial,WO,Local,Directed,Extends,State,Value,AllExtensions,forms}=limitLanguage(defs);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);return proofs[id];};
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const bounded=(goal,x,m,p)=>ei(goal,x,ai(m,p));
  const old=buildCoherentWellOrder(defs);
  const Capture=(b,k)=>named(old.formulas.capture,[b,k]);
  const LocalAt=(b,k,t)=>named(old.formulas.local,[b,k,t]);
  const InitialAt=(b,k,t)=>named(old.formulas.initial,[b,k,t]);
  const woPhi=(h,b)=>{
    // Build the formula-valued order directly with named binders.
    const lt=(x,y)=>Phi(h,b,x,y);
    const irr=all(b,x=>N(lt(x,x)));
    const tr=A(x=>A(y=>A(z=>I(M(x,b),I(M(y,b),I(M(z,b),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
    const tot=A(x=>A(y=>I(M(x,b),I(M(y,b),['|',Q(x,y),['|',lt(x,y),lt(y,x)]]))));
    const mins=A(s=>I(Sub(s,b),I(E(x=>M(x,s)),E(x=>C(M(x,s),all(s,y=>N(lt(y,x))))))));
    return C(C(C(irr,tr),tot),mins);
  };
  const identity=compiled(qs(2,(h,b)=>ii(woPhi(h,b),p=>p)));
  const realized=buildRealization(defs,forms.order_predicate,2,1,identity);
  const canonical=buildCanonicalRelation(defs,forms.order_predicate,2,1,realized,identity);
  proofs.limit_relation_exists=canonical.proofs.exact_membership_exists;
  proofs.limit_relation_unique=canonical.proofs.exact_membership_unique;
  proofs.limit_relation_agreement=canonical.proofs.exact_membership_implies_agreement;

  function unionIn(union,x,y,yh,xy){
    const goal=ue(union,x).goal[2][1];
    return into(union,x,bounded(goal,y,yh,xy));
  }
  function carrierIn(union,x,a,r,stage,xa){
    const goal=ue(union,x).goal[2][1],inner=inside(goal,a);
    return into(union,x,ei(goal,a,ei(inner,r,ai(stage,xa))));
  }
  function common(directed,a,r,b,s,ha,hb,fn){
    return open(app(us(directed,a,r,b,s),ha,hb),(c,cp)=>open(cp,(t,tp)=>fn(c,t,al(tp),al(ar(tp)),ar(ar(tp)))));
  }
  function openPhi(p,fn){return open(ar(p),(a,ap)=>open(ap,(r,rp)=>fn(a,r,al(al(rp)),al(ar(al(rp))),ar(ar(al(rp))),ar(rp))));}
  function phiIn(h,b,x,y,a,r,xb,yb,stage,xa,ya,xy){
    const goal=Phi(h,b,x,y),ag=goal[2],rg=inside(ag,a);
    return ai(ai(xb,yb),ei(ag,a,ei(rg,r,ai(ai(stage,ai(xa,ya)),xy))));
  }

  save('family_coordinates_double_union',qs(5,(h,u,v,a,r)=>ii(Union(h,u),hu=>ii(Union(u,v),uv=>ii(Val(h,a,r),stage=>
    open(stage,(p,pp)=>open(ar(pp),(s,sp)=>open(sp,(d,dp)=>{
      const single=al(al(dp)),double=ar(al(dp)),outer=ar(dp);
      const sp0=into(outer,s,ol(ref(s),Q(s,d))),dp0=into(outer,d,or(Q(d,s),ref(d)));
      const su=unionIn(hu,s,p,al(pp),sp0),du=unionIn(hu,d,p,al(pp),dp0);
      const as=into(single,a,ref(a)),rd=into(double,r,or(Q(r,a),ref(r)));
      return ai(unionIn(uv,a,s,su,as),unionIn(uv,r,d,du,rd));
    })))
  )))));
  save('carrier_family_exists',ui(h=>
    open(ue(ax({name:'union'}),h),(u,hu)=>open(ue(ax({name:'union'}),u),(v,uv)=>
      open(separation(v,[h],a=>E(r=>Val(h,a,r))),(k,kp)=>{
        const exact=ui(a=>ai(
          ii(M(a,k),ak=>ar(from(kp,a,ak))),
          ii(E(r=>Val(h,a,r)),hit=>open(hit,(r,stage)=>
            into(kp,a,ai(al(app(us(imported(proofs.family_coordinates_double_union),h,u,v,a,r),hu,uv,stage)),hit))))
        ));
        return ei(E(k=>CarrierFamily(h,k)),k,exact);
      })
    ))
  ));
  save('union_carrier_exists',ui(h=>
    open(ue(imported(proofs.carrier_family_exists),h),(k,carriers)=>
      open(ue(ax({name:'union'}),k),(b,union)=>{
        const exact=ui(x=>ai(
          ii(M(x,b),xb=>open(from(union,x,xb),(a,ap)=>open(from(carriers,a,al(ap)),(r,stage)=>{
            const goal=E(a=>E(r=>C(Val(h,a,r),M(x,a))));
            return ei(goal,a,ei(inside(goal,a),r,ai(stage,ar(ap))));
          }))),
          ii(E(a=>E(r=>C(Val(h,a,r),M(x,a)))),hit=>open(hit,(a,ap)=>open(ap,(r,rp)=>{
            const ak=into(carriers,a,ei(E(r=>Val(h,a,r)),r,al(rp)));
            return unionIn(union,x,a,ak,ar(rp));
          })))
        ));
        return ei(E(b=>UnionCarrier(h,b)),b,exact);
      })
    )
  ));
  save('union_carrier_unique',qs(3,(h,b,c)=>ii(UnionCarrier(h,b),hb=>ii(UnionCarrier(h,c),hc=>
    app(us(ax({name:'extensionality'}),b,c),ui(x=>ai(
      ii(M(x,b),xb=>into(hc,x,from(hb,x,xb))),ii(M(x,c),xc=>into(hb,x,from(hc,x,xc)))
    )))
  ))));
  save('stage_is_subset_of_union',qs(4,(h,b,a,r)=>ii(UnionCarrier(h,b),union=>ii(Val(h,a,r),stage=>
    ui(x=>ii(M(x,a),xa=>carrierIn(union,x,a,r,stage,xa)))
  ))));

  save('union_carrier_transitive',qs(2,(h,b)=>ii(UnionCarrier(h,b),union=>ii(LocalTrans(h),local=>
    ui(x=>ii(M(x,b),xb=>ui(y=>ii(M(y,x),yx=>
      open(from(union,x,xb),(a,ap)=>open(ap,(r,rp)=>{
        const ta=app(us(local,a,r),al(rp));
        const ya=app(ue(app(ue(ta,x),ar(rp)),y),yx);
        return carrierIn(union,y,a,r,al(rp),ya);
      }))
    ))))
  ))));

  save('union_order_restriction',qs(5,(h,b,t,a,r)=>ii(UnionCarrier(h,b),union=>ii(Directed(h),directed=>
    ii(Extends(h),extension=>ii(Agreement(h,b,t),agreement=>ii(Val(h,a,r),stage=>
      qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>ai(
        ii(Val(t,x,y),xy=>openPhi(app(al(us(agreement,x,y)),xy),(c,s,other,xc,yc,local)=>
          common(directed,a,r,c,s,stage,other,(d,u,hd,ad,cd)=>{
            const ac=al(app(us(extension,a,r,d,u),stage,hd,ad));
            const cc=al(app(us(extension,c,s,d,u),other,hd,cd));
            const atCommon=app(ar(app(us(cc,x,y),xc,yc)),local);
            return app(al(app(us(ac,x,y),xa,ya)),atCommon);
          })
        )),
        ii(Val(r,x,y),xy=>app(ar(us(agreement,x,y)),phiIn(h,b,x,y,a,r,
          carrierIn(union,x,a,r,stage,xa),carrierIn(union,y,a,r,stage,ya),stage,xa,ya,xy)))
      ))))
    )))))
  ));
  save('union_order_initial',qs(5,(h,b,t,a,r)=>ii(UnionCarrier(h,b),union=>ii(Directed(h),directed=>
    ii(Extends(h),extension=>ii(Agreement(h,b,t),agreement=>ii(Val(h,a,r),stage=>
      ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,b),yb=>ii(Val(t,y,x),yx=>
        openPhi(app(al(us(agreement,y,x)),yx),(c,s,other,yc,xc,local)=>
          common(directed,a,r,c,s,stage,other,(d,u,hd,ad,cd)=>{
            const oldInitial=ar(app(us(extension,a,r,d,u),stage,hd,ad));
            const otherRestriction=al(app(us(extension,c,s,d,u),other,hd,cd));
            const atCommon=app(ar(app(us(otherRestriction,y,x),yc,xc)),local);
            return app(ue(app(ue(oldInitial,x),xa),y),app(ue(cd,y),yc),atCommon);
          })
        )
      )))))
    )))))
  ));

  // A local comparison equivalence suffices to transfer each order clause.
  save('bounded_order_agreement_transfer',qs(3,(a,r,t)=>ii(WO(a,r),oldOrder=>ii(Restriction(a,r,t),restriction=>{
    const toOld=(x,y,xa,ya,p)=>app(al(app(us(restriction,x,y),xa,ya)),p);
    const toNew=(x,y,xa,ya,p)=>app(ar(app(us(restriction,x,y),xa,ya)),p);
    const irr=ui(x=>ii(M(x,a),xa=>ii(Val(t,x,x),xx=>app(app(ue(al(al(al(oldOrder))),x),xa),toOld(x,x,xa,xa,xx)))));
    const trans=qs(3,(x,y,z)=>ii(M(x,a),xa=>ii(M(y,a),ya=>ii(M(z,a),za=>ii(Val(t,x,y),xy=>ii(Val(t,y,z),yz=>
      toNew(x,z,xa,za,app(us(ar(al(al(oldOrder))),x,y,z),xa,ya,za,toOld(x,y,xa,ya,xy),toOld(y,z,ya,za,yz)))
    ))))));
    const total=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
      const goal=['|',Q(x,y),['|',Val(t,x,y),Val(t,y,x)]];
      return oe(app(us(ar(al(oldOrder)),x,y),xa,ya),goal,p=>ol(p,goal[2]),p=>oe(p,goal,
        xy=>or(goal[1],ol(toNew(x,y,xa,ya,xy),goal[2][2])),yx=>or(goal[1],or(goal[2][1],toNew(y,x,ya,xa,yx)))));
    })));
    const minima=ui(s=>ii(Sub(s,a),sa=>ii(E(x=>M(x,s)),sn=>
      open(app(ue(ar(oldOrder),s),sa,sn),(x,xp)=>{
        const bound=ui(y=>ii(M(y,s),ys=>ii(Val(t,y,x),yx=>app(app(ue(ar(xp),y),ys),
          toOld(y,x,app(ue(sa,y),ys),app(ue(sa,x),al(xp)),yx)))));
        return ei(E(x=>C(M(x,s),all(s,y=>N(Val(t,y,x))))),x,ai(al(xp),bound));
      })
    )));
    return ai(ai(ai(irr,trans),total),minima);
  }))));

  save('directed_union_capture',qs(3,(h,b,k)=>ii(UnionCarrier(h,b),union=>ii(CarrierFamily(h,k),carriers=>ii(Directed(h),directed=>
    qs(3,(x,y,z)=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>
      open(from(union,x,xb),(a,ap)=>open(ap,(r,rp)=>
        open(from(union,y,yb),(c,cp)=>open(cp,(s,sp)=>
          open(from(union,z,zb),(e,ep)=>open(ep,(v,vp)=>
            common(directed,a,r,c,s,al(rp),al(sp),(d,u,hd,ad,cd)=>
              common(directed,d,u,e,v,hd,al(vp),(f,q,hf,df,ef)=>{
                const fk=into(carriers,f,ei(E(q=>Val(h,f,q)),q,hf));
                const xf=app(ue(df,x),app(ue(ad,x),ar(rp))),yf=app(ue(df,y),app(ue(cd,y),ar(sp))),zf=app(ue(ef,z),ar(vp));
                return ei(E(f=>C(M(f,k),C(C(M(x,f),M(y,f)),M(z,f)))),f,ai(fk,ai(ai(xf,yf),zf)));
              })
            )
          ))
        ))
      ))
    ))))
  )))));
  save('union_local_well_orders',qs(4,(h,b,k,t)=>ii(UnionCarrier(h,b),union=>ii(CarrierFamily(h,k),carriers=>
    ii(Directed(h),directed=>ii(Extends(h),extension=>ii(Agreement(h,b,t),agreement=>ii(Local(h),local=>
      ui(a=>ii(M(a,k),ak=>open(from(carriers,a,ak),(r,stage)=>{
        const subset=app(us(imported(proofs.stage_is_subset_of_union),h,b,a,r),union,stage);
        const restriction=app(us(imported(proofs.union_order_restriction),h,b,t,a,r),union,directed,extension,agreement,stage);
        const order=app(us(imported(proofs.bounded_order_agreement_transfer),a,r,t),app(us(local,a,r),stage),restriction);
        return ai(subset,order);
      })))
    ))))))
  ));
  save('union_stages_initial',qs(4,(h,b,k,t)=>ii(UnionCarrier(h,b),union=>ii(CarrierFamily(h,k),carriers=>
    ii(Directed(h),directed=>ii(Extends(h),extension=>ii(Agreement(h,b,t),agreement=>
      ui(a=>ii(M(a,k),ak=>open(from(carriers,a,ak),(r,stage)=>
        app(us(imported(proofs.union_order_initial),h,b,t,a,r),union,directed,extension,agreement,stage)
      )))
    )))))
  ));
  save('union_order_well_order',qs(3,(h,b,t)=>ii(UnionCarrier(h,b),union=>ii(Directed(h),directed=>
    ii(Extends(h),extension=>ii(Agreement(h,b,t),agreement=>ii(Local(h),local=>
      open(ue(imported(proofs.carrier_family_exists),h),(k,carriers)=>{
        const capture=app(us(imported(proofs.directed_union_capture),h,b,k),union,carriers,directed);
        const orders=app(us(imported(proofs.union_local_well_orders),h,b,k,t),union,carriers,directed,extension,agreement,local);
        const initial=app(us(imported(proofs.union_stages_initial),h,b,k,t),union,carriers,directed,extension,agreement);
        return app(us(imported(old.proofs.directed_initial_segment_well_order),b,k,t),capture,orders,initial);
      })
    )))))
  ));

  save('limit_state_exists',ui(h=>open(ue(imported(proofs.union_carrier_exists),h),(b,union)=>
    open(us(imported(proofs.limit_relation_exists),h,b),(t,exact)=>{
      const goal=E(b=>E(t=>State(h,b,t)));
      return ei(goal,b,ei(inside(goal,b),t,ai(union,exact)));
    })
  )));
  save('limit_state_unique',qs(5,(h,b,t,c,s)=>ii(State(h,b,t),first=>ii(State(h,c,s),second=>{
    const carriers=app(us(imported(proofs.union_carrier_unique),h,b,c),al(first),al(second));
    const other=eqSub(sym(carriers),z=>Exact(h,z,s),ar(second));
    const orders=app(us(imported(proofs.limit_relation_unique),h,b,t,s),ar(first),other);
    return ai(carriers,sym(orders));
  }))));
  save('limit_state_well_order',qs(3,(h,b,t)=>ii(Local(h),local=>ii(Directed(h),directed=>ii(Extends(h),extension=>ii(State(h,b,t),state=>{
    const agreement=app(us(imported(proofs.limit_relation_agreement),h,b,t),ar(state));
    return app(us(imported(proofs.union_order_well_order),h,b,t),al(state),directed,extension,agreement,local);
  }))))));
  save('limit_state_extensions',qs(3,(h,b,t)=>ii(Directed(h),directed=>ii(Extends(h),extension=>ii(State(h,b,t),state=>{
    const agreement=app(us(imported(proofs.limit_relation_agreement),h,b,t),ar(state));
    return use(agreement,agree=>qs(2,(a,r)=>ii(Val(h,a,r),stage=>ai(
      app(us(imported(proofs.stage_is_subset_of_union),h,b,a,r),al(state),stage),ai(
        app(us(imported(proofs.union_order_restriction),h,b,t,a,r),al(state),directed,extension,agree,stage),
        app(us(imported(proofs.union_order_initial),h,b,t,a,r),al(state),directed,extension,agree,stage)
      )
    ))));
  })))));
  save('canonical_limit_complete',ui(h=>ii(Local(h),local=>ii(Directed(h),directed=>ii(Extends(h),extension=>
    open(ue(imported(proofs.limit_state_exists),h),(b,bp)=>open(bp,(t,state)=>{
      const order=app(us(imported(proofs.limit_state_well_order),h,b,t),local,directed,extension,state);
      const extensions=app(us(imported(proofs.limit_state_extensions),h,b,t),directed,extension,state);
      const goal=E(b=>E(t=>C(State(h,b,t),C(WO(b,t),AllExtensions(h,b,t)))));
      return ei(goal,b,ei(inside(goal,b),t,ai(state,ai(order,extensions))));
    }))
  )))));
  const finite=buildF(defs),pairUnique=buildE(defs,true).ordered_pair_unique;
  save('packed_limit_value_exists',ui(h=>
    open(ue(imported(proofs.limit_state_exists),h),(b,bp)=>open(bp,(t,state)=>
      open(us(imported(finite.pair_exists),b,t),(p,pair)=>{
        const goal=Value(h,p);
        return ei(E(p=>Value(h,p)),p,ei(goal,b,ei(inside(goal,b),t,ai(pair,state))));
      })
    ))
  ));
  save('packed_limit_value_unique',qs(3,(h,p,q)=>ii(Value(h,p),pv=>ii(Value(h,q),qv=>
    open(pv,(b,bp)=>open(bp,(t,tp)=>open(qv,(c,cp)=>open(cp,(s,sp)=>{
      const equal=app(us(imported(proofs.limit_state_unique),h,b,t,c,s),ar(tp),ar(sp));
      const fixCarrier=eqSub(sym(al(equal)),z=>Pair(q,z,s),al(sp));
      const fixed=eqSub(sym(ar(equal)),z=>Pair(q,b,z),fixCarrier);
      return app(us(imported(pairUnique),b,t,p,q),al(tp),fixed);
    }))))
  ))));
  return {proofs,formulas:forms};
}

export { canonicalLimitOrderFormulas, buildCanonicalLimitOrder };
