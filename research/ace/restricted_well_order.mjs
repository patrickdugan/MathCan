// ACE-03X. Restrict a carrier-relative well-order to an actual relation on a subset.
import {kernel} from './zf_interface.mjs';
import {buildF} from './finite_witnesses.mjs';

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

function restrictedLanguage(defs) {
  const l=language(defs),{M,Q,I,C,O,N,A,E,db,form,all,some,subset}=l;
  const Pair=(p,x,y)=>form('pair',p,x,y),Val=(r,x,y)=>form('val',r,x,y),iff=(p,q)=>C(I(p,q),I(q,p));
  const Support=(p,b)=>some(b,x=>some(b,y=>Pair(p,x,y)));
  const PairShape=(p,b)=>E(x=>E(y=>C(C(M(x,b),M(y,b)),Pair(p,x,y))));
  const Exact=(s,r,b)=>A(p=>iff(M(p,s),C(M(p,r),Support(p,b))));
  const PairOnly=(s,b)=>all(s,p=>PairShape(p,b));
  const Agreement=(s,r,b)=>A(x=>A(y=>iff(Val(s,x,y),C(C(M(x,b),M(y,b)),Val(r,x,y)))));
  const irref=(a,r)=>all(a,x=>N(Val(r,x,x)));
  const trans=(a,r)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(Val(r,x,y),I(Val(r,y,z),Val(r,x,z)))))))));
  const total=(a,r)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(Val(r,x,y),Val(r,y,x)))))));
  const minima=(a,r)=>A(d=>I(subset(d,a),I(E(x=>M(x,d)),E(x=>C(M(x,d),all(d,y=>N(Val(r,y,x))))))));
  const W=(a,r)=>C(C(C(irref(a,r),trans(a,r)),total(a,r)),minima(a,r));
  const formulas={
    exact_restriction:db(Exact('s','r','b'),['s','r','b']),
    pair_only:db(PairOnly('s','b'),['s','b']),pair_support:db(PairShape('p','b'),['p','b']),
    bounded_pair_support:db(Support('p','b'),['p','b']),
    guarded_agreement:db(Agreement('s','r','b'),['s','r','b']),
    well_order:db(W('a','r'),['a','r']),subset:db(subset('b','a'),['b','a'])
  };
  return {...l,Pair,Val,Support,PairShape,Exact,PairOnly,Agreement,W,formulas};
}

function restrictedWellOrderFormulas(defs) {return restrictedLanguage(defs).formulas;}

function buildRestrictedWellOrder(defs) {
  const {M,Q,C,O,N,A,E,replace,ui,ii,al,ar,ai,ue,us,app,ref,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,subset,qs,compiled,
    Pair,Val,Support,PairShape,Exact,PairOnly,Agreement,W,formulas}=restrictedLanguage(defs);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);return proofs[id];};
  const inner=(g,x)=>replace(g[2],g[1],x),finite=buildF(defs);
  const bounded=(goal,x,member,p)=>ei(goal,x,ai(member,p));
  function support(p,b,x,y,xb,yb,pair) {
    const goal=Support(p,b),afterX=inner(goal,x)[2];
    return bounded(goal,x,xb,bounded(afterX,y,yb,pair));
  }

  save('restriction_exact_exists',qs(2,(r,b)=>separation(r,[b],p=>Support(p,b))));
  save('restriction_exact_unique',qs(4,(s,t,r,b)=>ii(Exact(s,r,b),first=>ii(Exact(t,r,b),second=>
    app(us(ax({name:'extensionality'}),s,t),ui(p=>ai(
      ii(M(p,s),ps=>into(second,p,from(first,p,ps))),
      ii(M(p,t),pt=>into(first,p,from(second,p,pt)))
    )))
  ))));
  save('restriction_subset',qs(3,(s,r,b)=>ii(Exact(s,r,b),exact=>ui(p=>ii(M(p,s),ps=>al(from(exact,p,ps)))))));
  save('restriction_pair_only',qs(3,(s,r,b)=>ii(Exact(s,r,b),exact=>ui(p=>ii(M(p,s),ps=>
    open(ar(from(exact,p,ps)),(x,xp)=>open(ar(xp),(y,yp)=>{
      const goal=PairShape(p,b);
      return ei(goal,x,ei(inner(goal,x),y,ai(ai(al(xp),al(yp)),ar(yp))));
    }))
  )))));

  save('restriction_value_agreement',qs(3,(s,r,b)=>ii(Exact(s,r,b),exact=>qs(2,(x,y)=>ai(
    ii(Val(s,x,y),value=>open(value,(p,pp)=>use(from(exact,p,al(pp)),fact=>
      open(ar(fact),(u,up)=>open(ar(up),(v,vp)=>
        use(app(us(imported(finite.pair_injective),p,x,y,u,v),ar(pp),ar(vp)),coordinates=>{
          const xb=eqSub(sym(al(coordinates)),z=>M(z,b),al(up));
          const yb=eqSub(sym(ar(coordinates)),z=>M(z,b),al(vp));
          const old=ei(Val(r,x,y),p,ai(al(fact),ar(pp)));
          return ai(ai(xb,yb),old);
        })
      ))
    ))),
    ii(C(C(M(x,b),M(y,b)),Val(r,x,y)),fact=>open(ar(fact),(p,pp)=>{
      const supported=support(p,b,x,y,al(al(fact)),ar(al(fact)),ar(pp));
      const member=into(exact,p,ai(al(pp),supported));
      return ei(Val(s,x,y),p,ai(member,ar(pp)));
    }))
  )))));

  save('restriction_preserves_well_order',qs(4,(a,r,b,s)=>ii(subset(b,a),ba=>ii(W(a,r),order=>ii(Exact(s,r,b),exact=>
    use(app(us(imported(proofs.restriction_value_agreement),s,r,b),exact),agreement=>{
      const inA=(x,xb)=>app(ue(ba,x),xb);
      const old=(x,y,p)=>ar(app(al(us(agreement,x,y)),p));
      const restricted=(x,y,xb,yb,p)=>app(ar(us(agreement,x,y)),ai(ai(xb,yb),p));
      const irr=ui(x=>ii(M(x,b),xb=>ii(Val(s,x,x),xx=>app(app(ue(al(al(al(order))),x),inA(x,xb)),old(x,x,xx)))));
      const tr=qs(3,(x,y,z)=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>ii(Val(s,x,y),xy=>ii(Val(s,y,z),yz=>
        restricted(x,z,xb,zb,app(us(ar(al(al(order))),x,y,z),inA(x,xb),inA(y,yb),inA(z,zb),old(x,y,xy),old(y,z,yz)))
      ))))));
      const tot=qs(2,(x,y)=>ii(M(x,b),xb=>ii(M(y,b),yb=>{
        const goal=O(Q(x,y),O(Val(s,x,y),Val(s,y,x)));
        return oe(app(us(ar(al(order)),x,y),inA(x,xb),inA(y,yb)),goal,
          eq=>ol(eq,goal[2]),rest=>oe(rest,goal,
            xy=>or(Q(x,y),ol(restricted(x,y,xb,yb,xy),Val(s,y,x))),
            yx=>or(Q(x,y),or(Val(s,x,y),restricted(y,x,yb,xb,yx)))
          )
        );
      })));
      const mins=ui(d=>ii(subset(d,b),db=>ii(E(x=>M(x,d)),nonempty=>{
        const da=ui(x=>ii(M(x,d),xd=>inA(x,app(ue(db,x),xd))));
        return open(app(ue(ar(order),d),da,nonempty),(x,xp)=>{
          const goal=E(x=>C(M(x,d),A(y=>['>',M(y,d),N(Val(s,y,x))])));
          const least=ui(y=>ii(M(y,d),yd=>ii(Val(s,y,x),yx=>app(app(ue(ar(xp),y),yd),old(y,x,yx)))));
          return ei(goal,x,ai(al(xp),least));
        });
      })));
      return ai(ai(ai(irr,tr),tot),mins);
    })
  )))));

  save('restricted_well_order_exists',qs(3,(a,r,b)=>ii(subset(b,a),ba=>ii(W(a,r),order=>
    open(us(imported(proofs.restriction_exact_exists),r,b),(s,exact)=>{
      const wellOrdered=app(us(imported(proofs.restriction_preserves_well_order),a,r,b,s),ba,order,exact);
      const pairOnly=app(us(imported(proofs.restriction_pair_only),s,r,b),exact);
      return ei(E(s=>C(Exact(s,r,b),C(W(b,s),PairOnly(s,b)))),s,ai(exact,ai(wellOrdered,pairOnly)));
    })
  ))));
  return {formulas,proofs};
}

export {restrictedWellOrderFormulas,buildRestrictedWellOrder};

