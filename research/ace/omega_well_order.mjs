// ACE-03W. Membership well-orders a supplied least inductive set.
// The proof uses the pinned Omega formula and the unchanged ZF kernel.
import { kernel, scoped } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`o${serial++}`;
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

// P has free-variable order [n, ...parameters]. Parameters precede w in
// the closed theorem. The successor step is guarded by n in w.
function buildOmegaInduction(defs,property,paramCount) {
  if(!Number.isSafeInteger(paramCount)||paramCount<0||paramCount>32||!scoped(property,paramCount+1,false))
    throw Error('omega induction property scope');
  const {M,I,C,A,E,named,ui,ii,al,ar,ai,ue,us,app,ei,open,separation,from,into,Empty,Succ,Omega,qs,compiled}=language(defs);
  const p=qs(paramCount,(...ps)=>ui(w=>{
    const at=n=>named(property,[n,...ps]);
    const base=A(z=>I(Empty(z),at(z)));
    const step=A(n=>A(d=>I(M(n,w),I(Succ(n,d),I(at(n),at(d))))));
    return ii(Omega(w),ow=>ii(base,bp=>ii(step,sp=>
      open(separation(w,ps,at),(c,cp)=>{
        const zero=open(al(al(ow)),(z,zp)=>{
          const zc=into(cp,z,ai(al(zp),app(ue(bp,z),ar(zp))));
          return ei(E(y=>C(M(y,c),Empty(y))),z,ai(zc,ar(zp)));
        });
        const next=ui(n=>ii(M(n,c),nc=>{
          const previous=from(cp,n,nc);
          return open(app(ue(ar(al(ow)),n),al(previous)),(d,dp)=>{
            const pd=app(us(sp,n,d),al(previous),ar(dp),ar(previous));
            return ei(E(y=>C(M(y,c),Succ(n,y))),d,ai(into(cp,d,ai(al(dp),pd)),ar(dp)));
          });
        }));
        const included=app(ue(ar(ow),c),ai(zero,next));
        return ui(n=>ii(M(n,w),nw=>ar(from(cp,n,app(ue(included,n),nw)))));
      })
    )));
  }));
  return compiled(p);
}

function buildOmegaWellOrder(defs) {
  const {fresh,M,Q,F,I,C,O,N,A,E,db,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled}=language(defs);
  const nonempty=s=>E(x=>M(x,s));
  const compare=(x,y)=>O(Q(x,y),O(M(x,y),M(y,x)));
  const irref=a=>all(a,x=>N(M(x,x)));
  const trans=a=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(M(x,y),I(M(y,z),M(x,z)))))))));
  const total=a=>A(x=>A(y=>I(M(x,a),I(M(y,a),compare(x,y)))));
  const minimum=(s,x)=>C(M(x,s),all(s,y=>N(M(y,x))));
  const minima=a=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,x)))));
  const WO=a=>C(C(C(irref(a),trans(a)),total(a)),minima(a));
  const decomposition=(w,n)=>O(Empty(n),some(w,k=>Succ(k,n)));
  const proofs={},save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const noSelf=buildF(defs,'relations').foundation_no_self;
  function induct(w,ow,ps,property,base,step) {
    const n=fresh(),instance=buildOmegaInduction(defs,db(property(n),[n,...ps]),ps.length);
    return app(us(imported(instance),...ps,w),ow,base,step);
  }
  function emptyEqual(a,b,ea,eb) {
    return app(us(ax({name:'extensionality'}),a,b),ui(x=>ai(
      ii(M(x,a),xa=>fe(app(ue(ea,x),xa),M(x,b))),
      ii(M(x,b),xb=>fe(app(ue(eb,x),xb),M(x,a))))));
  }
  function successorEqual(n,d,e,nd,ne) {
    return app(us(ax({name:'extensionality'}),d,e),ui(x=>ai(
      ii(M(x,d),xd=>into(ne,x,from(nd,x,xd))),
      ii(M(x,e),xe=>into(nd,x,from(ne,x,xe))))));
  }
  function inSuccessor(su,x,n,xn){return into(su,x,ol(xn,Q(x,n)));}
  function predecessorInSuccessor(su,n){return into(su,n,or(M(n,n),ref(n)));}

  save('successor_set_unique',qs(3,(n,d,e)=>ii(Succ(n,d),nd=>ii(Succ(n,e),ne=>successorEqual(n,d,e,nd,ne)))));
  save('omega_successor_exists',qs(2,(w,n)=>ii(Omega(w),ow=>ii(M(n,w),nw=>app(ue(ar(al(ow)),n),nw)))));
  save('omega_successor_membership',qs(3,(w,n,d)=>ii(Omega(w),ow=>ii(M(n,w),nw=>ii(Succ(n,d),nd=>
    open(app(ue(ar(al(ow)),n),nw),(e,ep)=>eqSub(successorEqual(n,e,d,ar(ep),nd),x=>M(x,w),al(ep)))
  )))));

  save('omega_transitive',ui(w=>ii(Omega(w),ow=>{
    const base=ui(z=>ii(Empty(z),ez=>ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),M(x,w))))));
    const step=qs(2,(n,d)=>ii(M(n,w),nw=>ii(Succ(n,d),nd=>ii(subset(n,w),sub=>
      ui(x=>ii(M(x,d),xd=>oe(from(nd,x,xd),M(x,w),xn=>app(ue(sub,x),xn),eq=>eqSub(sym(eq),y=>M(y,w),nw))))
    ))));
    return induct(w,ow,[w],n=>subset(n,w),base,step);
  })));

  save('omega_members_transitive',ui(w=>ii(Omega(w),ow=>{
    const base=ui(z=>ii(Empty(z),ez=>ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),subset(x,z))))));
    const step=qs(2,(n,d)=>ii(M(n,w),()=>ii(Succ(n,d),nd=>ii(Trans(n),tn=>
      ui(x=>ii(M(x,d),xd=>ui(y=>ii(M(y,x),yx=>
        oe(from(nd,x,xd),M(y,d),
          xn=>inSuccessor(nd,y,n,app(ue(app(ue(tn,x),xn),y),yx)),
          eq=>inSuccessor(nd,y,n,eqSub(eq,z=>M(y,z),yx)))
      ))))
    ))));
    return induct(w,ow,[],Trans,base,step);
  })));
  save('omega_member_transitive',qs(2,(w,n)=>ii(Omega(w),ow=>ii(M(n,w),nw=>
    app(ue(app(ue(imported(proofs.omega_members_transitive),w),ow),n),nw)
  ))));

  save('omega_zero_or_successor',ui(w=>ii(Omega(w),ow=>{
    const base=ui(z=>ii(Empty(z),ez=>ol(ez,decomposition(w,z)[2])));
    const step=qs(2,(n,d)=>ii(M(n,w),nw=>ii(Succ(n,d),nd=>ii(decomposition(w,n),()=>
      or(Empty(d),ei(decomposition(w,d)[2],n,ai(nw,nd)))
    ))));
    return induct(w,ow,[w],n=>decomposition(w,n),base,step);
  })));
  save('omega_nonempty_predecessor',qs(2,(w,n)=>ii(Omega(w),ow=>ii(M(n,w),nw=>ii(nonempty(n),ne=>{
    const decomp=app(ue(app(ue(imported(proofs.omega_zero_or_successor),w),ow),n),nw),goal=some(w,k=>Succ(k,n));
    return oe(decomp,goal,empty=>open(ne,(x,xn)=>fe(app(ue(empty,x),xn),goal)),p=>p);
  })))));

  save('omega_membership_irreflexive',use(imported(noSelf),ns=>ui(w=>ii(Omega(w),()=>
    ui(n=>ii(M(n,w),()=>ue(ns,n)))
  ))));
  save('omega_membership_transitive',ui(w=>ii(Omega(w),ow=>
    use(app(ue(imported(proofs.omega_members_transitive),w),ow),members=>
      qs(3,(x,y,z)=>ii(M(x,w),()=>ii(M(y,w),()=>ii(M(z,w),zw=>ii(M(x,y),xy=>ii(M(y,z),yz=>
        app(ue(app(ue(app(ue(members,z),zw),y),yz),x),xy)
      ))))))
    )
  )));

  // The double induction below proves trichotomy directly on the least
  // inductive set. Transitivity eliminates the one possible backward cycle.
  save('omega_membership_total',use(imported(noSelf),ns=>ui(w=>ii(Omega(w),ow=>{
    const allCompare=n=>all(w,m=>compare(n,m));
    const base=ui(z=>ii(Empty(z),ez=>{
      const mb=ui(q=>ii(Empty(q),eq=>ol(emptyEqual(z,q,ez,eq),compare(z,q)[2])));
      const ms=qs(2,(m,e)=>ii(M(m,w),()=>ii(Succ(m,e),me=>ii(compare(z,m),cmp=>{
        const goal=compare(z,e);
        return oe(cmp,goal,eq=>or(Q(z,e),ol(eqSub(sym(eq),x=>M(x,e),predecessorInSuccessor(me,m)),M(e,z))),
          rest=>oe(rest,goal,zm=>or(Q(z,e),ol(inSuccessor(me,z,m,zm),M(e,z))),
            mz=>fe(app(ue(ez,m),mz),goal)));
      }))));
      return induct(w,ow,[z],m=>compare(z,m),mb,ms);
    }));
    const step=qs(2,(n,d)=>ii(M(n,w),nw=>ii(Succ(n,d),nd=>ii(allCompare(n),previous=>{
      const mb=ui(z=>ii(Empty(z),ez=>{
        // An empty set belongs to w by comparison with its supplied zero.
        return open(al(al(ow)),(q,qp)=>{
          const zw=eqSub(emptyEqual(q,z,ar(qp),ez),x=>M(x,w),al(qp));
          const cmp=app(ue(previous,z),zw),goal=compare(d,z);
          return oe(cmp,goal,eq=>or(Q(d,z),or(M(d,z),eqSub(eq,x=>M(x,d),predecessorInSuccessor(nd,n)))),
            rest=>oe(rest,goal,nz=>fe(app(ue(ez,n),nz),goal),zn=>or(Q(d,z),or(M(d,z),inSuccessor(nd,z,n,zn)))));
        });
      }));
      const ms=qs(2,(m,e)=>ii(M(m,w),mw=>ii(Succ(m,e),me=>ii(compare(d,m),cmp=>{
        const goal=compare(d,e);
        return oe(cmp,goal,eq=>or(Q(d,e),ol(eqSub(sym(eq),x=>M(x,e),predecessorInSuccessor(me,m)),M(e,d))),
          rest=>oe(rest,goal,dm=>or(Q(d,e),ol(inSuccessor(me,d,m,dm),M(e,d))),md=>
            oe(from(nd,m,md),goal,mn=>{
              const ew=app(us(imported(proofs.omega_successor_membership),w,m,e),ow,mw,me);
              const outer=app(ue(previous,e),ew);
              return oe(outer,goal,eq=>or(Q(d,e),or(M(d,e),eqSub(eq,x=>M(x,d),predecessorInSuccessor(nd,n)))),
                rest=>oe(rest,goal,ne=>{
                  const tn=app(us(imported(proofs.omega_member_transitive),w,n),ow,nw);
                  return oe(from(me,n,ne),goal,nm=>fe(app(ue(ns,n),app(ue(app(ue(tn,m),mn),n),nm)),goal),
                    eq=>fe(app(ue(ns,n),eqSub(sym(eq),x=>M(x,n),mn)),goal));
                },en=>or(Q(d,e),or(M(d,e),inSuccessor(nd,e,n,en)))));
            },eq=>{
              const atN=eqSub(eq,x=>Succ(x,e),me);
              return ol(successorEqual(n,d,e,nd,atN),goal[2]);
            })
          ));
      }))));
      return induct(w,ow,[n,d],m=>compare(d,m),mb,ms);
    }))));
    const bounded=induct(w,ow,[w],allCompare,base,step);
    return qs(2,(x,y)=>ii(M(x,w),xw=>ii(M(y,w),yw=>app(ue(app(ue(bounded,x),xw),y),yw))));
  }))));

  save('omega_membership_minima',ui(w=>ii(Omega(w),()=>ui(s=>ii(subset(s,w),()=>ii(nonempty(s),ne=>
    open(app(ue(ax({name:'foundation'}),s),ne),(x,xp)=>
      ei(E(y=>minimum(s,y)),x,ai(al(xp),ui(y=>ii(M(y,s),ys=>ii(M(y,x),yx=>app(app(ue(ar(xp),y),yx),ys))))))
    )
  ))))));
  save('omega_membership_well_order',ui(w=>ii(Omega(w),ow=>ai(ai(ai(
    app(ue(imported(proofs.omega_membership_irreflexive),w),ow),
    app(ue(imported(proofs.omega_membership_transitive),w),ow)),
    app(ue(imported(proofs.omega_membership_total),w),ow)),
    app(ue(imported(proofs.omega_membership_minima),w),ow)
  ))));
  save('omega_ordinal',ui(w=>ii(Omega(w),ow=>ai(
    app(ue(imported(proofs.omega_transitive),w),ow),
    app(ue(imported(proofs.omega_members_transitive),w),ow)
  ))));
  return {proofs,formulas:{transitive:db(Trans('n'),['n']),membership_well_order:db(WO('w'),['w']),
    zero_or_successor:db(decomposition('w','n'),['w','n'])}};
}

export { buildOmegaInduction, buildOmegaWellOrder };
