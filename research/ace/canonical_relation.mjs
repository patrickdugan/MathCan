// ACE-03U. Canonical relation sets with exact membership and uniqueness.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same, scoped } from './zf_interface.mjs';
import { buildOrderRealizations } from './relation_realization.mjs';
import { buildWellOrder } from './constructible_well_order.mjs';
import { buildSuccessorWellOrder } from './successor_well_order.mjs';

function buildCanonicalRelation(defs, formula, paramCount, carrierIndex, prior, previousOrder) {
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

  if(!Number.isSafeInteger(paramCount)||paramCount<1||paramCount>32||
     !Number.isSafeInteger(carrierIndex)||carrierIndex<0||carrierIndex>=paramCount||
     !scoped(formula,paramCount+2,false))throw Error('canonical formula scope');
  if(!same(formula.slice(0,2),['&',['&',['M',0,carrierIndex+2],['M',1,carrierIndex+2]]]))
    throw Error('canonical carrier guards required');
  const V=(r,x,y)=>named(defs.val,[r,x,y]);
  const Pair=(p,x,y)=>named(defs.pair,[p,x,y]);
  const subset=(s,a)=>A(x=>I(M(x,s),M(x,a)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const irref=(a,lt)=>A(x=>I(M(x,a),N(lt(x,x))));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),A(y=>I(M(y,s),N(lt(y,x)))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(E(x=>M(x,s)),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const quant=(n,fn,xs=[])=>xs.length===n?fn(...xs):ui(x=>quant(n,fn,[...xs,x]));
  const Phi=(ps,x,y)=>named(formula,[x,y,...ps]);
  const PairPredicate=(ps,p)=>E(x=>E(y=>C(Pair(p,x,y),Phi(ps,x,y))));
  const Exact=(ps,r)=>A(p=>B(M(p,r),PairPredicate(ps,p)));
  const PairOnly=(b,r)=>A(p=>I(M(p,r),E(x=>E(y=>C(C(M(x,b),M(y,b)),Pair(p,x,y))))));
  const Agreement=(ps,r)=>A(x=>A(y=>B(V(r,x,y),Phi(ps,x,y))));
  const Unique=(ps,r)=>A(s=>I(Exact(ps,s),Q(s,r)));
  const Complete=(ps,r)=>C(C(C(Exact(ps,r),Agreement(ps,r)),WO(ps[carrierIndex],(x,y)=>V(r,x,y))),Unique(ps,r));
  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  // The exact membership contract rules out every non-pair object and
  // every pair whose coordinates fail the supplied predicate.
  save('exact_membership_exists',quant(paramCount,(...ps)=>{
    const b=ps[carrierIndex],goal=E(r=>Exact(ps,r));
    return use(imported(prior.proofs.ordered_pair_double_power_bound),pairBound=>
      open(ue(ax({name:'power'}),b),(p1,pow1)=>open(ue(ax({name:'power'}),p1),(p2,pow2)=>
        open(separation(p2,ps,p=>PairPredicate(ps,p)),(r,rp)=>{
          const exact=ui(p=>{
            const forward=ii(M(p,r),pr=>ar(from(rp,p,pr)));
            const backward=ii(PairPredicate(ps,p),hit=>open(hit,(x,xp)=>open(xp,(y,yp)=>{
              const pair=al(yp),phi=ar(yp),guards=al(phi);
              const bound=app(us(pairBound,b,p1,p2,p,x,y),pow1,pow2,al(guards),ar(guards),pair);
              const pred=PairPredicate(ps,p),inner=replace(pred[2],pred[1],x);
              const witness=ei(pred,x,ei(inner,y,ai(pair,phi)));
              return into(rp,p,ai(bound,witness));
            })));
            return ai(forward,backward);
          });
          return ei(goal,r,exact);
        })
      ))
    );
  }));

  save('exact_membership_unique',quant(paramCount,(...ps)=>ui(r=>ui(s=>ii(Exact(ps,r),rr=>ii(Exact(ps,s),ss=>
    app(us(ax({name:'extensionality'}),s,r),ui(p=>ai(
      ii(M(p,s),sp=>into(rr,p,from(ss,p,sp))),
      ii(M(p,r),rp=>into(ss,p,from(rr,p,rp)))
    )))
  ))))));

  save('exact_membership_pair_only',quant(paramCount,(...ps)=>ui(r=>ii(Exact(ps,r),exact=>
    ui(p=>ii(M(p,r),pr=>{
      const goal=E(x=>E(y=>C(C(M(x,ps[carrierIndex]),M(y,ps[carrierIndex])),Pair(p,x,y))));
      return open(from(exact,p,pr),(x,xp)=>open(xp,(y,yp)=>{
        const inner=replace(goal[2],goal[1],x),guards=al(ar(yp));
        return ei(goal,x,ei(inner,y,ai(guards,al(yp))));
      }));
    }))
  ))));

  save('exact_membership_implies_agreement',quant(paramCount,(...ps)=>ui(r=>ii(Exact(ps,r),exact=>
    use(imported(prior.proofs.ordered_pair_exists),exists=>use(imported(prior.proofs.ordered_pair_injective),inj=>
      ui(x=>ui(y=>{
        const forward=ii(V(r,x,y),val=>open(val,(p,pv)=>
          open(from(exact,p,al(pv)),(u,up)=>open(up,(v,vp)=>{
            const equal=app(us(inj,p,x,y,u,v),ar(pv),al(vp));
            const atX=eqSub(sym(al(equal)),z=>Phi(ps,z,v),ar(vp));
            return eqSub(sym(ar(equal)),z=>Phi(ps,x,z),atX);
          }))
        ));
        const backward=ii(Phi(ps,x,y),phi=>open(us(exists,x,y),(p,pair)=>{
          const pred=PairPredicate(ps,p),inner=replace(pred[2],pred[1],x);
          const witness=ei(pred,x,ei(inner,y,ai(pair,phi)));
          return ei(V(r,x,y),p,ai(into(exact,p,witness),pair));
        }));
        return ai(forward,backward);
      }))
    ))
  ))));

  save('canonical_unique_relation',quant(paramCount,(...ps)=>
    open(us(imported(proofs.exact_membership_exists),...ps),(r,exact)=>{
      const unique=ui(s=>ii(Exact(ps,s),other=>app(us(imported(proofs.exact_membership_unique),...ps,r,s),exact,other)));
      const goal=E(r=>C(Exact(ps,r),Unique(ps,r)));
      return ei(goal,r,ai(exact,unique));
    })
  ));

  save('canonical_well_order_realization',quant(paramCount,(...ps)=>ii(WO(ps[carrierIndex],(x,y)=>Phi(ps,x,y)),wo=>
    open(us(imported(proofs.canonical_unique_relation),...ps),(r,cp)=>{
      const exact=al(cp),unique=ar(cp);
      const agreement=app(us(imported(proofs.exact_membership_implies_agreement),...ps,r),exact);
      return use(agreement,agree=>{
        const transferred=app(us(imported(prior.proofs.well_order_agreement_transfer),...ps,r),agree,wo);
        return ei(E(r=>Complete(ps,r)),r,ai(ai(ai(exact,agree),transferred),unique));
      });
    })
  )));

  save('composed_canonical_well_order',quant(paramCount,(...ps)=>{
    const before=us(imported(previousOrder),...ps);
    function take(p) {
      if(p.goal[0]==='>')return ii(p.goal[1],h=>take(app(p,h)));
      const expected=WO(ps[carrierIndex],(x,y)=>Phi(ps,x,y));
      if(!same(db(p.goal,ps.slice().reverse()),db(expected,ps.slice().reverse())))throw Error('canonical composition mismatch');
      return app(us(imported(proofs.canonical_well_order_realization),...ps),p);
    }
    return take(before);
  }));

  return {proofs,formula,paramCount,carrierIndex};
}

function buildCanonicalRelations(defs) {
  const prior=buildOrderRealizations(defs),least=buildWellOrder(defs),successor=buildSuccessorWellOrder(defs);
  return {
    induced:buildCanonicalRelation(defs,prior.induced.formula,4,1,prior.induced,least.proofs.induced_well_order),
    successor:buildCanonicalRelation(defs,prior.successor.formula,4,1,prior.successor,successor.proofs.successor_well_order)
  };
}

export { buildCanonicalRelation, buildCanonicalRelations };
