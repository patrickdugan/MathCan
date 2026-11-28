// ACE-03T. Actual set realization of the induced and successor order predicates.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same, scoped } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildWellOrder } from './constructible_well_order.mjs';
import { buildSuccessorWellOrder } from './successor_well_order.mjs';

function buildRealization(defs, formula, paramCount, carrierIndex, previous) {
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
     !scoped(formula,paramCount+2,false))throw Error('realization formula scope');
  if(!same(formula.slice(0,2),['&',['&',['M',0,carrierIndex+2],['M',1,carrierIndex+2]]]))
    throw Error('explicit carrier guards required');
  const V=(r,x,y)=>named(defs.val,[r,x,y]);
  const Pair=(p,x,y)=>named(defs.pair,[p,x,y]);
  const subset=(s,a)=>A(x=>I(M(x,s),M(x,a)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const Power=(b,p)=>A(z=>B(M(z,p),subset(z,b)));
  const irref=(a,lt)=>A(x=>I(M(x,a),N(lt(x,x))));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),A(y=>I(M(y,s),N(lt(y,x)))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(E(x=>M(x,s)),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const quant=(n,fn,xs=[])=>xs.length===n?fn(...xs):ui(x=>quant(n,fn,[...xs,x]));
  const Phi=(ps,x,y)=>named(formula,[x,y,...ps]);
  const Agreement=(ps,r)=>A(x=>A(y=>B(V(r,x,y),Phi(ps,x,y))));
  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  const finite=buildF(defs);
  // These are existing complete proof trees; their assumptions are empty.
  proofs.ordered_pair_exists=finite.pair_exists;
  proofs.ordered_pair_injective=finite.pair_injective;

  // Every Kuratowski pair of elements of b lies in P(P(b)). This bound is
  // proved here and then discharged using two actual Power Set instances.
  save('ordered_pair_double_power_bound',quant(6,(b,p1,p2,p,x,y)=>
    ii(Power(b,p1),pow1=>ii(Power(p1,p2),pow2=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(Pair(p,x,y),pair=>
      open(pair,(u,up)=>open(up,(v,vp)=>{
        const single=al(al(vp)),double=ar(al(vp)),outer=ar(vp);
        const u1=into(pow1,u,ui(z=>ii(M(z,u),zu=>eqSub(sym(from(single,z,zu)),t=>M(t,b),xb))));
        const v1=into(pow1,v,ui(z=>ii(M(z,v),zv=>oe(from(double,z,zv),M(z,b),
          zx=>eqSub(sym(zx),t=>M(t,b),xb),zy=>eqSub(sym(zy),t=>M(t,b),yb)))));
        return into(pow2,p,ui(z=>ii(M(z,p),zp=>oe(from(outer,z,zp),M(z,p1),
          zu=>eqSub(sym(zu),t=>M(t,p1),u1),zv=>eqSub(sym(zv),t=>M(t,p1),v1)))));
      }))
    )))))
  ));

  save('exact_relation_realization',quant(paramCount,(...ps)=>{
    const b=ps[carrierIndex],goal=E(r=>Agreement(ps,r));
    return use(imported(proofs.ordered_pair_exists),pairExists=>use(imported(proofs.ordered_pair_injective),pairInjective=>
      use(imported(proofs.ordered_pair_double_power_bound),pairBound=>
        open(ue(ax({name:'power'}),b),(p1,pow1)=>open(ue(ax({name:'power'}),p1),(p2,pow2)=>{
          const predicate=p=>E(x=>E(y=>C(Pair(p,x,y),Phi(ps,x,y))));
          return open(separation(p2,ps,predicate),(r,rp)=>{
            const agree=ui(x=>ui(y=>{
              const phi=Phi(ps,x,y);
              const forward=ii(V(r,x,y),val=>open(val,(p,pv)=>
                open(ar(from(rp,p,al(pv))),(u,up)=>open(up,(v,vp)=>{
                  const eq=app(us(pairInjective,p,x,y,u,v),ar(pv),al(vp));
                  const atX=eqSub(sym(al(eq)),z=>Phi(ps,z,v),ar(vp));
                  return eqSub(sym(ar(eq)),z=>Phi(ps,x,z),atX);
                }))
              ));
              const backward=ii(phi,xy=>open(us(pairExists,x,y),(p,pair)=>{
                const guards=al(xy),pBound=app(us(pairBound,b,p1,p2,p,x,y),pow1,pow2,al(guards),ar(guards),pair);
                const pred=predicate(p),inner=replace(pred[2],pred[1],x);
                const hit=ei(pred,x,ei(inner,y,ai(pair,xy)));
                const pr=into(rp,p,ai(pBound,hit));
                return ei(V(r,x,y),p,ai(pr,pair));
              }));
              return ai(forward,backward);
            }));
            return ei(goal,r,agree);
          });
        }))
      )
    ));
  }));

  // Exact pointwise agreement transports all four clauses of a well-order.
  // The formula may be arbitrarily quantified; no absoluteness is assumed.
  save('well_order_agreement_transfer',quant(paramCount,(...ps)=>ui(r=>ii(Agreement(ps,r),agree=>
    ii(WO(ps[carrierIndex],(x,y)=>Phi(ps,x,y)),old=>{
      const b=ps[carrierIndex],lt=(x,y)=>V(r,x,y);
      const toPhi=(x,y,p)=>app(al(us(agree,x,y)),p);
      const toVal=(x,y,p)=>app(ar(us(agree,x,y)),p);
      const irr=ui(x=>ii(M(x,b),xb=>ii(lt(x,x),xx=>app(app(ue(al(al(al(old))),x),xb),toPhi(x,x,xx)))));
      const tr=ui(x=>ui(y=>ui(z=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>ii(lt(x,y),xy=>ii(lt(y,z),yz=>
        toVal(x,z,app(us(ar(al(al(old))),x,y,z),xb,yb,zb,toPhi(x,y,xy),toPhi(y,z,yz)))
      ))))))));
      const tot=ui(x=>ui(y=>ii(M(x,b),xb=>ii(M(y,b),yb=>{
        const goal=O(Q(x,y),O(lt(x,y),lt(y,x)));
        return oe(app(us(ar(al(old)),x,y),xb,yb),goal,
          eq=>ol(eq,goal[2]),p=>oe(p,goal,
            xy=>or(Q(x,y),ol(toVal(x,y,xy),lt(y,x))),
            yx=>or(Q(x,y),or(lt(x,y),toVal(y,x,yx)))));
      }))));
      const mins=ui(s=>ii(subset(s,b),sb=>ii(E(x=>M(x,s)),sn=>
        open(app(ue(ar(old),s),sb,sn),(m,mp)=>{
          const goal=E(x=>minimum(s,lt,x));
          const bound=ui(y=>ii(M(y,s),ys=>ii(lt(y,m),ym=>app(app(ue(ar(mp),y),ys),toPhi(y,m,ym)))));
          return ei(goal,m,ai(al(mp),bound));
        })
      )));
      return ai(ai(ai(irr,tr),tot),mins);
    })
  ))));

  save('well_order_set_realization',quant(paramCount,(...ps)=>ii(WO(ps[carrierIndex],(x,y)=>Phi(ps,x,y)),old=>
    open(us(imported(proofs.exact_relation_realization),...ps),(r,agree)=>{
      const newOrder=app(ue(us(imported(proofs.well_order_agreement_transfer),...ps),r),agree,old);
      const goal=E(r=>C(Agreement(ps,r),WO(ps[carrierIndex],(x,y)=>V(r,x,y))));
      return ei(goal,r,ai(agree,newOrder));
    })
  )));

  // Compose with the already checked code-order or successor theorem,
  // retaining its original hypotheses in exactly their original order.
  if(previous) {
    save('composed_well_order_realization',quant(paramCount,(...ps)=>{
      const before=us(imported(previous),...ps);
      function take(p) {
        if(p.goal[0]==='>')return ii(p.goal[1],h=>take(app(p,h)));
        const expected=WO(ps[carrierIndex],(x,y)=>Phi(ps,x,y));
        if(!same(db(p.goal,ps.slice().reverse()),db(expected,ps.slice().reverse())))throw Error('composition well-order mismatch');
        return app(us(imported(proofs.well_order_set_realization),...ps),p);
      }
      return take(before);
    }));
  }

  return {proofs,formula,paramCount,carrierIndex};
}

function reindex(p,indices,d=0) {
  const [op,a,b]=p;
  if(op==='F')return p;
  if(op==='A'||op==='E')return [op,reindex(a,indices,d+1)];
  if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
  return [op,reindex(a,indices,d),reindex(b,indices,d)];
}

function buildOrderRealizations(defs) {
  const least=buildWellOrder(defs),successor=buildSuccessorWellOrder(defs);
  return {
    induced:buildRealization(defs,reindex(least.formulas.induced,[2,3,4,5,0,1]),4,1,least.proofs.induced_well_order),
    successor:buildRealization(defs,reindex(successor.formulas.successor_order,[2,3,4,5,0,1]),4,1,successor.proofs.successor_well_order)
  };
}

export { buildRealization, buildOrderRealizations };
