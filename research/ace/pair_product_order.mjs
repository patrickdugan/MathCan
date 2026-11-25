// ACE-03W. Exact Cartesian-product carriers and their canonical lexicographic orders.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildLexicographicPullback, pairLexicographicSpecification } from './lexicographic_pullback.mjs';
import { buildRealization } from './relation_realization.mjs';
import { buildCanonicalRelation } from './canonical_relation.mjs';

function buildPairProductOrder(defs) {
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


  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const Pair=(p,a,b)=>named(defs.pair,[p,a,b]),Val=(r,x,y)=>named(defs.val,[r,x,y]);
  const Product=(a,b,c)=>A(p=>iff(M(p,c),some(a,x=>some(b,y=>Pair(p,x,y)))));
  const irref=(s,lt)=>all(s,x=>N(lt(x,x)));
  const trans=(s,lt)=>A(x=>A(y=>A(z=>I(M(x,s),I(M(y,s),I(M(z,s),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(s,lt)=>A(x=>A(y=>I(M(x,s),I(M(y,s),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minima=(s,lt)=>A(t=>I(all(t,x=>M(x,s)),I(E(x=>M(x,t)),E(x=>C(M(x,t),all(t,y=>N(lt(y,x))))))));
  const WO=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const W=(s,r)=>WO(s,(x,y)=>Val(r,x,y));
  const pairSpec=pairLexicographicSpecification(defs),lex=buildLexicographicPullback(defs,pairSpec);
  const Cover=(a,b,c)=>named(lex.formulas.cover,[a,b,c,a,b]);
  const Func=c=>named(lex.formulas.functional,[c,c,c,c,c]);
  const Inj=c=>named(lex.formulas.injective,[c,c,c,c,c]);
  const Lex=(a,b,c,r,s,p,q)=>named(lex.formulas.lexicographic,[p,q,a,b,c,r,s]);
  const proofs={};
  const save=(id,p)=>{proofs[id]={goal:db(p.goal),proof:p.emit([],[])};};
  const finite=buildF(defs),earlier=buildE(defs,true);
  const realization=buildRealization(defs,lex.formulas.lexicographic,5,2,lex.proofs.lexicographic_well_order);
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const boundedWitness=(goal,x,m,p)=>ei(goal,x,ai(m,p));
  function unionIn(union,x,y,ys,xy){
    const target=ue(union,x).goal[2][1];
    return into(union,x,ei(target,y,ai(ys,xy)));
  }

  save('pair_product_exists',qs(2,(a,b)=>
    use(imported(realization.proofs.ordered_pair_double_power_bound),bound=>
      open(us(ax({name:'pairing'}),a,b),(ab,abp)=>open(ue(ax({name:'union'}),ab),(base,bp)=>
        open(ue(ax({name:'power'}),base),(p1,pow1)=>open(ue(ax({name:'power'}),p1),(p2,pow2)=>{
          const pred=p=>some(a,x=>some(b,y=>Pair(p,x,y)));
          return open(separation(p2,[a,b],pred),(c,cp)=>{
            const exact=ui(p=>ai(
              ii(M(p,c),pc=>ar(from(cp,p,pc))),
              ii(pred(p),hit=>open(hit,(x,xp)=>open(ar(xp),(y,yp)=>{
                const aab=into(abp,a,ol(ref(a),Q(a,b))),bab=into(abp,b,or(Q(b,a),ref(b)));
                const xb=unionIn(bp,x,a,aab,al(xp)),yb=unionIn(bp,y,b,bab,al(yp));
                const limit=app(us(bound,base,p1,p2,p,x,y),pow1,pow2,xb,yb,ar(yp));
                return into(cp,p,ai(limit,hit));
              })))
            ));
            return ei(E(c=>Product(a,b,c)),c,exact);
          });
        }))
      ))
    )
  ));
  save('pair_product_unique',qs(4,(a,b,c,d)=>ii(Product(a,b,c),pc=>ii(Product(a,b,d),pd=>
    app(us(ax({name:'extensionality'}),c,d),ui(p=>ai(
      ii(M(p,c),mc=>into(pd,p,from(pc,p,mc))),
      ii(M(p,d),md=>into(pc,p,from(pd,p,md)))
    )))
  ))));
  save('pair_product_covers',qs(3,(a,b,c)=>ii(Product(a,b,c),product=>
    ui(p=>ii(M(p,c),pc=>from(product,p,pc)))
  )));
  save('pair_product_coordinate_functionality',ui(c=>
    use(imported(finite.pair_injective),inj=>qs(5,(p,a,b,d,e)=>
      ii(M(p,c),_=>ii(Pair(p,a,b),pab=>ii(Pair(p,d,e),pde=>app(us(inj,p,a,b,d,e),pab,pde))))
    ))
  ));
  save('pair_product_joint_injection',ui(c=>
    use(imported(earlier.ordered_pair_unique),unique=>qs(4,(p,q,a,b)=>
      ii(M(p,c),_=>ii(M(q,c),_=>ii(Pair(p,a,b),pab=>ii(Pair(q,a,b),qab=>app(us(unique,a,b,p,q),pab,qab)))))
    ))
  ));
  save('pair_product_lexicographic_well_order',qs(5,(a,b,c,r,s)=>ii(W(a,r),wa=>ii(W(b,s),wb=>ii(Product(a,b,c),product=>{
    const cover=app(us(imported(proofs.pair_product_covers),a,b,c),product);
    const functional=ue(imported(proofs.pair_product_coordinate_functionality),c);
    const injective=ue(imported(proofs.pair_product_joint_injection),c);
    return app(us(imported(lex.proofs.lexicographic_well_order),a,b,c,r,s),wa,wb,cover,functional,injective);
  })))));

  const canonical=buildCanonicalRelation(defs,lex.formulas.lexicographic,5,2,realization,proofs.pair_product_lexicographic_well_order);
  proofs.pair_product_canonical_well_order=canonical.proofs.composed_canonical_well_order;
  save('ordered_product_exists',qs(4,(a,b,r,s)=>ii(W(a,r),wa=>ii(W(b,s),wb=>
    open(us(imported(proofs.pair_product_exists),a,b),(c,product)=>
      open(app(us(imported(proofs.pair_product_canonical_well_order),a,b,c,r,s),wa,wb,product),(t,complete)=>{
        const goal=E(c=>E(t=>C(Product(a,b,c),W(c,t))));
        return ei(goal,c,ei(inside(goal,c),t,ai(product,ar(al(complete)))));
      })
    )
  ))));
  return {proofs,formulas:{product:db(Product('a','b','c'),['a','b','c']),
    cover:db(Cover('a','b','c'),['a','b','c']),
    coordinate_functionality:db(Func('c'),['c']),joint_injection:db(Inj('c'),['c']),
    lexicographic:lex.formulas.lexicographic,well_order:db(W('a','r'),['a','r'])},spec:pairSpec};
}

export {buildPairProductOrder};
