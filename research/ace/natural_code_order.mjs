// ACE-03W. Canonical natural-number order and the exact triple instruction alphabet.
import { kernel } from './zf_interface.mjs';
import { buildOmegaWellOrder } from './omega_well_order.mjs';
import { buildPairProductOrder } from './pair_product_order.mjs';
import { buildRealization } from './relation_realization.mjs';
import { buildCanonicalRelation } from './canonical_relation.mjs';

function buildNaturalCodeOrder(defs) {
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
  const Omega=w=>named(defs.omega,[w]);
  const Product=(a,b,c)=>A(p=>iff(M(p,c),some(a,x=>some(b,y=>Pair(p,x,y)))));
  const Triple=(c,t,i,j)=>E(d=>C(Pair(d,i,j),Pair(c,t,d)));
  const TripleCarrier=(c,w)=>A(p=>iff(M(p,c),some(w,t=>some(w,i=>some(w,j=>Triple(p,t,i,j))))));
  const NatLt=(w,x,y)=>C(C(M(x,w),M(y,w)),M(x,y));
  const irref=(s,lt)=>all(s,x=>N(lt(x,x)));
  const trans=(s,lt)=>A(x=>A(y=>A(z=>I(M(x,s),I(M(y,s),I(M(z,s),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(s,lt)=>A(x=>A(y=>I(M(x,s),I(M(y,s),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minima=(s,lt)=>A(t=>I(all(t,x=>M(x,s)),I(E(x=>M(x,t)),E(x=>C(M(x,t),all(t,y=>N(lt(y,x))))))));
  const WO=(s,lt)=>C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));
  const W=(s,r)=>WO(s,(x,y)=>Val(r,x,y));
  const proofs={};
  const save=(id,p)=>{proofs[id]={goal:db(p.goal),proof:p.emit([],[])};};
  const omega=buildOmegaWellOrder(defs),products=buildPairProductOrder(defs);
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const bounded=(goal,x,m,p)=>ei(goal,x,ai(m,p));

  save('omega_guarded_well_order',ui(w=>ii(Omega(w),ow=>
    use(app(ue(imported(omega.proofs.omega_membership_well_order),w),ow),old=>{
      const irr=ui(x=>ii(M(x,w),xw=>ii(NatLt(w,x,x),xx=>app(app(ue(al(al(al(old))),x),xw),ar(xx)))));
      const tr=qs(3,(x,y,z)=>ii(M(x,w),xw=>ii(M(y,w),yw=>ii(M(z,w),zw=>
        ii(NatLt(w,x,y),xy=>ii(NatLt(w,y,z),yz=>
          ai(ai(xw,zw),app(us(ar(al(al(old))),x,y,z),xw,yw,zw,ar(xy),ar(yz)))))))));
      const tot=qs(2,(x,y)=>ii(M(x,w),xw=>ii(M(y,w),yw=>{
        const goal=O(Q(x,y),O(NatLt(w,x,y),NatLt(w,y,x)));
        return oe(app(us(ar(al(old)),x,y),xw,yw),goal,
          eq=>ol(eq,goal[2]),p=>oe(p,goal,
            xy=>or(Q(x,y),ol(ai(ai(xw,yw),xy),goal[2][2])),
            yx=>or(Q(x,y),or(goal[2][1],ai(ai(yw,xw),yx)))));
      })));
      const mins=ui(s=>ii(all(s,x=>M(x,w)),sw=>ii(E(x=>M(x,s)),ne=>
        open(app(ue(ar(old),s),sw,ne),(x,xp)=>
          ei(E(x=>C(M(x,s),all(s,y=>N(NatLt(w,y,x))))),x,
            ai(al(xp),ui(y=>ii(M(y,s),ys=>ii(NatLt(w,y,x),yx=>app(app(ue(ar(xp),y),ys),ar(yx)))))))
        )
      )));
      return ai(ai(ai(irr,tr),tot),mins);
    })
  )));
  const naturalFormula=db(NatLt('w','x','y'),['x','y','w']);
  const realization=buildRealization(defs,naturalFormula,1,0,proofs.omega_guarded_well_order);
  const canonical=buildCanonicalRelation(defs,naturalFormula,1,0,realization,proofs.omega_guarded_well_order);
  proofs.omega_canonical_relation=canonical.proofs.composed_canonical_well_order;
  save('omega_set_well_order_exists',ui(w=>ii(Omega(w),ow=>
    open(app(ue(imported(proofs.omega_canonical_relation),w),ow),(r,complete)=>
      ei(E(r=>W(w,r)),r,ar(al(complete))))
  )));

  save('nested_products_are_triple_carrier',qs(3,(w,p,c)=>ii(Product(w,w,p),pp=>ii(Product(w,p,c),cp=>
    ui(q=>ai(
      ii(M(q,c),qc=>open(from(cp,q,qc),(t,tp)=>open(ar(tp),(d,dp)=>
        open(from(pp,d,al(dp)),(i,ip)=>open(ar(ip),(j,jp)=>{
          const g=some(w,t=>some(w,i=>some(w,j=>Triple(q,t,i,j))));
          const gi=inside(g,t)[2],gj=inside(gi,i)[2],tr=inside(gj,j)[2];
          return bounded(g,t,al(tp),bounded(gi,i,al(ip),bounded(gj,j,al(jp),
            ei(tr,d,ai(ar(jp),ar(dp))))));
        }))
      ))),
      ii(some(w,t=>some(w,i=>some(w,j=>Triple(q,t,i,j)))),hit=>
        open(hit,(t,tp)=>open(ar(tp),(i,ip)=>open(ar(ip),(j,jp)=>open(ar(jp),(d,dp)=>{
          const pi=some(w,x=>some(w,y=>Pair(d,x,y))),pj=inside(pi,i)[2];
          const member=into(pp,d,bounded(pi,i,al(ip),bounded(pj,j,al(jp),al(dp))));
          const ct=some(w,x=>some(p,y=>Pair(q,x,y))),cd=inside(ct,t)[2];
          return into(cp,q,bounded(ct,t,al(tp),bounded(cd,d,member,ar(dp))));
        }))))
      )
    ))
  ))));
  save('natural_triple_well_order_exists',ui(w=>ii(Omega(w),ow=>
    open(app(ue(imported(proofs.omega_set_well_order_exists),w),ow),(rw,ww)=>
      use(imported(products.proofs.ordered_product_exists),product=>
        open(app(us(product,w,w,rw,rw),ww,ww),(p,pe)=>open(pe,(rp,pinfo)=>
          open(app(us(product,w,p,rw,rp),ww,ar(pinfo)),(c,ce)=>open(ce,(r,cinfo)=>{
            const exact=app(us(imported(proofs.nested_products_are_triple_carrier),w,p,c),al(pinfo),al(cinfo));
            const goal=E(c=>E(r=>C(TripleCarrier(c,w),W(c,r))));
            return ei(goal,c,ei(inside(goal,c),r,ai(exact,ar(cinfo))));
          }))
        ))
      )
    )
  )));
  return {proofs,formulas:{guarded_membership:naturalFormula,
    triple:db(Triple('c','t','i','j'),['c','t','i','j']),
    triple_carrier:db(TripleCarrier('c','w'),['c','w']),
    product:db(Product('a','b','c'),['a','b','c']),well_order:db(W('a','r'),['a','r'])}};
}

export {buildNaturalCodeOrder};
