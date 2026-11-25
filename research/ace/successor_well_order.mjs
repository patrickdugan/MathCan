// ACE-03T. Successor order by retaining old elements and appending new ones.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same } from './zf_interface.mjs';

function buildSuccessorWellOrder(defs) {
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

  const em=p=>dn(ii(N(O(p,N(p))),h=>app(h,or(p,ii(p,hp=>app(h,ol(hp,N(p))))))));
  const V=(r,x,y)=>named(defs.val,[r,x,y]);
  const subset=(s,a)=>A(x=>I(M(x,s),M(x,a)));
  const nonempty=s=>E(x=>M(x,s));
  const irref=(a,lt)=>A(x=>I(M(x,a),N(lt(x,x))));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),A(y=>I(M(y,s),N(lt(y,x)))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const T=(a,b,r,s,x,y)=>C(C(M(x,b),M(y,b)),O(
    C(C(M(x,a),M(y,a)),V(r,x,y)),
    O(C(M(x,a),N(M(y,a))),C(C(N(M(x,a)),N(M(y,a))),V(s,x,y)))
  ));
  function cases(p,g,oo,on,nn){return oe(ar(p),g,oo,q=>oe(q,g,on,nn));}
  function oldOld(a,b,r,s,x,y,xb,yb,xa,ya,xy){
    const g=T(a,b,r,s,x,y);
    return ai(ai(xb,yb),ol(ai(ai(xa,ya),xy),g[2][2]));
  }
  function oldNew(a,b,r,s,x,y,xb,yb,xa,ny){
    const g=T(a,b,r,s,x,y);
    return ai(ai(xb,yb),or(g[2][1],ol(ai(xa,ny),g[2][2][2])));
  }
  function newNew(a,b,r,s,x,y,xb,yb,nx,ny,xy){
    const g=T(a,b,r,s,x,y);
    return ai(ai(xb,yb),or(g[2][1],or(g[2][2][1],ai(ai(nx,ny),xy))));
  }
  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}
  function withOrders(fn){return ui(a=>ui(b=>ui(r=>ui(s=>ii(subset(a,b),ab=>ii(WO(a,(x,y)=>V(r,x,y)),wa=>ii(WO(b,(x,y)=>V(s,x,y)),wb=>fn(a,b,r,s,ab,wa,wb))))))));}

  save('successor_irreflexive',withOrders((a,b,r,s,ab,wa,wb)=>
    ui(x=>ii(M(x,b),xb=>ii(T(a,b,r,s,x,x),xx=>cases(xx,F,
      p=>app(app(ue(al(al(al(wa))),x),al(al(p))),ar(p)),
      p=>app(ar(p),al(p)),
      p=>app(app(ue(al(al(al(wb))),x),xb),ar(p))
    ))))
  ));

  save('successor_transitive',withOrders((a,b,r,s,ab,wa,wb)=>
    ui(x=>ui(y=>ui(z=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>ii(T(a,b,r,s,x,y),xy=>ii(T(a,b,r,s,y,z),yz=>{
      const goal=T(a,b,r,s,x,z);
      return cases(xy,goal,
        p=>cases(yz,goal,
          q=>oldOld(a,b,r,s,x,z,xb,zb,al(al(p)),ar(al(q)),app(us(ar(al(al(wa))),x,y,z),al(al(p)),ar(al(p)),ar(al(q)),ar(p),ar(q))),
          q=>oldNew(a,b,r,s,x,z,xb,zb,al(al(p)),ar(q)),
          q=>fe(app(al(al(q)),ar(al(p))),goal)),
        p=>cases(yz,goal,
          q=>fe(app(ar(p),al(al(q))),goal),
          q=>fe(app(ar(p),al(q)),goal),
          q=>oldNew(a,b,r,s,x,z,xb,zb,al(p),ar(al(q)))),
        p=>cases(yz,goal,
          q=>fe(app(ar(al(p)),al(al(q))),goal),
          q=>fe(app(ar(al(p)),al(q)),goal),
          q=>newNew(a,b,r,s,x,z,xb,zb,al(al(p)),ar(al(q)),app(us(ar(al(al(wb))),x,y,z),xb,yb,zb,ar(p),ar(q)))));
    }))))))))
  ));

  save('successor_total',withOrders((a,b,r,s,ab,wa,wb)=>
    ui(x=>ui(y=>ii(M(x,b),xb=>ii(M(y,b),yb=>{
      const xy=T(a,b,r,s,x,y),yx=T(a,b,r,s,y,x),goal=O(Q(x,y),O(xy,yx));
      return oe(em(M(x,a)),goal,xa=>oe(em(M(y,a)),goal,
        ya=>oe(app(us(ar(al(wa)),x,y),xa,ya),goal,
          eq=>ol(eq,O(xy,yx)),
          p=>oe(p,goal,
            rxy=>or(Q(x,y),ol(oldOld(a,b,r,s,x,y,xb,yb,xa,ya,rxy),yx)),
            ryx=>or(Q(x,y),or(xy,oldOld(a,b,r,s,y,x,yb,xb,ya,xa,ryx))))),
        ny=>or(Q(x,y),ol(oldNew(a,b,r,s,x,y,xb,yb,xa,ny),yx))),
      nx=>oe(em(M(y,a)),goal,
        ya=>or(Q(x,y),or(xy,oldNew(a,b,r,s,y,x,yb,xb,ya,nx))),
        ny=>oe(app(us(ar(al(wb)),x,y),xb,yb),goal,
          eq=>ol(eq,O(xy,yx)),
          p=>oe(p,goal,
            sxy=>or(Q(x,y),ol(newNew(a,b,r,s,x,y,xb,yb,nx,ny,sxy),yx)),
            syx=>or(Q(x,y),or(xy,newNew(a,b,r,s,y,x,yb,xb,ny,nx,syx)))))));
    }))))
  ));

  save('successor_minima',withOrders((a,b,r,s,ab,wa,wb)=>
    ui(v=>ii(subset(v,b),vb=>ii(nonempty(v),vn=>{
      const lt=(x,y)=>T(a,b,r,s,x,y),goal=E(m=>minimum(v,lt,m));
      const hasOld=E(x=>C(M(x,v),M(x,a)));
      return oe(em(hasOld),goal,old=>
        open(separation(v,[a],x=>M(x,a)),(t,tp)=>{
          const ta=ui(x=>ii(M(x,t),xt=>ar(from(tp,x,xt))));
          const tn=open(old,(x,xp)=>ei(nonempty(t),x,into(tp,x,xp)));
          return open(app(ue(ar(wa),t),ta,tn),(m,mp)=>{
            const members=from(tp,m,al(mp)),mv=al(members),ma=ar(members);
            const bound=ui(y=>ii(M(y,v),yv=>ii(lt(y,m),ym=>cases(ym,F,
              p=>app(app(ue(ar(mp),y),into(tp,y,ai(yv,al(al(p))))),ar(p)),
              p=>app(ar(p),ma),
              p=>app(ar(al(p)),ma)
            ))));
            return ei(goal,m,ai(mv,bound));
          });
        }),
      noOld=>open(app(ue(ar(wb),v),vb,vn),(m,mp)=>{
        const bound=ui(y=>ii(M(y,v),yv=>ii(lt(y,m),ym=>cases(ym,F,
          p=>app(noOld,ei(hasOld,y,ai(yv,al(al(p))))),
          p=>app(noOld,ei(hasOld,y,ai(yv,al(p)))),
          p=>app(app(ue(ar(mp),y),yv),ar(p))
        ))));
        return ei(goal,m,ai(al(mp),bound));
      }));
    })))
  ));

  save('successor_well_order',withOrders((a,b,r,s,ab,wa,wb)=>{
    const apply=name=>app(us(imported(proofs[name]),a,b,r,s),ab,wa,wb);
    return ai(ai(ai(apply('successor_irreflexive'),apply('successor_transitive')),apply('successor_total')),apply('successor_minima'));
  }));

  save('successor_restriction',ui(a=>ui(b=>ui(r=>ui(s=>ii(subset(a,b),ab=>
    ui(x=>ui(y=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
      const tx=T(a,b,r,s,x,y),rr=V(r,x,y);
      const left=ii(tx,t=>cases(t,rr,
        p=>ar(p),
        p=>fe(app(ar(p),ya),rr),
        p=>fe(app(ar(al(p)),ya),rr)));
      const right=ii(rr,rxy=>oldOld(a,b,r,s,x,y,app(ue(ab,x),xa),app(ue(ab,y),ya),xa,ya,rxy));
      return ai(left,right);
    }))))
  ))))));

  save('successor_initial_segment',ui(a=>ui(b=>ui(r=>ui(s=>
    ui(x=>ui(y=>ii(M(x,a),xa=>ii(M(y,b),()=>ii(T(a,b,r,s,y,x),yx=>cases(yx,M(y,a),
      p=>al(al(p)),p=>al(p),p=>fe(app(ar(al(p)),xa),M(y,a))
    ))))))
  )))));

  return {proofs,formulas:{
    successor_order:db(T('a','b','r','s','x','y'),['a','b','r','s','x','y']),
    well_order:db(WO('a',(x,y)=>V('r',x,y)),['a','r'])
  }};
}

export { buildSuccessorWellOrder };
