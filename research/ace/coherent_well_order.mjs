// ACE-03T. Directed initial-segment limit transfer for a set-coded order.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same } from './zf_interface.mjs';

function buildCoherentWellOrder(defs) {
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

  const V=(r,x,y)=>named(defs.val,[r,x,y]);
  const subset=(s,a)=>A(x=>I(M(x,s),M(x,a)));
  const nonempty=s=>E(x=>M(x,s));
  const irref=(a,r)=>A(x=>I(M(x,a),N(V(r,x,x))));
  const trans=(a,r)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(V(r,x,y),I(V(r,y,z),V(r,x,z)))))))));
  const total=(a,r)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(V(r,x,y),V(r,y,x)))))));
  const minimum=(s,r,x)=>C(M(x,s),A(y=>I(M(y,s),N(V(r,y,x)))));
  const minima=(a,r)=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,r,x)))));
  const WO=(a,r)=>C(C(C(irref(a,r),trans(a,r)),total(a,r)),minima(a,r));

  // H is a set of stages, B a candidate union carrier, and R one fixed
  // ambient set-coded relation. Triple capture gives directedness exactly
  // where the three-variable transitivity law uses it.
  const Capture=(b,h)=>A(x=>A(y=>A(z=>I(M(x,b),I(M(y,b),I(M(z,b),E(a=>C(M(a,h),C(C(M(x,a),M(y,a)),M(z,a))))))))));
  const Local=(b,h,r)=>A(a=>I(M(a,h),C(subset(a,b),WO(a,r))));
  const Initial=(b,h,r)=>A(a=>I(M(a,h),A(x=>I(M(x,a),A(y=>I(M(y,b),I(V(r,y,x),M(y,a))))))));

  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  save('directed_irreflexive',ui(b=>ui(h=>ui(r=>ii(Capture(b,h),cap=>ii(Local(b,h,r),local=>
    ui(x=>ii(M(x,b),xb=>ii(V(r,x,x),xx=>
      open(app(us(cap,x,x,x),xb,xb,xb),(a,ap)=>{
        const wo=ar(app(ue(local,a),al(ap))),xa=al(al(ar(ap)));
        return app(app(ue(al(al(al(wo))),x),xa),xx);
      })
    )))
  ))))));

  save('directed_transitive',ui(b=>ui(h=>ui(r=>ii(Capture(b,h),cap=>ii(Local(b,h,r),local=>
    ui(x=>ui(y=>ui(z=>ii(M(x,b),xb=>ii(M(y,b),yb=>ii(M(z,b),zb=>ii(V(r,x,y),xy=>ii(V(r,y,z),yz=>
      open(app(us(cap,x,y,z),xb,yb,zb),(a,ap)=>{
        const wo=ar(app(ue(local,a),al(ap))),members=ar(ap);
        return app(us(ar(al(al(wo))),x,y,z),al(al(members)),ar(al(members)),ar(members),xy,yz);
      })
    ))))))))
  ))))));

  save('directed_total',ui(b=>ui(h=>ui(r=>ii(Capture(b,h),cap=>ii(Local(b,h,r),local=>
    ui(x=>ui(y=>ii(M(x,b),xb=>ii(M(y,b),yb=>
      open(app(us(cap,x,y,x),xb,yb,xb),(a,ap)=>{
        const wo=ar(app(ue(local,a),al(ap))),members=al(ar(ap));
        return app(us(ar(al(wo)),x,y),al(members),ar(members));
      })
    ))))
  ))))));

  save('initial_segment_minima',ui(b=>ui(h=>ui(r=>ii(Capture(b,h),cap=>ii(Local(b,h,r),local=>ii(Initial(b,h,r),initial=>
    ui(s=>ii(subset(s,b),sb=>ii(nonempty(s),sn=>{
      const goal=E(m=>minimum(s,r,m));
      return open(sn,(x,xs)=>{
        const xb=app(ue(sb,x),xs);
        return open(app(us(cap,x,x,x),xb,xb,xb),(a,ap)=>{
          const ah=al(ap),xa=al(al(ar(ap))),wo=ar(app(ue(local,a),ah));
          return open(separation(s,[a],y=>M(y,a)),(t,tp)=>{
            const ta=ui(y=>ii(M(y,t),yt=>ar(from(tp,y,yt))));
            const tn=ei(nonempty(t),x,into(tp,x,ai(xs,xa)));
            return open(app(ue(ar(wo),t),ta,tn),(m,mp)=>{
              const split=from(tp,m,al(mp)),ms=al(split),ma=ar(split);
              const bound=ui(y=>ii(M(y,s),ys=>ii(V(r,y,m),ym=>{
                const yb=app(ue(sb,y),ys);
                const ya=app(ue(app(ue(app(ue(initial,a),ah),m),ma),y),yb,ym);
                const yt=into(tp,y,ai(ys,ya));
                return app(app(ue(ar(mp),y),yt),ym);
              })));
              return ei(goal,m,ai(ms,bound));
            });
          });
        });
      });
    })))
  )))))));

  save('directed_initial_segment_well_order',ui(b=>ui(h=>ui(r=>ii(Capture(b,h),cap=>ii(Local(b,h,r),local=>ii(Initial(b,h,r),initial=>{
    const apply=name=>app(us(imported(proofs[name]),b,h,r),cap,local);
    const irr=apply('directed_irreflexive'),tr=apply('directed_transitive'),tot=apply('directed_total');
    const mins=app(apply('initial_segment_minima'),initial);
    return ai(ai(ai(irr,tr),tot),mins);
  })))))));

  return {proofs,formulas:{
    capture:db(Capture('b','h'),['b','h']),
    local:db(Local('b','h','r'),['b','h','r']),
    initial:db(Initial('b','h','r'),['b','h','r']),
    well_order:db(WO('b','r'),['b','r'])
  }};
}

export { buildCoherentWellOrder };
