// ACE-03W. Uniform finite tuple lexicographic order and length-first order.
// The pinned Tuple/Graph formulas and executable ZF kernel are unchanged.
import { kernel, same } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildOmegaInduction, buildOmegaWellOrder } from './omega_well_order.mjs';
import { buildLexicographicPullback } from './lexicographic_pullback.mjs';

function finiteSequenceOrderFormulas(defs) {
  let serial=0;
  const fresh=()=>`fs${serial++}`;
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],F=['F'];
  const I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q],N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh();return [op,x,fn(x)];};
  const A=fn=>bind('A',fn),E=fn=>bind('E',fn);
  function named(p,env){
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,env[a],env[b]];
    if(op==='A'||op==='E'){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env){
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='='){
      const i=env.indexOf(a),j=env.indexOf(b);
      if(i<0||j<0)throw Error('finite sequence interface free variable');
      return [op,i,j];
    }
    if(op==='A'||op==='E')return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const form=(name,...args)=>named(defs[name],args);
  const V=(f,i,x)=>form('val',f,i,x),G=(f,n)=>form('graph',f,n),T=(f,n,a)=>form('tuple',f,n,a);
  const prefix=(h,f,n)=>C(G(h,n),all(n,i=>A(x=>iff(V(h,i,x),V(f,i,x)))));
  const before=(f,g,k)=>all(k,i=>A(x=>A(y=>I(V(f,i,x),I(V(g,i,y),Q(x,y))))));
  const lex=(f,g,n,r)=>some(n,k=>E(x=>E(y=>C(C(C(V(f,k,x),V(g,k,y)),V(r,x,y)),before(f,g,k)))));
  const subset=(s,a)=>all(s,x=>M(x,a)),nonempty=s=>E(x=>M(x,s));
  const irref=(a,lt)=>all(a,x=>N(lt(x,x)));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),all(s,y=>N(lt(y,x))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const family=(s,n,a)=>all(s,f=>T(f,n,a));
  const good=(n,a,r)=>A(s=>I(family(s,n,a),WO(s,(f,g)=>lex(f,g,n,r))));
  const finiteFamily=(s,w,a)=>all(s,f=>some(w,n=>T(f,n,a)));
  const finiteCarrier=(s,w,a)=>A(f=>iff(M(f,s),some(w,n=>T(f,n,a))));
  const shortlex=(f,g,w,a,r)=>some(w,m=>some(w,n=>C(C(T(f,m,a),T(g,n,a)),O(M(m,n),C(Q(m,n),lex(f,g,m,r))))));
  const fibre=(t,s,n,a)=>A(f=>iff(M(f,t),C(M(f,s),T(f,n,a))));
  const fibres=(s,w,a,r)=>all(w,n=>E(t=>C(fibre(t,s,n,a),WO(t,(f,g)=>lex(f,g,n,r)))));
  return {
    prefix:db(prefix('h','f','n'),['h','f','n']),
    before:db(before('f','g','k'),['f','g','k']),
    lex:db(lex('f','g','n','r'),['f','g','n','r']),
    tuple_family:db(family('s','n','a'),['s','n','a']),
    finite_lex_property:db(good('n','a','r'),['n','a','r']),
    finite_tuple_family:db(finiteFamily('s','w','a'),['s','w','a']),
    finite_tuple_carrier:db(finiteCarrier('s','w','a'),['s','w','a']),
    shortlex:db(shortlex('f','g','w','a','r'),['f','g','w','a','r']),
    tuple_fibre:db(fibre('t','s','n','a'),['t','s','n','a']),
    ordered_tuple_fibres:db(fibres('s','w','a','r'),['s','w','a','r'])
  };
}

function buildFiniteSequenceOrder(defs) {
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
  const subset=(s,a)=>all(s,x=>M(x,a)),nonempty=s=>E(x=>M(x,s));
  const Trans=n=>all(n,k=>all(k,i=>M(i,n)));
  const Union=(s,u)=>A(x=>iff(M(x,u),E(y=>C(M(y,s),M(x,y)))));
  const Power=(a,p)=>A(x=>iff(M(x,p),subset(x,a)));
  const form=(name,...args)=>named(defs[name],args);
  const V=(f,k,x)=>form('val',f,k,x),G=(f,n)=>form('graph',f,n),T=(f,n,a)=>form('tuple',f,n,a);
  const Pair=(p,x,y)=>form('pair',p,x,y),Empty=n=>form('empty',n),Succ=(n,d)=>form('successor',n,d);
  const Omega=w=>form('omega',w),forms=finiteSequenceOrderFormulas(defs);
  const Prefix=(h,f,n)=>named(forms.prefix,[h,f,n]);
  const Before=(f,g,k)=>named(forms.before,[f,g,k]);
  const Lex=(f,g,n,r)=>named(forms.lex,[f,g,n,r]);
  const Family=(s,n,a)=>named(forms.tuple_family,[s,n,a]);
  const Good=(n,a,r)=>named(forms.finite_lex_property,[n,a,r]);
  const FiniteFamily=(s,w,a)=>named(forms.finite_tuple_family,[s,w,a]);
  const Shortlex=(f,g,w,a,r)=>named(forms.shortlex,[f,g,w,a,r]);
  const Fibre=(t,s,n,a)=>named(forms.tuple_fibre,[t,s,n,a]);
  const Fibres=(s,w,a,r)=>named(forms.ordered_tuple_fibres,[s,w,a,r]);
  const irref=(a,lt)=>all(a,x=>N(lt(x,x)));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),all(s,y=>N(lt(y,x))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const inner=(p,x)=>replace(p[2],p[1],x)[2];
  const someIn=(goal,x,xs,p)=>ei(goal,x,ai(xs,p));
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  const finite=buildF(defs,'relations'),existing=buildE(defs,true),omega=buildOmegaWellOrder(defs);
  const proofs={};
  const save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];};
  function withProofs(names,fn,ps=[]){return names.length===0?fn(...ps):
    use(imported(proofs[names[0]]),p=>withProofs(names.slice(1),fn,[...ps,p]));}
  const graphExt=()=>imported(existing.graph_extensionality);
  function graphUnique(graph,f,n,i,ins,x,y,fx,fy) {
    return open(app(ue(ar(graph),i),ins),(u,up)=>chain(app(ue(ar(up),x),fx),sym(app(ue(ar(up),y),fy))));
  }
  function prefixTo(prefix,i,ins,v,value){return app(al(ue(app(ue(ar(prefix),i),ins),v)),value);}
  function prefixFrom(prefix,i,ins,v,value){return app(ar(ue(app(ue(ar(prefix),i),ins),v)),value);}
  function lexIntro(f,g,n,r,k,x,y,kn,fx,gy,xy,before) {
    const goal=Lex(f,g,n,r),afterK=inner(goal,k),afterX=replace(afterK[2],afterK[1],x);
    return someIn(goal,k,kn,ei(afterK,x,ei(afterX,y,ai(ai(ai(fx,gy),xy),before))));
  }
  function openLex(p,fn){return open(p,(k,kp)=>open(ar(kp),(x,xp)=>open(xp,(y,yp)=>
    fn(k,x,y,al(kp),al(al(al(yp))),ar(al(al(yp))),ar(al(yp)),ar(yp)))));}
  function unionIn(u,x,y,yb,xy){const goal=ue(u,x).goal[2][1];return into(u,x,ei(goal,y,ai(yb,xy)));}
  const Rep=(f,h,x,n)=>C(Prefix(h,f,n),V(f,n,x));
  const productSpec={paramCount:5,firstCarrier:4,secondCarrier:1,outputCarrier:3,
    firstOrder:db(Lex('x','y','n','r'),['x','y','n','a','r','s','p']),
    secondOrder:db(V('r','x','y'),['x','y','n','a','r','s','p']),
    representation:db(Rep('f','h','x','n'),['f','h','x','n','a','r','s','p'])};
  const product=buildLexicographicPullback(defs,productSpec);
  const Cover=(s,p,n,a)=>all(s,f=>some(p,h=>some(a,x=>Rep(f,h,x,n))));
  const Func=(s,n)=>A(f=>A(h=>A(x=>A(q=>A(y=>I(M(f,s),I(Rep(f,h,x,n),I(Rep(f,q,y,n),C(Q(h,q),Q(x,y))))))))));
  const Inj=(s,n)=>A(f=>A(g=>A(h=>A(x=>I(M(f,s),I(M(g,s),I(Rep(f,h,x,n),I(Rep(g,h,x,n),Q(f,g)))))))));
  const ProductLex=(f,g,n,a,r,s,p)=>named(product.formulas.lexicographic,[f,g,n,a,r,s,p]);
  const ProductAgree=(s,p,n,d,a,r)=>A(f=>A(g=>I(M(f,s),I(M(g,s),iff(ProductLex(f,g,n,a,r,s,p),Lex(f,g,d,r))))));
  function openProduct(lex,fn){return open(ar(lex),(h,hp)=>open(ar(hp),(x,xp)=>
    open(ar(ar(xp)),(q,qp)=>open(ar(qp),(y,yp)=>fn(h,x,q,y,
      al(hp),al(xp),al(qp),al(yp),al(ar(xp)),al(ar(yp)),ar(ar(yp)))))));}
  function productIntro(f,g,n,a,r,s,p,fs,gs,h,x,q,y,hp,xa,qp,ya,fh,gq,cmp) {
    const goal=ProductLex(f,g,n,a,r,s,p),afterH=inner(goal[2],h),afterX=inner(afterH,x);
    const afterQ=inner(afterX[2],q);
    return ai(ai(fs,gs),someIn(goal[2],h,hp,someIn(afterH,x,xa,ai(fh,
      someIn(afterX[2],q,qp,someIn(afterQ,y,ya,ai(gq,cmp)))))));
  }
  function openShort(p,fn){return open(p,(m,mp)=>open(ar(mp),(n,np)=>
    fn(m,n,al(mp),al(np),al(al(ar(np))),ar(al(ar(np))),ar(ar(np)))));}
  function shortIntro(f,g,w,a,r,m,n,mw,nw,tf,tg,cmp) {
    const goal=Shortlex(f,g,w,a,r);
    return someIn(goal,m,mw,someIn(inner(goal,m),n,nw,ai(ai(tf,tg),cmp)));
  }

  // Separation restricts the exact graph itself, so raw members keep their
  // pair shape and every value in the smaller domain is preserved.
  save('prefix_graph_exists',qs(3,(f,d,n)=>ii(G(f,d),graph=>ii(subset(n,d),nd=>
    open(separation(f,[n],p=>some(n,i=>E(v=>Pair(p,i,v)))),(h,hp)=>{
      const hf=ui(p=>ii(M(p,h),ph=>al(from(hp,p,ph))));
      const forward=(i,v,value)=>open(value,(p,pv)=>ei(V(f,i,v),p,ai(al(from(hp,p,al(pv))),ar(pv))));
      const backward=(i,ins,v,value)=>open(value,(p,pv)=>{
        const pred=some(n,j=>E(x=>Pair(p,j,x))),afterI=inner(pred,i);
        const hit=someIn(pred,i,ins,ei(afterI,v,ar(pv)));
        return ei(V(h,i,v),p,ai(into(hp,p,ai(al(pv),hit)),ar(pv)));
      });
      const shape=ui(p=>ii(M(p,h),ph=>ar(from(hp,p,ph))));
      const values=ui(i=>ii(M(i,n),ins=>open(app(ue(ar(graph),i),app(ue(nd,i),ins)),(v,vp)=>{
        const goal=E(x=>C(V(h,i,x),A(y=>I(V(h,i,y),Q(y,x)))));
        const unique=ui(y=>ii(V(h,i,y),hy=>app(ue(ar(vp),y),forward(i,y,hy))));
        return ei(goal,v,ai(backward(i,ins,v,al(vp)),unique));
      })));
      const agree=ui(i=>ii(M(i,n),ins=>ui(v=>ai(
        ii(V(h,i,v),hv=>forward(i,v,hv)),ii(V(f,i,v),fv=>backward(i,ins,v,fv))
      ))));
      return ei(E(h=>C(subset(h,f),Prefix(h,f,n))),h,ai(hf,ai(ai(shape,values),agree)));
    })
  ))));

  save('prefix_graph_unique',qs(4,(p,q,f,n)=>ii(Prefix(p,f,n),pf=>ii(Prefix(q,f,n),qf=>
    app(us(graphExt(),p,q,n),al(pf),al(qf),ui(i=>ii(M(i,n),ins=>ui(v=>ai(
      ii(V(p,i,v),pv=>prefixFrom(qf,i,ins,v,prefixTo(pf,i,ins,v,pv))),
      ii(V(q,i,v),qv=>prefixFrom(pf,i,ins,v,prefixTo(qf,i,ins,v,qv)))
    )))))
  ))));

  save('prefixes_equal_from_before',qs(5,(p,q,f,g,n)=>
    ii(Prefix(p,f,n),pf=>ii(Prefix(q,g,n),qg=>ii(Before(f,g,n),before=>
      app(us(graphExt(),p,q,n),al(pf),al(qg),ui(i=>ii(M(i,n),ins=>ui(v=>{
        const forward=ii(V(p,i,v),pv=>open(app(ue(ar(al(qg)),i),ins),(u,up)=>{
          const equal=app(us(app(ue(before,i),ins),v,u),prefixTo(pf,i,ins,v,pv),prefixTo(qg,i,ins,u,al(up)));
          return eqSub(sym(equal),z=>V(q,i,z),al(up));
        }));
        const backward=ii(V(q,i,v),qv=>open(app(ue(ar(al(pf)),i),ins),(u,up)=>{
          const equal=app(us(app(ue(before,i),ins),u,v),prefixTo(pf,i,ins,u,al(up)),prefixTo(qg,i,ins,v,qv));
          return eqSub(equal,z=>V(p,i,z),al(up));
        }));
        return ai(forward,backward);
      }))))
    )))
  ));

  save('tuple_value_in_carrier',qs(5,(f,n,a,i,x)=>ii(T(f,n,a),tuple=>ii(M(i,n),ins=>ii(V(f,i,x),fx=>
    open(app(ue(ar(tuple),i),ins),(y,yp)=>{
      const equal=graphUnique(al(tuple),f,n,i,ins,x,y,fx,ar(yp));
      return eqSub(sym(equal),z=>M(z,a),al(yp));
    })
  )))));

  save('prefix_is_tuple',qs(5,(h,f,n,d,a)=>ii(T(f,d,a),tuple=>ii(subset(n,d),nd=>ii(Prefix(h,f,n),prefix=>
    ai(al(prefix),ui(i=>ii(M(i,n),ins=>open(app(ue(ar(tuple),i),app(ue(nd,i),ins)),(v,vp)=>
      someIn(some(a,x=>V(h,i,x)),v,al(vp),prefixFrom(prefix,i,ins,v,ar(vp)))
    ))))
  )))));

  save('prefix_last_value_functional',qs(7,(f,p,q,n,d,x,y)=>
    ii(Succ(n,d),succ=>ii(G(f,d),graph=>ii(Prefix(p,f,n),pf=>ii(Prefix(q,f,n),qf=>
    ii(V(f,n,x),fx=>ii(V(f,n,y),fy=>{
      const samePrefix=app(us(imported(proofs.prefix_graph_unique),p,q,f,n),pf,qf);
      const ns=into(succ,n,or(M(n,n),ref(n)));
      return ai(samePrefix,graphUnique(graph,f,d,n,ns,x,y,fx,fy));
    }))))))
  ));

  save('prefix_last_value_injective',qs(6,(f,g,p,n,d,x)=>
    ii(Succ(n,d),succ=>ii(G(f,d),fg=>ii(G(g,d),gg=>ii(Prefix(p,f,n),pf=>ii(Prefix(p,g,n),pg=>
    ii(V(f,n,x),fx=>ii(V(g,n,x),gx=>{
      const ns=into(succ,n,or(M(n,n),ref(n)));
      const agree=ui(i=>ii(M(i,d),ins=>ui(v=>ai(
        ii(V(f,i,v),fv=>oe(from(succ,i,ins),V(g,i,v),
          prev=>prefixTo(pg,i,prev,v,prefixFrom(pf,i,prev,v,fv)),
          last=>{
            const atN=eqSub(last,k=>V(f,k,v),fv);
            const same=graphUnique(fg,f,d,n,ns,v,x,atN,fx);
            const gv=eqSub(sym(same),z=>V(g,n,z),gx);
            return eqSub(sym(last),k=>V(g,k,v),gv);
          })),
        ii(V(g,i,v),gv=>oe(from(succ,i,ins),V(f,i,v),
          prev=>prefixTo(pf,i,prev,v,prefixFrom(pg,i,prev,v,gv)),
          last=>{
            const atN=eqSub(last,k=>V(g,k,v),gv);
            const same=graphUnique(gg,g,d,n,ns,v,x,atN,gx);
            const fv=eqSub(sym(same),z=>V(f,n,z),fx);
            return eqSub(sym(last),k=>V(f,k,v),fv);
          }))
      ))));
      return app(us(graphExt(),f,g,d),fg,gg,agree);
    })))))))
  ));

  save('successor_lex_prefix_last',qs(9,(f,g,p,q,n,d,r,x,y)=>
    ii(Succ(n,d),succ=>ii(Trans(n),tn=>ii(G(f,d),fg=>ii(G(g,d),gg=>
    ii(Prefix(p,f,n),pf=>ii(Prefix(q,g,n),qg=>ii(V(f,n,x),fx=>ii(V(g,n,y),gy=>{
      const split=O(Lex(p,q,n,r),C(Q(p,q),V(r,x,y)));
      const ns=into(succ,n,or(M(n,n),ref(n)));
      const forward=ii(Lex(f,g,d,r),lex=>openLex(lex,(k,u,v,kd,fu,gv,uv,before)=>
        oe(from(succ,k,kd),split,
          kn=>{
            const earlier=ui(i=>ii(M(i,k),ik=>ui(a=>ui(b=>ii(V(p,i,a),pa=>ii(V(q,i,b),qb=>{
              const ins=app(ue(app(ue(tn,k),kn),i),ik);
              return app(us(app(ue(before,i),ik),a,b),prefixTo(pf,i,ins,a,pa),prefixTo(qg,i,ins,b,qb));
            }))))));
            const previous=lexIntro(p,q,n,r,k,u,v,kn,prefixFrom(pf,k,kn,u,fu),prefixFrom(qg,k,kn,v,gv),uv,earlier);
            return ol(previous,split[2]);
          },
          last=>{
            const earlier=eqSub(last,z=>Before(f,g,z),before);
            const samePrefix=app(us(imported(proofs.prefixes_equal_from_before),p,q,f,g,n),pf,qg,earlier);
            const fn=eqSub(last,z=>V(f,z,u),fu),gn=eqSub(last,z=>V(g,z,v),gv);
            const ux=graphUnique(fg,f,d,n,ns,u,x,fn,fx),vy=graphUnique(gg,g,d,n,ns,v,y,gn,gy);
            const atX=eqSub(ux,z=>V(r,z,v),uv),atY=eqSub(vy,z=>V(r,x,z),atX);
            return or(split[1],ai(samePrefix,atY));
          })
      ));
      const backward=ii(split,splitProof=>oe(splitProof,Lex(f,g,d,r),
        previous=>openLex(previous,(k,u,v,kn,pu,qv,uv,before)=>{
          const earlier=ui(i=>ii(M(i,k),ik=>ui(a=>ui(b=>ii(V(f,i,a),fa=>ii(V(g,i,b),gb=>{
            const ins=app(ue(app(ue(tn,k),kn),i),ik);
            return app(us(app(ue(before,i),ik),a,b),prefixFrom(pf,i,ins,a,fa),prefixFrom(qg,i,ins,b,gb));
          }))))));
          return lexIntro(f,g,d,r,k,u,v,into(succ,k,ol(kn,Q(k,n))),
            prefixTo(pf,k,kn,u,pu),prefixTo(qg,k,kn,v,qv),uv,earlier);
        }),
        last=>{
          const earlier=ui(i=>ii(M(i,n),ins=>ui(a=>ui(b=>ii(V(f,i,a),fa=>ii(V(g,i,b),gb=>{
            const pa=prefixFrom(pf,i,ins,a,fa),qb=prefixFrom(qg,i,ins,b,gb);
            const pb=eqSub(sym(al(last)),z=>V(z,i,b),qb);
            return graphUnique(al(pf),p,n,i,ins,a,b,pa,pb);
          }))))));
          return lexIntro(f,g,d,r,n,x,y,ns,fx,gy,ar(last),earlier);
        }
      ));
      return ai(forward,backward);
    }))))))))
  ));

  save('empty_length_lex_well_order',qs(3,(n,a,r)=>ii(Empty(n),empty=>ui(s=>ii(Family(s,n,a),family=>{
    const lt=(f,g)=>Lex(f,g,n,r),absurd=p=>openLex(p,(k,x,y,kn)=>app(ue(empty,k),kn));
    const irr=ui(f=>ii(M(f,s),()=>ii(lt(f,f),ff=>absurd(ff))));
    const tr=ui(f=>ui(g=>ui(h=>ii(M(f,s),()=>ii(M(g,s),()=>ii(M(h,s),()=>ii(lt(f,g),fg=>ii(lt(g,h),()=>fe(absurd(fg),lt(f,h))))))))));
    const tot=ui(f=>ui(g=>ii(M(f,s),fs=>ii(M(g,s),gs=>{
      const equiv=ui(i=>ii(M(i,n),ins=>ui(v=>fe(app(ue(empty,i),ins),iff(V(f,i,v),V(g,i,v))))));
      const equal=app(us(graphExt(),f,g,n),al(app(ue(family,f),fs)),al(app(ue(family,g),gs)),equiv);
      return ol(equal,O(lt(f,g),lt(g,f)));
    }))));
    const mins=ui(t=>ii(subset(t,s),()=>ii(nonempty(t),tn=>open(tn,(f,ft)=>
      ei(E(f=>minimum(t,lt,f)),f,ai(ft,ui(g=>ii(M(g,t),()=>ii(lt(g,f),gf=>absurd(gf))))))
    ))));
    return ai(ai(ai(irr,tr),tot),mins);
  })))));

  // Every prefix is a subset of an original tuple. Power Set of the union
  // of the supplied family therefore bounds all prefixes used in induction.
  save('prefix_carrier_exists',qs(4,(s,n,d,a)=>ii(Succ(n,d),succ=>ii(Family(s,d,a),family=>
    withProofs(['prefix_graph_exists','prefix_is_tuple'],(restrict,tuplePrefix)=>
    open(ue(ax({name:'union'}),s),(u,su)=>open(ue(ax({name:'power'}),u),(b,ub)=>{
      const predicate=h=>C(T(h,n,a),some(s,f=>Prefix(h,f,n)));
      return open(separation(b,[s,n,a],predicate),(p,pp)=>{
        const allPrefixes=ui(h=>ii(M(h,p),hp=>al(ar(from(pp,h,hp)))));
        const cover=ui(f=>ii(M(f,s),fs=>{
          const tuple=app(ue(family,f),fs),nd=ui(i=>ii(M(i,n),ins=>into(succ,i,ol(ins,Q(i,n)))));
          return open(app(us(restrict,f,d,n),al(tuple),nd),(h,hp)=>{
            const hBound=into(ub,h,ui(z=>ii(M(z,h),zh=>unionIn(su,z,f,fs,app(ue(al(hp),z),zh)))));
            const hTuple=app(us(tuplePrefix,h,f,n,d,a),tuple,nd,ar(hp));
            const member=into(pp,h,ai(hBound,ai(hTuple,someIn(some(s,g=>Prefix(h,g,n)),f,fs,ar(hp)))));
            const ns=into(succ,n,or(M(n,n),ref(n)));
            return open(app(ue(ar(tuple),n),ns),(x,xp)=>{
              const goal=some(p,h=>some(a,x=>Rep(f,h,x,n)));
              return someIn(goal,h,member,someIn(inner(goal,h),x,al(xp),ai(ar(hp),ar(xp))));
            });
          });
        }));
        return ei(E(p=>C(Family(p,n,a),Cover(s,p,n,a))),p,ai(allPrefixes,cover));
      });
    })))
  ))));

  save('prefix_representation_laws',qs(4,(s,n,d,a)=>ii(Succ(n,d),succ=>ii(Family(s,d,a),family=>
    withProofs(['prefix_last_value_functional','prefix_last_value_injective'],(func,inj)=>{
      const functional=qs(5,(f,h,x,q,y)=>ii(M(f,s),fs=>ii(Rep(f,h,x,n),fh=>ii(Rep(f,q,y,n),fq=>
        app(us(func,f,h,q,n,d,x,y),succ,al(app(ue(family,f),fs)),al(fh),al(fq),ar(fh),ar(fq))
      ))));
      const injective=qs(4,(f,g,h,x)=>ii(M(f,s),fs=>ii(M(g,s),gs=>ii(Rep(f,h,x,n),fh=>ii(Rep(g,h,x,n),gh=>
        app(us(inj,f,g,h,n,d,x),succ,al(app(ue(family,f),fs)),al(app(ue(family,g),gs)),al(fh),al(gh),ar(fh),ar(gh))
      )))));
      return ai(functional,injective);
    })
  ))));

  save('prefix_lex_agreement',qs(6,(s,p,n,d,a,r)=>ii(Succ(n,d),succ=>ii(Trans(n),tn=>
    ii(Family(s,d,a),family=>ii(Cover(s,p,n,a),cover=>withProofs(['successor_lex_prefix_last'],recurrence=>
      ui(f=>ui(g=>ii(M(f,s),fs=>ii(M(g,s),gs=>{
        const fg=al(app(ue(family,f),fs)),gg=al(app(ue(family,g),gs));
        const forward=ii(ProductLex(f,g,n,a,r,s,p),lex=>openProduct(lex,(h,x,q,y,hp,xa,qp,ya,fh,gq,cmp)=>{
          const formula=app(us(recurrence,f,g,h,q,n,d,r,x,y),succ,tn,fg,gg,al(fh),al(gq),ar(fh),ar(gq));
          return app(ar(formula),cmp);
        }));
        const backward=ii(Lex(f,g,d,r),lex=>open(app(ue(cover,f),fs),(h,hp)=>open(ar(hp),(x,xp)=>
          open(app(ue(cover,g),gs),(q,qp)=>open(ar(qp),(y,yp)=>{
            const fh=ar(xp),gq=ar(yp);
            const formula=app(us(recurrence,f,g,h,q,n,d,r,x,y),succ,tn,fg,gg,al(fh),al(gq),ar(fh),ar(gq));
            return productIntro(f,g,n,a,r,s,p,fs,gs,h,x,q,y,al(hp),al(xp),al(qp),al(yp),fh,gq,app(al(formula),lex));
          })))));
        return ai(forward,backward);
      }))))
    )))
  ))));

  save('prefix_order_agreement_transfer',qs(6,(s,p,n,d,a,r)=>
    ii(ProductAgree(s,p,n,d,a,r),agree=>ii(WO(s,(f,g)=>ProductLex(f,g,n,a,r,s,p)),old=>{
      const toNew=(f,g,fs,gs,proof)=>app(al(app(us(agree,f,g),fs,gs)),proof);
      const toOld=(f,g,fs,gs,proof)=>app(ar(app(us(agree,f,g),fs,gs)),proof);
      const lt=(f,g)=>Lex(f,g,d,r);
      const irr=ui(f=>ii(M(f,s),fs=>ii(lt(f,f),ff=>app(app(ue(al(al(al(old))),f),fs),toOld(f,f,fs,fs,ff)))));
      const tr=qs(3,(f,g,h)=>ii(M(f,s),fs=>ii(M(g,s),gs=>ii(M(h,s),hs=>ii(lt(f,g),fg=>ii(lt(g,h),gh=>
        toNew(f,h,fs,hs,app(us(ar(al(al(old))),f,g,h),fs,gs,hs,toOld(f,g,fs,gs,fg),toOld(g,h,gs,hs,gh)))
      ))))));
      const tot=qs(2,(f,g)=>ii(M(f,s),fs=>ii(M(g,s),gs=>{
        const goal=O(Q(f,g),O(lt(f,g),lt(g,f)));
        return oe(app(us(ar(al(old)),f,g),fs,gs),goal,equal=>ol(equal,goal[2]),alternatives=>oe(alternatives,goal,
          fg=>or(goal[1],ol(toNew(f,g,fs,gs,fg),lt(g,f))),
          gf=>or(goal[1],or(lt(f,g),toNew(g,f,gs,fs,gf)))));
      })));
      const mins=ui(t=>ii(subset(t,s),ts=>ii(nonempty(t),tn=>open(app(ue(ar(old),t),ts,tn),(f,fp)=>{
        const fs=app(ue(ts,f),al(fp));
        const minimal=ui(g=>ii(M(g,t),gt=>ii(lt(g,f),gf=>
          app(app(ue(ar(fp),g),gt),toOld(g,f,app(ue(ts,g),gt),fs,gf))
        )));
        return ei(E(f=>minimum(t,lt,f)),f,ai(al(fp),minimal));
      }))));
      return ai(ai(ai(irr,tr),tot),mins);
    }))
  ));

  // This successor proof constructs its own prefix carrier and invokes the
  // preceding-length theorem on that carrier. Its well-order is not a premise.
  save('successor_length_lex_well_order',qs(4,(n,d,a,r)=>ii(Succ(n,d),succ=>ii(Trans(n),tn=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>ii(Good(n,a,r),previous=>ui(s=>ii(Family(s,d,a),family=>
      open(app(us(imported(proofs.prefix_carrier_exists),s,n,d,a),succ,family),(p,pp)=>{
        const first=app(ue(previous,p),al(pp)),cover=ar(pp);
        const laws=app(us(imported(proofs.prefix_representation_laws),s,n,d,a),succ,family);
        const ordered=app(us(imported(product.proofs.lexicographic_well_order),n,a,r,s,p),first,letters,cover,al(laws),ar(laws));
        const agree=app(us(imported(proofs.prefix_lex_agreement),s,p,n,d,a,r),succ,tn,family,cover);
        return app(us(imported(proofs.prefix_order_agreement_transfer),s,p,n,d,a,r),agree,ordered);
      })
    )))))
  )));

  proofs.tuple_length_induction=buildOmegaInduction(defs,forms.finite_lex_property,2);
  save('finite_length_lex_well_order',qs(4,(w,a,r,m)=>ii(Omega(w),ow=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>ii(M(m,w),mw=>{
      const base=ui(z=>ii(Empty(z),empty=>app(us(imported(proofs.empty_length_lex_well_order),z,a,r),empty)));
      const step=ui(n=>ui(d=>ii(M(n,w),nw=>ii(Succ(n,d),succ=>ii(Good(n,a,r),previous=>{
        const tn=app(us(imported(omega.proofs.omega_member_transitive),w,n),ow,nw);
        return app(us(imported(proofs.successor_length_lex_well_order),n,d,a,r),succ,tn,letters,previous);
      })))));
      const allLengths=app(us(imported(proofs.tuple_length_induction),a,r,w),ow,base,step);
      return app(ue(allLengths,m),mw);
    }))
  )));

  save('exact_graph_domain_unique',qs(3,(f,m,n)=>ii(G(f,m),fm=>ii(G(f,n),fn=>
    use(imported(finite.value_in_domain),domain=>
      app(us(ax({name:'extensionality'}),m,n),ui(i=>ai(
        ii(M(i,m),im=>open(app(ue(ar(fm),i),im),(x,xp)=>app(us(domain,f,n,i,x),fn,al(xp)))),
        ii(M(i,n),ins=>open(app(ue(ar(fn),i),ins),(x,xp)=>app(us(domain,f,m,i,x),fm,al(xp))))
      )))
    )
  ))));

  // For each length separately, Separation provides an actual fibre of the
  // supplied family, and the discharged finite induction well-orders it.
  save('finite_tuple_fibres_well_order',qs(4,(w,a,r,s)=>ii(Omega(w),ow=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>use(imported(proofs.finite_length_lex_well_order),finiteOrder=>
      ui(n=>ii(M(n,w),nw=>open(separation(s,[n,a],f=>T(f,n,a)),(t,tp)=>{
        const family=ui(f=>ii(M(f,t),ft=>ar(from(tp,f,ft))));
        const good=app(us(finiteOrder,w,a,r,n),ow,letters,nw);
        return ei(E(t=>C(Fibre(t,s,n,a),WO(t,(f,g)=>Lex(f,g,n,r)))),t,ai(tp,app(ue(good,t),family)));
      })))
    ))
  )));

  save('shortlex_from_ordered_fibres',qs(4,(w,a,r,s)=>
    ii(WO(w,(m,n)=>M(m,n)),lengthOrder=>ii(Fibres(s,w,a,r),fibres=>ii(FiniteFamily(s,w,a),family=>
      use(imported(proofs.exact_graph_domain_unique),domainUnique=>{
        const lt=(f,g)=>Shortlex(f,g,w,a,r);
        const lengthIrr=al(al(al(lengthOrder))),lengthTrans=ar(al(al(lengthOrder)));
        const lengthTotal=ar(al(lengthOrder)),lengthMin=ar(lengthOrder);
        const fibreAt=(n,nw,fn)=>open(app(ue(fibres,n),nw),(t,tp)=>fn(t,al(tp),ar(tp)));

        const irr=ui(f=>ii(M(f,s),fs=>ii(lt(f,f),ff=>openShort(ff,(m,n,mw,nw,tf,tg,cmp)=>{
          const equal=app(us(domainUnique,f,m,n),al(tf),al(tg));
          return oe(cmp,F,
            mn=>app(app(ue(lengthIrr,m),mw),eqSub(sym(equal),z=>M(m,z),mn)),
            last=>fibreAt(m,mw,(t,tp,order)=>{
              const ft=into(tp,f,ai(fs,tf));
              return app(app(ue(al(al(al(order))),f),ft),ar(last));
            }));
        }))));

        const tr=qs(3,(f,g,h)=>ii(M(f,s),fs=>ii(M(g,s),gs=>ii(M(h,s),hs=>
          ii(lt(f,g),fg=>ii(lt(g,h),gh=>openShort(fg,(m,n,mw,nw,tf,tg,first)=>
            openShort(gh,(k,l,kw,lw,tg2,th,second)=>{
              const nk=app(us(domainUnique,g,n,k),al(tg),al(tg2));
              const atN=eqSub(sym(nk),z=>O(M(z,l),C(Q(z,l),Lex(g,h,z,r))),second);
              const goal=O(M(m,l),C(Q(m,l),Lex(f,h,m,r)));
              const cmp=oe(first,goal,
                mn=>oe(atN,goal,
                  nl=>ol(app(us(lengthTrans,m,n,l),mw,nw,lw,mn,nl),goal[2]),
                  last=>ol(eqSub(al(last),z=>M(m,z),mn),goal[2])),
                same=>oe(atN,goal,
                  nl=>ol(eqSub(sym(al(same)),z=>M(z,l),nl),goal[2]),
                  last=>{
                    const ml=chain(al(same),al(last));
                    const gAtM=eqSub(sym(al(same)),z=>T(g,z,a),tg);
                    const hAtM=eqSub(sym(ml),z=>T(h,z,a),th);
                    const ghAtM=eqSub(sym(al(same)),z=>Lex(g,h,z,r),ar(last));
                    return fibreAt(m,mw,(t,tp,order)=>{
                      const ft=into(tp,f,ai(fs,tf)),gt=into(tp,g,ai(gs,gAtM)),ht=into(tp,h,ai(hs,hAtM));
                      const fh=app(us(ar(al(al(order))),f,g,h),ft,gt,ht,ar(same),ghAtM);
                      return or(goal[1],ai(ml,fh));
                    });
                  }));
              return shortIntro(f,h,w,a,r,m,l,mw,lw,tf,th,cmp);
            })
          ))
        )))));

        const tot=qs(2,(f,g)=>ii(M(f,s),fs=>ii(M(g,s),gs=>
          open(app(ue(family,f),fs),(m,mp)=>open(app(ue(family,g),gs),(n,np)=>{
            const mw=al(mp),nw=al(np),tf=ar(mp),tg=ar(np);
            const goal=O(Q(f,g),O(lt(f,g),lt(g,f)));
            return oe(app(us(lengthTotal,m,n),mw,nw),goal,
              equal=>fibreAt(m,mw,(t,tp,order)=>{
                const gAtM=eqSub(sym(equal),z=>T(g,z,a),tg);
                const ft=into(tp,f,ai(fs,tf)),gt=into(tp,g,ai(gs,gAtM));
                return oe(app(us(ar(al(order)),f,g),ft,gt),goal,
                  same=>ol(same,goal[2]),alternatives=>oe(alternatives,goal,
                    fg=>or(goal[1],ol(shortIntro(f,g,w,a,r,m,m,mw,mw,tf,gAtM,or(M(m,m),ai(ref(m),fg))),lt(g,f))),
                    gf=>or(goal[1],or(lt(f,g),shortIntro(g,f,w,a,r,m,m,mw,mw,gAtM,tf,or(M(m,m),ai(ref(m),gf)))))));
              }),
              alternatives=>oe(alternatives,goal,
                mn=>or(goal[1],ol(shortIntro(f,g,w,a,r,m,n,mw,nw,tf,tg,ol(mn,C(Q(m,n),Lex(f,g,m,r)))),lt(g,f))),
                nm=>or(goal[1],or(lt(f,g),shortIntro(g,f,w,a,r,n,m,nw,mw,tg,tf,ol(nm,C(Q(n,m),Lex(g,f,n,r))))))));
          }))
        )));

        const mins=ui(u=>ii(subset(u,s),usub=>ii(nonempty(u),un=>{
          const realised=n=>some(u,f=>T(f,n,a));
          return open(separation(w,[u,a],realised),(lengths,lp)=>{
            const lw=ui(n=>ii(M(n,lengths),nl=>al(from(lp,n,nl))));
            const ln=open(un,(f,fu)=>open(app(ue(family,f),app(ue(usub,f),fu)),(n,np)=>{
              const hit=someIn(realised(n),f,fu,ar(np));
              return ei(nonempty(lengths),n,into(lp,n,ai(al(np),hit)));
            }));
            return open(app(ue(lengthMin,lengths),lw,ln),(m,minLength)=>{
              const minInfo=from(lp,m,al(minLength)),mw=al(minInfo),witness=ar(minInfo);
              return fibreAt(m,mw,(t,tp,order)=>open(separation(u,[m,a],f=>T(f,m,a)),(v,vp)=>{
                const vt=ui(f=>ii(M(f,v),fv=>{
                  const data=from(vp,f,fv);
                  return into(tp,f,ai(app(ue(usub,f),al(data)),ar(data)));
                }));
                const vn=open(witness,(f,fp)=>ei(nonempty(v),f,into(vp,f,fp)));
                return open(app(ue(ar(order),v),vt,vn),(f,minTuple)=>{
                  const finfo=from(vp,f,al(minTuple)),fu=al(finfo),tf=ar(finfo);
                  const minimal=ui(g=>ii(M(g,u),gu=>ii(lt(g,f),gf=>
                    openShort(gf,(n,l,nw,lw,tg,tf2,cmp)=>{
                      const lm=app(us(domainUnique,f,l,m),al(tf2),al(tf));
                      const atM=eqSub(lm,z=>O(M(n,z),C(Q(n,z),Lex(g,f,n,r))),cmp);
                      return oe(atM,F,
                        nm=>{
                          const hit=someIn(realised(n),g,gu,tg);
                          const nl=into(lp,n,ai(nw,hit));
                          return app(app(ue(ar(minLength),n),nl),nm);
                        },
                        same=>{
                          const gAtM=eqSub(al(same),z=>T(g,z,a),tg);
                          const gfAtM=eqSub(al(same),z=>Lex(g,f,z,r),ar(same));
                          const gv=into(vp,g,ai(gu,gAtM));
                          return app(app(ue(ar(minTuple),g),gv),gfAtM);
                        });
                    })
                  )));
                  return ei(E(f=>minimum(u,lt,f)),f,ai(fu,minimal));
                });
              }));
            });
          });
        })));
        return ai(ai(ai(irr,tr),tot),mins);
      })
    )))
  ));

  save('finite_shortlex_well_order',qs(4,(w,a,r,s)=>ii(Omega(w),ow=>
    ii(WO(a,(x,y)=>V(r,x,y)),letters=>ii(FiniteFamily(s,w,a),family=>{
      const lengths=app(ue(imported(omega.proofs.omega_membership_well_order),w),ow);
      const fibres=app(us(imported(proofs.finite_tuple_fibres_well_order),w,a,r,s),ow,letters);
      return app(us(imported(proofs.shortlex_from_ordered_fibres),w,a,r,s),lengths,fibres,family);
    }))
  )));

  return {proofs,formulas:forms,product_specification:productSpec,product_formulas:product.formulas};
}

export { finiteSequenceOrderFormulas, buildFiniteSequenceOrder };
