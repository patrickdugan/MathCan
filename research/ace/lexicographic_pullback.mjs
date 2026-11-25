// ACE-03W. Lexicographic order through a functional injective representation.
// Formula-valued component orders allow finite tuple induction without
// presupposing that every intermediate order has a set representation.
import { kernel, same, scoped } from './zf_interface.mjs';

function buildLexicographicPullback(defs,spec) {
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

  const {paramCount,firstCarrier,secondCarrier,outputCarrier,firstOrder,secondOrder,representation}=spec;
  if(!Number.isSafeInteger(paramCount)||paramCount<1||paramCount>30||
    ![firstCarrier,secondCarrier,outputCarrier].every(i=>Number.isSafeInteger(i)&&i>=0&&i<paramCount)||
    !scoped(firstOrder,paramCount+2,false)||!scoped(secondOrder,paramCount+2,false)||
    !scoped(representation,paramCount+3,false))throw Error('lexicographic specification scope');
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const sub=(s,a)=>all(s,x=>M(x,a)),ne=s=>E(x=>M(x,s));
  const irref=(a,lt)=>all(a,x=>N(lt(x,x)));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),all(s,y=>N(lt(y,x))));
  const minima=(a,lt)=>A(s=>I(sub(s,a),I(ne(s),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const first=(ps,x,y)=>named(firstOrder,[x,y,...ps]);
  const second=(ps,x,y)=>named(secondOrder,[x,y,...ps]);
  const rep=(ps,p,a,b)=>named(representation,[p,a,b,...ps]);
  const cover=ps=>all(ps[outputCarrier],p=>some(ps[firstCarrier],a=>some(ps[secondCarrier],b=>rep(ps,p,a,b))));
  const functional=ps=>A(p=>A(a=>A(b=>A(c=>A(d=>I(M(p,ps[outputCarrier]),
    I(rep(ps,p,a,b),I(rep(ps,p,c,d),C(Q(a,c),Q(b,d))))))))));
  const injective=ps=>A(p=>A(q=>A(a=>A(b=>I(M(p,ps[outputCarrier]),I(M(q,ps[outputCarrier]),
    I(rep(ps,p,a,b),I(rep(ps,q,a,b),Q(p,q)))))))));
  const compare=(ps,a,b,c,d)=>O(first(ps,a,c),C(Q(a,c),second(ps,b,d)));
  const lex=(ps,p,q)=>C(C(M(p,ps[outputCarrier]),M(q,ps[outputCarrier])),
    some(ps[firstCarrier],a=>some(ps[secondCarrier],b=>C(rep(ps,p,a,b),
      some(ps[firstCarrier],c=>some(ps[secondCarrier],d=>C(rep(ps,q,c,d),compare(ps,a,b,c,d))))))));
  const firstWO=ps=>WO(ps[firstCarrier],(x,y)=>first(ps,x,y));
  const secondWO=ps=>WO(ps[secondCarrier],(x,y)=>second(ps,x,y));
  const outputWO=ps=>WO(ps[outputCarrier],(x,y)=>lex(ps,x,y));
  const premises={first:firstWO,second:secondWO,cover,functional,injective},proofs={};
  function withPremises(names,fn) {
    return qs(paramCount,(...ps)=>{
      function next(i,hs){return i===names.length?fn(ps,hs):ii(premises[names[i]](ps),h=>next(i+1,{...hs,[names[i]]:h}));}
      return next(0,{});
    });
  }
  const save=(id,p)=>{proofs[id]={goal:db(p.goal),proof:p.emit([],[])};};
  const part=(wo,k)=>k===0?al(al(al(wo))):k===1?ar(al(al(wo))):k===2?ar(al(wo)):ar(wo);
  const equalChain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  const inSome=(goal,x,m,p)=>ei(goal,x,ai(m,p));
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  function introduce(ps,p,q,pc,qc,a,b,c,d,aa,bb,ca,dbb,rp,rq,cmp) {
    const goal=lex(ps,p,q),ga=goal[2],gb=inside(ga,a)[2];
    const gc=inside(gb,b)[2][2],gd=inside(gc,c)[2];
    return ai(ai(pc,qc),inSome(ga,a,aa,inSome(gb,b,bb,ai(rp,
      inSome(gc,c,ca,inSome(gd,d,dbb,ai(rq,cmp)))))));
  }
  function openLex(p,fn) {
    return open(ar(p),(a,ap)=>open(ar(ap),(b,bp)=>
      open(ar(ar(bp)),(c,cp)=>open(ar(cp),(d,dp)=>fn({
        a,b,c,d,aa:al(ap),bb:al(bp),ca:al(cp),dbb:al(dp),
        left:al(ar(bp)),right:al(ar(dp)),cmp:ar(ar(dp)),pc:al(al(p)),qc:ar(al(p))
      })))));
  }
  function coordinates(covered,p,pc,fn) {
    return open(app(ue(covered,p),pc),(a,ap)=>open(ar(ap),(b,bp)=>fn(a,b,al(ap),al(bp),ar(bp))));
  }

  save('lexicographic_irreflexive',withPremises(['first','second','functional'],(ps,h)=>
    allProof(ps[outputCarrier],p=>ii(lex(ps,p,p),pp=>openLex(pp,t=>{
      const eq=app(us(h.functional,p,t.a,t.b,t.c,t.d),t.pc,t.left,t.right);
      return oe(t.cmp,F,
        lt=>app(app(ue(part(h.first,0),t.a),t.aa),eqSub(sym(al(eq)),z=>first(ps,t.a,z),lt)),
        right=>app(app(ue(part(h.second,0),t.b),t.bb),eqSub(sym(ar(eq)),z=>second(ps,t.b,z),ar(right))));
    })))
  ));
  function allProof(set,fn){return ui(x=>ii(M(x,set),hx=>fn(x,hx)));}

  save('lexicographic_transitive',withPremises(['first','second','functional'],(ps,h)=>
    qs(3,(p,q,r)=>ii(M(p,ps[outputCarrier]),pc=>ii(M(q,ps[outputCarrier]),qc=>ii(M(r,ps[outputCarrier]),rc=>
      ii(lex(ps,p,q),pq=>ii(lex(ps,q,r),qr=>openLex(pq,t=>openLex(qr,u=>{
        const eq=app(us(h.functional,q,t.c,t.d,u.a,u.b),qc,t.right,u.left);
        const ca=eqSub(sym(al(eq)),z=>compare(ps,z,u.b,u.c,u.d),u.cmp);
        const cd=eqSub(sym(ar(eq)),z=>compare(ps,t.c,z,u.c,u.d),ca);
        const cmpGoal=compare(ps,t.a,t.b,u.c,u.d);
        const cmp=oe(t.cmp,cmpGoal,
          ac=>oe(cd,cmpGoal,
            ce=>ol(app(us(part(h.first,1),t.a,t.c,u.c),t.aa,t.ca,u.ca,ac,ce),cmpGoal[2]),
            ef=>ol(eqSub(al(ef),z=>first(ps,t.a,z),ac),cmpGoal[2])),
          ab=>oe(cd,cmpGoal,
            ce=>ol(eqSub(sym(al(ab)),z=>first(ps,z,u.c),ce),cmpGoal[2]),
            ef=>or(cmpGoal[1],ai(equalChain(al(ab),al(ef)),
              app(us(part(h.second,1),t.b,t.d,u.d),t.bb,t.dbb,u.dbb,ar(ab),ar(ef))))));
        return introduce(ps,p,r,pc,rc,t.a,t.b,u.c,u.d,t.aa,t.bb,u.ca,u.dbb,t.left,u.right,cmp);
      }))))))))
  ));

  save('lexicographic_total',withPremises(['first','second','cover','injective'],(ps,h)=>
    qs(2,(p,q)=>ii(M(p,ps[outputCarrier]),pc=>ii(M(q,ps[outputCarrier]),qc=>
      coordinates(h.cover,p,pc,(a,b,aa,bb,rp)=>coordinates(h.cover,q,qc,(c,d,ca,dbb,rq)=>{
        const goal=O(Q(p,q),O(lex(ps,p,q),lex(ps,q,p)));
        const forward=cmp=>or(goal[1],ol(introduce(ps,p,q,pc,qc,a,b,c,d,aa,bb,ca,dbb,rp,rq,cmp),goal[2][2]));
        const reverse=cmp=>or(goal[1],or(goal[2][1],introduce(ps,q,p,qc,pc,c,d,a,b,ca,dbb,aa,bb,rq,rp,cmp)));
        const firstCases=app(us(part(h.first,2),a,c),aa,ca);
        return oe(firstCases,goal,
          ac=>oe(app(us(part(h.second,2),b,d),bb,dbb),goal,
            bd=>{
              const atA=eqSub(sym(ac),z=>rep(ps,q,z,d),rq);
              const atB=eqSub(sym(bd),z=>rep(ps,q,a,z),atA);
              return ol(app(us(h.injective,p,q,a,b),pc,qc,rp,atB),goal[2]);
            },
            alternatives=>oe(alternatives,goal,
              bd=>forward(or(first(ps,a,c),ai(ac,bd))),
              db0=>reverse(or(first(ps,c,a),ai(sym(ac),db0))))),
          alternatives=>oe(alternatives,goal,
            ac=>forward(ol(ac,C(Q(a,c),second(ps,b,d)))),
            ca0=>reverse(ol(ca0,C(Q(c,a),second(ps,d,b))))));
      }))
    )))
  ));

  save('lexicographic_minima',withPremises(['first','second','cover','functional'],(ps,h)=>
    ui(s=>ii(sub(s,ps[outputCarrier]),sc=>ii(ne(s),sn=>{
      const image=a=>some(s,p=>some(ps[secondCarrier],b=>rep(ps,p,a,b)));
      return open(separation(ps[firstCarrier],[...ps,s],image),(imageSet,im)=>{
        const imageSub=ui(a=>ii(M(a,imageSet),ma=>al(from(im,a,ma))));
        const imageNonempty=open(sn,(p,ps0)=>coordinates(h.cover,p,app(ue(sc,p),ps0),(a,b,aa,bb,rp)=>
          ei(ne(imageSet),a,into(im,a,ai(aa,inSome(image(a),p,ps0,
            inSome(inside(image(a),p)[2],b,bb,rp)))))));
        return open(app(ue(part(h.first,3),imageSet),imageSub,imageNonempty),(a,amin)=>{
          const firstInfo=from(im,a,al(amin)),aa=al(firstInfo);
          const fiber=b=>some(s,p=>rep(ps,p,a,b));
          return open(separation(ps[secondCarrier],[...ps,s,a],fiber),(fiberSet,fs)=>{
            const fiberSub=ui(b=>ii(M(b,fiberSet),mb=>al(from(fs,b,mb))));
            const fiberNonempty=open(ar(firstInfo),(p,pp)=>open(ar(pp),(b,bp)=>
              ei(ne(fiberSet),b,into(fs,b,ai(al(bp),inSome(fiber(b),p,al(pp),ar(bp)))))));
            return open(app(ue(part(h.second,3),fiberSet),fiberSub,fiberNonempty),(b,bmin)=>{
              const secondInfo=from(fs,b,al(bmin)),bb=al(secondInfo);
              return open(ar(secondInfo),(p,pp)=>{
                const pc=app(ue(sc,p),al(pp)),rp=ar(pp);
                const minimal=ui(q=>ii(M(q,s),qs0=>ii(lex(ps,q,p),qp=>openLex(qp,t=>{
                  const eq=app(us(h.functional,p,a,b,t.c,t.d),pc,rp,t.right);
                  const atA=eqSub(sym(al(eq)),z=>compare(ps,t.a,t.b,z,t.d),t.cmp);
                  const atB=eqSub(sym(ar(eq)),z=>compare(ps,t.a,t.b,a,z),atA);
                  return oe(atB,F,
                    lt=>{
                      const coordinate=into(im,t.a,ai(t.aa,inSome(image(t.a),q,qs0,
                        inSome(inside(image(t.a),q)[2],t.b,t.bb,t.left))));
                      return app(app(ue(ar(amin),t.a),coordinate),lt);
                    },
                    last=>{
                      const sameFirst=eqSub(al(last),z=>rep(ps,q,z,t.b),t.left);
                      const coordinate=into(fs,t.b,ai(t.bb,inSome(fiber(t.b),q,qs0,sameFirst)));
                      return app(app(ue(ar(bmin),t.b),coordinate),ar(last));
                    });
                }))));
                return ei(E(x=>minimum(s,(x,y)=>lex(ps,x,y),x)),p,ai(al(pp),minimal));
              });
            });
          });
        });
      });
    })))
  ));

  save('lexicographic_well_order',withPremises(['first','second','cover','functional','injective'],(ps,h)=>{
    const get=(name,keys)=>app(us(imported(proofs[name]),...ps),...keys.map(k=>h[k]));
    return ai(ai(ai(
      get('lexicographic_irreflexive',['first','second','functional']),
      get('lexicographic_transitive',['first','second','functional'])),
      get('lexicographic_total',['first','second','cover','injective'])),
      get('lexicographic_minima',['first','second','cover','functional']));
  }));
  const ps=Array.from({length:paramCount},(_,i)=>'p'+i);
  return {proofs,spec,formulas:{
    cover:db(cover(ps),ps),functional:db(functional(ps),ps),injective:db(injective(ps),ps),
    lexicographic:db(lex(ps,'x','y'),['x','y',...ps]),
    well_order_first:db(firstWO(ps),ps),well_order_second:db(secondWO(ps),ps),well_order_output:db(outputWO(ps),ps)
  }};
}

function pairLexicographicSpecification(defs) {
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  return {paramCount:5,firstCarrier:0,secondCarrier:1,outputCarrier:2,
    firstOrder:embed(defs.val,[5,0,1]),secondOrder:embed(defs.val,[6,0,1]),representation:defs.pair};
}

export { buildLexicographicPullback, pairLexicographicSpecification };
