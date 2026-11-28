// ACE-03T. Proof objects for least representatives in a well-ordered code set.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same } from './zf_interface.mjs';

function buildWellOrder(defs) {
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

  // Val is the exact Kuratowski-pair graph relation of the pinned definition.
  const V=(r,x,y)=>named(defs.val,[r,x,y]);
  const subset=(s,a)=>A(x=>I(M(x,s),M(x,a)));
  const nonempty=s=>E(x=>M(x,s));
  const irref=(a,lt)=>A(x=>I(M(x,a),N(lt(x,x))));
  const trans=(a,lt)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(a,lt)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minimum=(s,lt,x)=>C(M(x,s),A(y=>I(M(y,s),N(lt(y,x)))));
  const minima=(a,lt)=>A(s=>I(subset(s,a),I(nonempty(s),E(x=>minimum(s,lt,x)))));
  const WO=(a,lt)=>C(C(C(irref(a,lt),trans(a,lt)),total(a,lt)),minima(a,lt));
  const Surj=(a,b,f)=>A(x=>I(M(x,b),E(c=>C(M(c,a),V(f,c,x)))));
  const Func=(a,f)=>A(c=>A(x=>A(y=>I(M(c,a),I(V(f,c,x),I(V(f,c,y),Q(x,y)))))));
  const Min=(a,r,f,x,c)=>C(C(M(c,a),V(f,c,x)),A(d=>I(M(d,a),I(V(f,d,x),N(V(r,d,c))))));
  const MinTotal=(a,b,r,f)=>A(x=>I(M(x,b),E(c=>Min(a,r,f,x,c))));
  const MinUnique=(a,r,f)=>A(x=>A(c=>A(d=>I(Min(a,r,f,x,c),I(Min(a,r,f,x,d),Q(d,c))))));
  const Out=(a,b,r,f,x,y)=>C(C(M(x,b),M(y,b)),E(c=>E(d=>C(C(Min(a,r,f,x,c),Min(a,r,f,y,d)),V(r,c,d)))));
  const outWitness=(a,b,r,f,x,y,c,d,xb,yb,mc,md,lt)=>{
    const g=Out(a,b,r,f,x,y),g1=g[2],g2=replace(g1[2],g1[1],c);
    return ai(ai(xb,yb),ei(g1,c,ei(g2,d,ai(ai(mc,md),lt))));
  };
  const minMem=p=>al(al(p)), minValue=p=>ar(al(p)), minBound=p=>ar(p);
  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  // A nonempty evaluation fiber is an ambient set by Separation.
  save('least_code_total',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>ii(Surj(a,b,f),onto=>ui(x=>ii(M(x,b),xb=>{
    const goal=E(c=>Min(a,r,f,x,c));
    return open(separation(a,[f,x],c=>V(f,c,x)),(s,sp)=>{
      const sub=ui(c=>ii(M(c,s),cs=>al(from(sp,c,cs))));
      const ne=open(app(ue(onto,x),xb),(c,cp)=>ei(nonempty(s),c,into(sp,c,cp)));
      return open(app(ue(ar(wo),s),sub,ne),(c,cp)=>{
        const fiber=from(sp,c,al(cp));
        const bound=ui(d=>ii(M(d,a),da=>ii(V(f,d,x),dx=>app(ue(ar(cp),d),into(sp,d,ai(da,dx))))));
        return ei(goal,c,ai(fiber,bound));
      });
    });
  })))))))));

  // Trichotomy makes a least code unique, without evaluation functionality.
  save('least_code_unique',ui(a=>ui(r=>ui(f=>ii(total(a,(x,y)=>V(r,x,y)),tr=>ui(x=>ui(c=>ui(d=>ii(Min(a,r,f,x,c),mc=>ii(Min(a,r,f,x,d),md=>{
    const cases=app(us(tr,d,c),minMem(md),minMem(mc)),g=Q(d,c);
    return oe(cases,g,p=>p,p=>oe(p,g,
      dc=>fe(app(app(us(minBound(mc),d),minMem(md),minValue(md)),dc),g),
      cd=>fe(app(app(us(minBound(md),c),minMem(mc),minValue(mc)),cd),g)));
  }))))))))));

  save('least_code_injective',ui(a=>ui(r=>ui(f=>ii(Func(a,f),fn=>ui(x=>ui(y=>ui(c=>ii(Min(a,r,f,x,c),mx=>ii(Min(a,r,f,y,c),my=>
    app(us(fn,c,x,y),minMem(mx),minValue(mx),minValue(my))
  ))))))))));

  // Transfer the linear-order laws through the unique least-code relation.
  save('induced_irreflexive',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>{
    const unique=app(us(imported(proofs.least_code_unique),a,r,f),ar(al(wo)));
    return use(unique,uq=>ui(x=>ii(M(x,b),()=>ii(Out(a,b,r,f,x,x),xx=>
      open(ar(xx),(c,cp)=>open(cp,(d,dp)=>{
        const mc=al(al(dp)),md=ar(al(dp)),dc=app(us(uq,x,c,d),mc,md);
        const cc=eqSub(dc,z=>V(r,c,z),ar(dp));
        return app(app(ue(al(al(al(wo))),c),minMem(mc)),cc);
      }))
    ))));
  }))))));

  save('induced_transitive',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>{
    const unique=app(us(imported(proofs.least_code_unique),a,r,f),ar(al(wo)));
    return use(unique,uq=>ui(x=>ui(y=>ui(z=>ii(M(x,b),xb=>ii(M(y,b),()=>ii(M(z,b),zb=>ii(Out(a,b,r,f,x,y),xy=>ii(Out(a,b,r,f,y,z),yz=>
      open(ar(xy),(c,cp)=>open(cp,(d,dp)=>open(ar(yz),(e,ep)=>open(ep,(g,gp)=>{
        const mc=al(al(dp)),md=ar(al(dp)),me=al(al(gp)),mg=ar(al(gp));
        const ed=app(us(uq,y,d,e),md,me),dg=eqSub(ed,v=>V(r,v,g),ar(gp));
        const cg=app(us(ar(al(al(wo))),c,d,g),minMem(mc),minMem(md),minMem(mg),ar(dp),dg);
        return outWitness(a,b,r,f,x,z,c,g,xb,zb,mc,mg,cg);
      }))))
    )))))))));
  }))))));

  save('induced_total',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>ii(Func(a,f),fn=>ii(MinTotal(a,b,r,f),sel=>
    ui(x=>ui(y=>ii(M(x,b),xb=>ii(M(y,b),yb=>{
      const goal=O(Q(x,y),O(Out(a,b,r,f,x,y),Out(a,b,r,f,y,x)));
      return open(app(ue(sel,x),xb),(c,mc)=>open(app(ue(sel,y),yb),(d,md)=>{
        const cases=app(us(ar(al(wo)),c,d),minMem(mc),minMem(md));
        return oe(cases,goal,cd=>{
          const mdAtC=eqSub(sym(cd),v=>Min(a,r,f,y,v),md);
          const eq=app(us(fn,c,x,y),minMem(mc),minValue(mc),minValue(mdAtC));
          return ol(eq,goal[2]);
        },p=>oe(p,goal,
          cd=>or(Q(x,y),ol(outWitness(a,b,r,f,x,y,c,d,xb,yb,mc,md,cd),Out(a,b,r,f,y,x))),
          dc=>or(Q(x,y),or(Out(a,b,r,f,x,y),outWitness(a,b,r,f,y,x,d,c,yb,xb,md,mc,dc)))));
      }));
    }))))
  ))))))));

  // The image of a nonempty set under least codes exists by Separation
  // inside the original code set, so a global choice function is unnecessary.
  save('induced_minima',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>ii(MinTotal(a,b,r,f),sel=>{
    const unique=app(us(imported(proofs.least_code_unique),a,r,f),ar(al(wo)));
    return use(unique,uq=>ui(s=>ii(subset(s,b),sb=>ii(nonempty(s),sn=>{
      const lt=(x,y)=>Out(a,b,r,f,x,y),goal=E(x=>minimum(s,lt,x));
      return open(separation(a,[a,r,f,s],c=>E(x=>C(M(x,s),Min(a,r,f,x,c)))),(t,tp)=>{
        const ta=ui(c=>ii(M(c,t),ct=>al(from(tp,c,ct))));
        const tn=open(sn,(x,xs)=>open(app(ue(sel,x),app(ue(sb,x),xs)),(c,mc)=>{
          const hit=E(y=>C(M(y,s),Min(a,r,f,y,c)));
          return ei(nonempty(t),c,into(tp,c,ai(minMem(mc),ei(hit,x,ai(xs,mc)))));
        }));
        return open(app(ue(ar(wo),t),ta,tn),(c,cp)=>{
          const fiber=ar(from(tp,c,al(cp)));
          return open(fiber,(x,xp)=>{
            const xs=al(xp),mx=ar(xp);
            const minimal=ui(y=>ii(M(y,s),ys=>ii(lt(y,x),yx=>
              open(ar(yx),(d,dp)=>open(dp,(e,ep)=>{
                const my=al(al(ep)),mx2=ar(al(ep)),ec=app(us(uq,x,c,e),mx,mx2);
                const dc=eqSub(ec,v=>V(r,d,v),ar(ep));
                const hit=E(z=>C(M(z,s),Min(a,r,f,z,d)));
                const dt=into(tp,d,ai(minMem(my),ei(hit,y,ai(ys,my))));
                return app(app(ue(ar(cp),d),dt),dc);
              }))
            )));
            return ei(goal,x,ai(xs,minimal));
          });
        });
      });
    }))));
  })))))));

  save('induced_well_order',ui(a=>ui(b=>ui(r=>ui(f=>ii(WO(a,(x,y)=>V(r,x,y)),wo=>ii(Func(a,f),fn=>ii(Surj(a,b,f),onto=>{
    const sel=app(us(imported(proofs.least_code_total),a,b,r,f),wo,onto);
    return use(sel,totalCodes=>{
      const irr=app(us(imported(proofs.induced_irreflexive),a,b,r,f),wo);
      const tr=app(us(imported(proofs.induced_transitive),a,b,r,f),wo);
      const tot=app(us(imported(proofs.induced_total),a,b,r,f),wo,fn,totalCodes);
      const mins=app(us(imported(proofs.induced_minima),a,b,r,f),wo,totalCodes);
      return ai(ai(ai(irr,tr),tot),mins);
    });
  }))))))));

  save('well_order_minimum_unique',ui(u=>ui(r=>ui(s=>ii(total(u,(x,y)=>V(r,x,y)),tr=>ii(subset(s,u),su=>
    ui(y=>ui(z=>ii(minimum(s,(x,y)=>V(r,x,y),y),my=>ii(minimum(s,(x,y)=>V(r,x,y),z),mz=>{
      const cases=app(us(tr,z,y),app(ue(su,z),al(mz)),app(ue(su,y),al(my))),g=Q(z,y);
      return oe(cases,g,p=>p,p=>oe(p,g,
        zy=>fe(app(app(ue(ar(my),z),al(mz)),zy),g),
        yz=>fe(app(app(ue(ar(mz),y),al(my)),yz),g)));
    }))))
  ))))));

  const FamilyNE=a=>A(x=>I(M(x,a),nonempty(x)));
  const Disjoint=a=>A(x=>A(y=>I(C(C(M(x,a),M(y,a)),N(Q(x,y))),A(z=>I(M(z,x),N(M(z,y)))))));
  const Covers=(a,u)=>A(x=>I(M(x,a),subset(x,u)));
  const Selected=a=>E(c=>A(x=>I(M(x,a),E(y=>C(C(M(y,x),M(y,c)),A(z=>I(C(M(z,x),M(z,c)),Q(z,y))))))));

  // Ambient final combinator for the kernel's exact disjoint-family Choice
  // axiom body. Constructibility of the carrier, order and separating set
  // is an additional obligation for a relativized L-Choice certificate.
  save('choice_from_carrier_well_order',ui(a=>ui(u=>ui(r=>ii(WO(u,(x,y)=>V(r,x,y)),wo=>ii(Covers(a,u),cover=>ii(C(FamilyNE(a),Disjoint(a)),family=>{
    const lt=(x,y)=>V(r,x,y);
    const predicate=y=>E(x=>C(M(x,a),minimum(x,lt,y)));
    return open(separation(u,[a,r],predicate),(c,cp)=>{
      const each=ui(x=>ii(M(x,a),xa=>{
        const xu=app(ue(cover,x),xa),xn=app(ue(al(family),x),xa);
        return open(app(ue(ar(wo),x),xu,xn),(y,my)=>{
          const yc=into(cp,y,ai(app(ue(xu,y),al(my)),ei(predicate(y),x,ai(xa,my))));
          const unique=ui(z=>ii(C(M(z,x),M(z,c)),zp=>{
            const chosen=ar(from(cp,z,ar(zp)));
            return open(chosen,(t,tp)=>{
              const ta=al(tp),mz=ar(tp);
              const xt=dn(ii(N(Q(x,t)),different=>{
                const dis=app(us(ar(family),x,t),ai(ai(xa,ta),different));
                return app(app(ue(dis,z),al(zp)),al(mz));
              }));
              const mzx=eqSub(sym(xt),v=>minimum(v,lt,z),mz);
              const minUnique=app(us(imported(proofs.well_order_minimum_unique),u,r,x),ar(al(wo)),xu);
              return app(us(minUnique,y,z),my,mzx);
            });
          }));
          const goal=E(y=>C(C(M(y,x),M(y,c)),A(z=>I(C(M(z,x),M(z,c)),Q(z,y)))));
          return ei(goal,y,ai(ai(al(my),yc),unique));
        });
      }));
      return ei(Selected(a),c,each);
    });
  })))))));

  return {proofs,formulas:{
    least_code:db(Min('a','r','f','x','c'),['a','r','f','x','c']),
    well_order:db(WO('a',(x,y)=>V('r',x,y)),['a','r']),
    functional:db(Func('a','f'),['a','f']),
    surjective:db(Surj('a','b','f'),['a','b','f']),
    induced:db(Out('a','b','r','f','x','y'),['a','b','r','f','x','y']),
    choice_antecedent:db(C(FamilyNE('a'),Disjoint('a')),['a']),
    selected_set:db(Selected('a'),['a'])
  }};
}

export { buildWellOrder };
