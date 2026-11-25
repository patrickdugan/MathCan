import { definition } from './constructible_definition.mjs';
import { kernel, same } from './zf_interface.mjs';
function buildF(defs){
  let serial=0;
  const fresh=()=>`q${serial++}`,M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b],F=["F"],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],N=p=>I(p,F);
  const bind=(op,f)=>{const x=fresh();return [op,x,f(x)];};
  const A=f=>bind("A",f),E=f=>bind("E",f);
  function named(p,env){
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="M"||op==="=")return [op,env[a],env[b]];
    if(op==="A"||op==="E"){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env){
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="M"||op==="="){
      const i=env.indexOf(a),j=env.indexOf(b);if(i<0||j<0)throw Error("unbound proof variable "+a+" "+b);
      return [op,i,j];
    }
    if(op==="A"||op==="E")return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }
  function replace(p,x,y){
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="M"||op==="=")return [op,a===x?y:a,b===x?y:b];
    if(op==="A"||op==="E"){
      if(a===x)return p;
      if(a===y){const z=fresh();return [op,z,replace(replace(b,a,z),x,y)];}
      return [op,a,replace(b,x,y)];
    }
    return [op,replace(a,x,y),replace(b,x,y)];
  }
  const P=(goal,emit)=>({goal,emit});
  function assume(goal){
    const id=fresh();
    return {id,p:P(goal,(_,h)=>{const i=h.indexOf(id);if(i<0)throw Error("unbound hypothesis");return ["h",i];})};
  }
  function ui(fn){const x=fresh(),p=fn(x);return P(["A",x,p.goal],(e,h)=>["uI",p.emit([x,...e],h)]);}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>["iI",db(g,e),p.emit(e,[...h,a.id])]);}
  const al=p=>P(p.goal[1],(e,h)=>["aL",p.emit(e,h)]);
  const ar=p=>P(p.goal[2],(e,h)=>["aR",p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>["aI",p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>["iE",p.emit(e,h),q.emit(e,h)]);
  function ue(p,x){return P(replace(p.goal[2],p.goal[1],x),(e,h)=>["uE",p.emit(e,h),e.indexOf(x)]);}
  const fe=(p,g)=>P(g,(e,h)=>["fE",p.emit(e,h),db(g,e)]);
  function ee(p,g,fn){
    if(p.goal[0]!=="E")throw Error("expected E got "+p.goal[0]);
    const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
    return P(g,(e,h)=>["eE",p.emit(e,h),db(g,e),q.emit([x,...e],[...h,a.id])]);
  }
  function ei(g,x,p){return P(g,(e,h)=>["eI",db(g[2],[g[1],...e]),e.indexOf(x),p.emit(e,h)]);}
  function oe(p,g,left,right){
    const a=assume(p.goal[1]),b=assume(p.goal[2]),l=left(a.p),r=right(b.p);
    return P(g,(e,h)=>["oE",p.emit(e,h),l.emit(e,[...h,a.id]),r.emit(e,[...h,b.id])]);
  }
  const ol=(p,g)=>P(["|",p.goal,g],(e,h)=>["oL",p.emit(e,h),db(g,e)]);
  const subset=(a,b)=>A(x=>I(M(x,a),M(x,b)));
  const trans=a=>A(x=>I(M(x,a),subset(x,a)));
  const D=(a,x)=>named(defs.definable,[a,x]);
  const Def=(a,b)=>named(defs.Def,[a,b]);
  const Empty=x=>named(defs.empty,[x]);

  const ax=spec=>P(named(kernel(0,[],["axiom",spec],false,"ZF").goal,[]),()=>["axiom",spec]);
  const dn=p=>P(p.goal[1][1],(e,h)=>["dne",p.emit(e,h)]);
  const or=(g,p)=>P(["|",g,p.goal],(e,h)=>["oR",db(g,e),p.emit(e,h)]);
  const ref=x=>P(Q(x,x),(e,h)=>["refl",e.indexOf(x)]);
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const us=(p,...xs)=>xs.reduce((q,x)=>ue(q,x),p);
  const app=(p,...args)=>args.reduce((q,a)=>ie(q,a),p);
  const form=(name,...args)=>named(defs[name],args);
  const B=(a,b)=>C(I(a,b),I(b,a));
  function eqSub(eq,prop,proof){
    const v=fresh(),g=prop(v);
    return P(replace(g,v,eq.goal[2]),(e,h)=>["eqS",db(g,[v,...e]),eq.emit(e,h),proof.emit(e,h)]);
  }
  const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  function use(p,fn){return ie(ii(p.goal,fn),p);}
  function open(p,fn){
    if(p.goal[0]!=="E")throw Error("expected exists, got "+p.goal[0]);
    const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
    return P(q.goal,(e,h)=>["eE",p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);
  }
  const from=(p,x,px)=>ie(al(ue(p,x)),px);
  const into=(p,x,px)=>ie(ar(ue(p,x)),px);
  function exintro(g,x,p){return ei(g,x,p);}
  function withSetPair(a,b,fn){return open(us(ax({name:"pairing"}),a,b),fn);}
  function withSingleton(a,fn){
    return withSetPair(a,a,(s,sp)=>{
      const proof=ui(x=>ai(ii(M(x,s),xs=>oe(from(sp,x,xs),Q(x,a),q=>q,q=>q)),
        ii(Q(x,a),q=>into(sp,x,ol(q,Q(x,a))))));
      return use(proof,single=>fn(s,single));
    });
  }
  function withPair(a,b,fn){
    return withSingleton(a,(u,up)=>withSetPair(a,b,(v,vp)=>withSetPair(u,v,(p,pp)=>{
      const g=form("pair",p,a,b),inner=replace(g[2],g[1],u);
      const proof=ei(g,u,ei(inner,v,ai(ai(up,vp),pp)));
      return use(proof,pr=>fn(p,pr));
    })));
  }
  const pairExists=qs(2,(a,b)=>withPair(a,b,(p,pr)=>ei(E(x=>form("pair",x,a,b)),p,pr)));
  function unpack(p,fn){
    return open(p,(u,up)=>open(up,(v,both)=>fn(u,v,al(al(both)),ar(al(both)),ar(both))));
  }
  const pairInjective=qs(5,(p,a,b,c,d)=>ii(form("pair",p,a,b),ab=>ii(form("pair",p,c,d),cd=>{
    return unpack(ab,(u,v,up,vp,pp)=>unpack(cd,(w,t,wp,tp,qq)=>{
      const uIn=into(pp,u,ol(ref(u),Q(u,v)));
      const vIn=into(pp,v,or(Q(v,u),ref(v)));
      const wIn=into(qq,w,ol(ref(w),Q(w,t)));
      const tIn=into(qq,t,or(Q(t,w),ref(t)));
      const au=into(up,a,ref(a)),av=into(vp,a,ol(ref(a),Q(a,b)));
      const bv=into(vp,b,or(Q(b,a),ref(b)));
      const dt=into(tp,d,or(Q(d,c),ref(d)));
      const ac=from(wp,a,oe(from(pp,w,wIn),M(a,w),
        wu=>eqSub(sym(wu),z=>M(a,z),au),
        wv=>eqSub(sym(wv),z=>M(a,z),av)));
      const bcd=oe(from(qq,v,vIn),["|",Q(b,c),Q(b,d)],
        vw=>ol(from(wp,b,eqSub(vw,z=>M(b,z),bv)),Q(b,d)),
        vt=>from(tp,b,eqSub(vt,z=>M(b,z),bv)));
      const dab=oe(from(pp,t,tIn),["|",Q(d,a),Q(d,b)],
        tu=>ol(from(up,d,eqSub(tu,z=>M(d,z),dt)),Q(d,b)),
        tv=>from(vp,d,eqSub(tv,z=>M(d,z),dt)));
      const bd=oe(bcd,Q(b,d),bc=>oe(dab,Q(b,d),
        da=>chain(chain(bc,sym(ac)),sym(da)),db=>sym(db)),q=>q);
      return ai(ac,bd);
    }));
  })));
  // A two-element set of distinct indices; actual function graph is
  // built by Pairing applied to two Kuratowski pairs. The same proof
  // works when values coincide.
  function withBinaryGraph(i,j,x,y,n,nn,distinct,inj,fn){
    return withPair(i,x,(p,pp)=>withPair(j,y,(q,qp)=>withSetPair(p,q,(s,sp)=>{
      const Val=(a,b)=>form("val",s,a,b);
      const V=(a,b,w,wp,inc)=>ei(Val(a,b),w,ai(inc,wp));
      const pv=V(i,x,p,pp,into(sp,p,ol(ref(p),Q(p,q))));
      const qv=V(j,y,q,qp,into(sp,q,or(Q(q,p),ref(q))));
      function classify(a,b,v){
        return open(v,(w,ww)=>{
          const eq=from(sp,w,al(ww));
          const goal=["|",C(Q(a,i),Q(b,x)),C(Q(a,j),Q(b,y))];
          return oe(eq,goal,
            z=>ol(app(us(inj,p,a,b,i,x),eqSub(z,t=>form("pair",t,a,b),ar(ww)),pp),goal[2]),
            z=>or(goal[1],app(us(inj,q,a,b,j,y),eqSub(z,t=>form("pair",t,a,b),ar(ww)),qp)));
        });
      }
      const graph=ai(ui(w=>ii(M(w,s),ws=>{
        const goal=E(a=>C(M(a,n),E(b=>form("pair",w,a,b))));
        return oe(from(sp,w,ws),goal,
          eq=>ei(goal,i,ai(into(nn,i,ol(ref(i),Q(i,j))),ei(replace(goal[2][2],goal[1],i),x,eqSub(sym(eq),t=>form("pair",t,i,x),pp)))),
          eq=>ei(goal,j,ai(into(nn,j,or(Q(j,i),ref(j))),ei(replace(goal[2][2],goal[1],j),y,eqSub(sym(eq),t=>form("pair",t,j,y),qp)))));
      })),ui(a=>ii(M(a,n),an=>{
        const goal=E(b=>C(Val(a,b),A(c=>I(Val(a,c),Q(c,b)))));
        function at(ia,b,v,first){
          const av=eqSub(sym(ia),z=>Val(z,b),v);
          const uniq=ui(c=>ii(Val(a,c),vc=>{
            return oe(classify(a,c,vc),Q(c,b),l=>first?ar(l):fe(app(distinct,chain(sym(ia),al(l))),Q(c,b)),
              r=>first?fe(app(distinct,chain(sym(ia),al(r))),Q(c,b)):ar(r));
          }));
          return ei(goal,b,ai(av,uniq));
        }
        // distinct has orientation i != j; second case uses symmetry.
        return oe(from(nn,a,an),goal,
          ia=>at(ia,x,pv,true),
          ja=>{
            const av=eqSub(sym(ja),z=>Val(z,y),qv);
            const uniq=ui(c=>ii(Val(a,c),vc=>oe(classify(a,c,vc),Q(c,y),
              l=>fe(app(distinct,chain(sym(al(l)),ja)),Q(c,y)),r=>ar(r))));
            return ei(goal,y,ai(av,uniq));
          });
      })));
      return use(graph,gg=>use(pv,v0=>use(qv,v1=>fn(s,gg,v0,v1))));
    })));
  }
  const binaryGraph=use(pairInjective,inj=>qs(5,(i,j,x,y,n)=>ii(form("unordered",n,i,j),nn=>ii(N(Q(i,j)),ne=>{
    const goal=E(s=>C(C(form("graph",s,n),form("val",s,i,x)),form("val",s,j,y)));
    return withBinaryGraph(i,j,x,y,n,nn,ne,inj,(s,g,v0,v1)=>ei(goal,s,ai(ai(g,v0),v1)));
  }))));
  const proofs={pair_exists:pairExists,pair_injective:pairInjective,binary_graph_exists:binaryGraph};
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
