import { pathToFileURL } from "node:url";
import { definition } from './constructible_definition.mjs';
import { kernel, same, inst, classProofs, compile, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
function buildF(defs,extended=false){
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

  function withUnaryGraph(i,x,n,nn,inj,fn){
    return withPair(i,x,(p,pp)=>withSingleton(p,(s,sp)=>{
      const Val=(a,b)=>form("val",s,a,b);
      const pv=ei(Val(i,x),p,ai(into(sp,p,ref(p)),pp));
      function classify(a,b,v){
        return open(v,(w,ww)=>app(us(inj,p,a,b,i,x),eqSub(from(sp,w,al(ww)),z=>form("pair",z,a,b),ar(ww)),pp));
      }
      const graph=ai(ui(w=>ii(M(w,s),ws=>{
        const goal=E(a=>C(M(a,n),E(b=>form("pair",w,a,b))));
        return ei(goal,i,ai(into(nn,i,ref(i)),ei(replace(goal[2][2],goal[1],i),x,eqSub(sym(from(sp,w,ws)),z=>form("pair",z,i,x),pp))));
      })),ui(a=>ii(M(a,n),an=>{
        const goal=E(b=>C(Val(a,b),A(c=>I(Val(a,c),Q(c,b)))));
        const av=eqSub(sym(from(nn,a,an)),z=>Val(z,x),pv);
        const uniq=ui(c=>ii(Val(a,c),vc=>ar(classify(a,c,vc))));
        return ei(goal,x,ai(av,uniq));
      })));
      return use(graph,g=>use(pv,v=>fn(s,g,v)));
    }));
  }
  const unaryGraph=use(pairInjective,inj=>qs(3,(i,x,n)=>ii(form("singleton",n,i),nn=>{
    const goal=E(s=>C(form("graph",s,n),form("val",s,i,x)));
    return withUnaryGraph(i,x,n,nn,inj,(s,g,v)=>ei(goal,s,ai(g,v)));
  })));

  function emptyEq(a,b,ea,eb){
    return app(us(ax({name:"extensionality"}),a,b),ui(x=>ai(ii(M(x,a),m=>fe(app(ue(ea,x),m),M(x,b))),ii(M(x,b),m=>fe(app(ue(eb,x),m),M(x,a))))));
  }
  function extEq(a,b,fn){return app(us(ax({name:"extensionality"}),a,b),ui(fn));}
  function succUnique(a,b,c,sb,sc){
    return extEq(b,c,x=>ai(ii(M(x,b),m=>into(sc,x,from(sb,x,m))),ii(M(x,c),m=>into(sb,x,from(sc,x,m)))));
  }
  const omegaExists= open(ax({name:"infinity"}),(a,indA)=>{
    const property=x=>A(b=>I(form("inductive",b),M(x,b)));
    const v=fresh(),sep={name:"separation",params:0,body:db(property(v),[v])};
    return open(ue(ax(sep),a),(w,sw)=>{
      const base=open(al(indA),(z,ez)=>{
        const all=ui(b=>ii(form("inductive",b),ib=>{
          return open(al(ib),(y,ey)=>eqSub(emptyEq(y,z,ar(ey),al(ez)),t=>M(t,b),al(ey)));
        }));
        const wz=into(sw,z,ai(ar(ez),all));
        return ei(form("inductive",w)[1],z,ai(wz,al(ez)));
      });
      const step=ui(x=>ii(M(x,w),xw=>{
        const xa=al(from(sw,x,xw)),allX=ar(from(sw,x,xw));
        return open(app(ue(ar(indA),x),xa),(y,sy)=>{
          const all=ui(b=>ii(form("inductive",b),ib=>{
            const xb=app(ue(allX,b),ib);
            return open(app(ue(ar(ib),x),xb),(z,sz)=>eqSub(succUnique(x,z,y,ar(sz),ar(sy)),t=>M(t,b),al(sz)));
          }));
          const yw=into(sw,y,ai(al(sy),all));
          const st=form("inductive",w)[2];
          return ei(replace(st[2][2],st[1],x),y,ai(yw,ar(sy)));
        });
      }));
      const least=ui(b=>ii(form("inductive",b),ib=>ui(x=>ii(M(x,w),xw=>app(ue(ar(from(sw,x,xw)),b),ib)))));
      const goal=E(w=>form("omega",w));
      return ei(goal,w,ai(ai(base,step),least));
    });
  });
  function withOrdinals(ow,w,fn){
    return open(al(al(ow)),(z,ez)=>{
      const zw=al(ez),zero=ar(ez);
      return open(app(ue(ar(al(ow)),z),zw),(o,so)=>{
        const ow0=al(so),su0=ar(so);
        const zo=into(su0,z,or(M(z,z),ref(z)));
        const single=ui(i=>ai(ii(M(i,o),io=>oe(from(su0,i,io),Q(i,z),iz=>fe(app(ue(zero,i),iz),Q(i,z)),q=>q)),ii(Q(i,z),q=>into(su0,i,or(M(i,z),q)))));
        const distinct=ii(Q(z,o),eq=>app(ue(zero,z),eqSub(sym(eq),t=>M(z,t),zo)));
        return open(app(ue(ar(al(ow)),o),ow0),(n,sn)=>{
          const su1=ar(sn);
          const two=ui(i=>ai(ii(M(i,n),iv=>oe(from(su1,i,iv),["|",Q(i,z),Q(i,o)],io=>ol(from(single,i,io),Q(i,o)),q=>or(Q(i,z),q))),
            ii(["|",Q(i,z),Q(i,o)],alt=>into(su1,i,oe(alt,["|",M(i,o),Q(i,o)],q=>ol(into(single,i,q),Q(i,o)),q=>or(M(i,o),q))))));
          const zn=into(two,z,ol(ref(z),Q(z,o))),on=into(two,o,or(Q(o,z),ref(o)));
          const ne0=ei(E(i=>M(i,o)),z,zo),ne1=ei(E(i=>M(i,n)),z,zn);
          return use(single,ss=>use(two,tt=>use(distinct,ne=>fn({w,z,o,n,zero,zw,ow0,nw:al(sn),su0,su1,ss,tt,ne,zo,zn,on,ne0,ne1}))));
        });
      });
    });
  }
  const finiteOrdinals=use(omegaExists,owEx=>open(owEx,(w,ow)=>withOrdinals(ow,w,a=>{
    const {z,o,n}=a;
    const body=(w,z,o,n)=>C(C(C(C(C(form("omega",w),form("empty",z)),form("singleton",o,z)),form("unordered",n,z,o)),N(Q(z,o))),C(M(o,w),M(n,w)));
    const goal=E(w=>E(z=>E(o=>E(n=>body(w,z,o,n)))));
    const g1=replace(goal[2],goal[1],w),g2=replace(g1[2],g1[1],z),g3=replace(g2[2],g2[1],o);
    return ei(goal,w,ei(g1,z,ei(g2,o,ei(g3,n,ai(ai(ai(ai(ai(ow,a.zero),a.ss),a.tt),a.ne),ai(a.ow0,a.nw))))));
  })));

  function valueUnique(g,s,i,im,x,y,vx,vy){
    return open(app(ue(ar(g),i),im),(v,uv)=>{
      return chain(app(ue(ar(uv),x),vx),sym(app(ue(ar(uv),y),vy)));
    });
  }
  function withPower(a,fn){return open(ue(ax({name:"power"}),a),fn);}
  function withUnion(a,fn){return open(ue(ax({name:"union"}),a),fn);}
  function withRelation(a,n,i,j,fn){
    return withSetPair(a,n,(an,anp)=>withUnion(an,(b,bp)=>{
      const ain=into(anp,a,ol(ref(a),Q(a,n)));
      const nin=into(anp,n,or(Q(n,a),ref(n)));
      const intoB=(x,t,tm,xm)=>{
        const goal=ar(ue(bp,x)).goal[1];
        return into(bp,x,ei(goal,t,ai(tm,xm)));
      };
      return withPower(b,(p1,p1p)=>withPower(p1,(p2,p2p)=>withPower(p2,(p3,p3p)=>{
        function bound(s,tuple){
          return into(p3p,s,ui(p=>ii(M(p,s),ps=>{
            return open(app(ue(al(al(tuple)),p),ps),(l,li)=>{
              return open(ar(li),(y,py)=>{
                return open(app(ue(ar(tuple),l),al(li)),(v,vy)=>{
                  const lv=ei(form("val",s,l,y),p,ai(ps,py));
                  const eq=valueUnique(al(tuple),s,l,al(li),v,y,ar(vy),lv);
                  const ya=eqSub(eq,z=>M(z,a),al(vy));
                  const lb=intoB(l,n,nin,al(li)),yb=intoB(y,a,ain,ya);
                  return unpack(py,(u,w,up,wp,pp)=>{
                    const u1=into(p1p,u,ui(z=>ii(M(z,u),zu=>eqSub(sym(from(up,z,zu)),t=>M(t,b),lb))));
                    const w1=into(p1p,w,ui(z=>ii(M(z,w),zw=>oe(from(wp,z,zw),M(z,b),e=>eqSub(sym(e),t=>M(t,b),lb),e=>eqSub(sym(e),t=>M(t,b),yb)))));
                    return into(p2p,p,ui(z=>ii(M(z,p),zp=>oe(from(pp,z,zp),M(z,p1),e=>eqSub(sym(e),t=>M(t,p1),u1),e=>eqSub(sym(e),t=>M(t,p1),w1)))));
                  });
                });
              });
            });
          })));
        }
        const dummy=fresh();
        function condition(s){
          const g=form("relMem",dummy,n,a,i,j);
          return replace(g[2][1][2],g[1],s);
        }
        const v=fresh(),ps=[n,a,i,j],spec={name:"separation",params:ps.length,body:db(condition(v),[v,...ps])};
        const sep=us(ax(spec),...ps.slice().reverse(),p3);
        return open(sep,(r,rp)=>{
          const exact=ui(s=>ai(ii(M(s,r),sr=>ar(from(rp,s,sr))),ii(condition(s),cp=>into(rp,s,ai(bound(s,al(cp)),cp)))));
          return use(exact,re=>fn(r,re));
        });
      })));
    }));
  }
  const relationExists=qs(4,(a,n,i,j)=>withRelation(a,n,i,j,(r,rp)=>ei(E(r=>form("relMem",r,n,a,i,j)),r,rp)));

  function withTuple(a,n,z,o,u,v,tt,ne,inj,ua,va,fn){
    return withBinaryGraph(z,o,u,v,n,tt,ne,inj,(s,g,vz,vo)=>{
      const Val=(i,x)=>form("val",s,i,x);
      const range=ui(i=>ii(M(i,n),inN=>{
        const goal=E(x=>C(M(x,a),Val(i,x)));
        return oe(from(tt,i,inN),goal,
          iz=>ei(goal,u,ai(ua,eqSub(sym(iz),j=>Val(j,u),vz))),
          io=>ei(goal,v,ai(va,eqSub(sym(io),j=>Val(j,v),vo))));
      }));
      return use(ai(g,range),tu=>fn(s,tu,vz,vo));
    });
  }
  function proveAgree(s,b,n,z,o,x,tt,on,ne,st,bt,so,bo){
    const S=(i,v)=>form("val",s,i,v),Bv=(i,v)=>form("val",b,i,v);
    return ui(j=>ii(M(j,n),jn=>ii(N(Q(z,j)),neq=>ui(v=>{
      const goal=B(S(j,v),Bv(j,v));
      return oe(from(tt,j,jn),goal,jz=>fe(app(neq,sym(jz)),goal),jo=>{
        function transfer(st,sp,fromVal,toVal,toP,p){
          const vo=eqSub(jo,i=>fromVal(i,v),p);
          const eq=valueUnique(al(st),s,o,on,x,v,sp,vo);
          return eqSub(sym(jo),i=>toVal(i,v),eqSub(eq,t=>toVal(o,t),toP));
        }
        const left=ii(S(j,v),p=>transfer(st,so,S,Bv,bo,p));
        const right=ii(Bv(j,v),p=>transfer(bt,bo,Bv,S,so,p));
        return ai(left,right);
      });
    }))));
  }
  function proveSlice(a,x,r,n,z,o,b,tt,zn,on,ne,ta,xa,bt,bo,rp,inj){
    return ui(y=>{
      const target=form("slice",x,r,a,n,z,b);
      const g=replace(target[2],target[1],y);
      const witness=g[1][2][2];
      const left=ii(M(y,x),yx=>{
        const ya=app(ue(app(ue(ta,x),xa),y),yx);
        return withTuple(a,n,z,o,y,x,tt,ne,inj,ya,xa,(s,st,sz,so)=>{
          const atomCond=ar(ue(rp,s)).goal[1];
          const prop=atomCond[2];
          const propY=replace(prop[2],prop[1],y);
          const propX=propY[2];
          const rel=ei(prop,y,ai(ya,ei(propX,x,ai(xa,ai(ai(sz,so),yx)))));
          const sr=into(rp,s,ai(st,rel));
          const ag=proveAgree(s,b,n,z,o,x,tt,on,ne,st,bt,so,bo);
          return ai(ya,ei(witness,s,ai(sr,ai(sz,ag))));
        });
      });
      const right=ii(g[2][1],p=>{
        return open(ar(p),(s,sw)=>{
          const sr=al(sw),sz=al(ar(sw)),ag=ar(ar(sw));
          const cond=from(rp,s,sr),st=al(cond),pr=ar(cond);
          return open(pr,(u,up)=>open(ar(up),(v,vp)=>{
            const zv=al(al(ar(vp))),ov=ar(al(ar(vp))),uv=ar(ar(vp));
            const uy=valueUnique(al(st),s,z,zn,u,y,zv,sz);
            const agO=app(ue(ag,o),on,ne);
            const bv=app(al(ue(agO,v)),ov);
            const vx=valueUnique(al(bt),b,o,on,v,x,bv,bo);
            return eqSub(vx,t=>M(y,t),eqSub(uy,t=>M(t,v),uv));
          }));
        });
      });
      return ai(left,right);
    });
  }
  function entryProof(f,z,r,n,a,o,zn,on,rp){
    const g=form("entry",f,z,r,n,a),am=g[1][1][1][2];
    const inn=replace(am[2],am[1],z)[2];
    const p=ei(am,z,ai(zn,ei(inn,o,ai(on,rp))));
    return ol(ol(ol(or(g[1][1][1][1],p),g[1][1][2]),g[1][2]),g[2]);
  }
  function atomicWitness(a,x,ta,xa,inj,owEx,relEx){
    return open(owEx,(w,ow)=>withOrdinals(ow,w,ords=>{
      const {z,o,n,zero,ow0,nw,su0,ss,tt,ne,zo,zn,on,ne0,ne1}=ords;
      return open(us(relEx,a,n,z,o),(r,rp)=>{
        return withTuple(a,n,z,o,x,x,tt,ne,inj,xa,xa,(b,bt,bz,bo)=>{
          return withUnaryGraph(z,r,o,ss,inj,(f,fg,fz)=>{
            const goal=D(a,x),owGoal=goal[2];
            const owBody=replace(owGoal[2],owGoal[1],w);
            const nGoal=owBody[2],nBody=replace(nGoal[2],nGoal[1],n);
            const mGoal=nBody[2],mBody=replace(mGoal[2],mGoal[1],o);
            const fGoal=mBody[2][2],fBody=replace(fGoal[2],fGoal[1],f);
            const ep=entryProof(f,z,r,n,a,o,zn,on,rp);
            const allK=ui(j=>ii(M(j,o),jo=>{
              const jz=from(ss,j,jo);
              const goal=E(r=>C(form("val",f,j,r),form("entry",f,j,r,n,a)));
              const value=eqSub(sym(jz),k=>C(form("val",f,k,r),form("entry",f,k,r,n,a)),ai(fz,ep));
              return ei(goal,r,value);
            }));
            const valid=ai(fg,allK);
            const ls=fBody[2],lsBody=replace(ls[2],ls[1],z);
            const rGoal=lsBody[2][2],rBody=replace(rGoal[2],rGoal[1],r);
            const zGoal=rBody[2],zBody=replace(zGoal[2],zGoal[1],z);
            const bGoal=zBody[2][2];
            const slice=proveSlice(a,x,r,n,z,o,b,tt,zn,on,ne,ta,xa,bt,bo,rp,inj);
            const base=ei(bGoal,b,ai(bt,slice));
            const atZero=ei(zGoal,z,ai(zn,ai(zero,base)));
            const atR=ei(rGoal,r,ai(fz,atZero));
            const last=ei(ls,z,ai(zo,ai(su0,atR)));
            const pF=ei(fGoal,f,ai(valid,last));
            const pM=ei(mGoal,o,ai(ow0,ai(ai(ne1,ne0),pF)));
            const pN=ei(nGoal,n,ai(nw,pM));
            return or(goal[1],ei(owGoal,w,ai(ow,pN)));
          });
        });
      });
    }));
  }
  const atomicDef=use(pairInjective,inj=>use(omegaExists,ow=>use(relationExists,re=>{
    return ui(a=>ii(trans(a),ta=>ui(x=>ii(M(x,a),xa=>atomicWitness(a,x,ta,xa,inj,ow,re)))));
  })));
  const defInflation=use(atomicDef,ad=>qs(2,(a,b)=>ii(Def(a,b),dd=>ii(trans(a),ta=>{
    return ui(x=>ii(M(x,a),xa=>into(dd,x,app(ue(app(ue(ad,a),ta),x),xa))));
  }))));
  const proofs={pair_exists:pairExists,pair_injective:pairInjective,binary_graph_exists:binaryGraph,unary_graph_exists:unaryGraph,omega_exists:omegaExists,finite_ordinals:finiteOrdinals,membership_relation_exists:relationExists,atomic_member_definable:atomicDef,def_inflation:defInflation};

  if(extended){
    function definableSubset(a,x,d){
      return ui(y=>ii(M(y,x),mem=>{
        const goal=M(y,a);
        function follow(p,path){
          if(!path.length)return al(ie(al(ue(p,y)),mem));
          const [step,...tail]=path;
          if(step==="l")return follow(al(p),tail);
          if(step==="r")return follow(ar(p),tail);
          return ee(p,goal,(_,q)=>follow(q,tail));
        }
        return oe(d,goal,p=>fe(app(ue(p,y),mem),goal),
          p=>follow(p,["e","r","e","r","e","r","r","e","r","e","r","r","e","r","e","r","r","e","r"]));
      }));
    }
    function emptyDef(z,o,ez,os){
      return ui(x=>ai(ii(M(x,o),mx=>{
        const xz=from(os,x,mx);
        const ex=eqSub(sym(xz),t=>Empty(t),ez);
        return ol(ex,D(z,x)[2]);
      }),ii(D(z,x),dx=>{
        const sub=definableSubset(z,x,dx);
        const ex=ui(y=>ii(M(y,x),yx=>app(ue(ez,y),app(ue(sub,y),yx))));
        return into(os,x,emptyEq(x,z,ex,ez));
      })));
    }
    const defZero=qs(2,(z,o)=>ii(Empty(z),ez=>ii(form("singleton",o,z),os=>emptyDef(z,o,ez,os))));
    function stageZero(f,z,ez){
      const st=form("stage",f,z,z),limit=st[2][1],union=st[2][2];
      const noPred=ii(limit[1],p=>open(p,(_,w)=>app(ue(ez,w.goal[1][1]),al(w))));
      const limitVal=ui(x=>{
        const u=replace(union[2],union[1],x),ex=u[2][1];
        const left=ii(M(x,z),xz=>fe(app(ue(ez,x),xz),ex));
        const right=ii(ex,p=>open(p,(i,w)=>fe(app(ue(ez,i),al(w)),M(x,z))));
        return ai(left,right);
      });
      return or(st[1],ai(noPred,limitVal));
    }
    function stageOne(f,z,o,zo,su0,vz,def0){
      const st=form("stage",f,o,o),sc=st[1];
      const sBody=replace(sc[2],sc[1],z),sEx=sBody[2][2];
      return ol(ei(sc,z,ai(zo,ai(su0,ei(sEx,z,ai(vz,def0))))),st[2]);
    }
    function ordOne(z,o,ez,os){
      const tr=ui(x=>ii(M(x,o),xo=>ui(y=>ii(M(y,x),yx=>{
        const xz=from(os,x,xo);
        return fe(app(ue(ez,y),eqSub(xz,t=>M(y,t),yx)),M(y,o));
      }))));
      const each=ui(x=>ii(M(x,o),xo=>ui(y=>ii(M(y,x),yx=>ui(v=>ii(M(v,y),vy=>{
        return fe(app(ue(ez,y),eqSub(from(os,x,xo),t=>M(y,t),yx)),M(v,x));
      }))))));
      return ai(tr,each);
    }
    function graphZero(z,o,ez,os,inj,fn){
      return withUnaryGraph(z,z,o,os,inj,(f,g,vz)=>{
        const s0=stageZero(f,z,ez);
        const steps=ui(i=>ii(M(i,o),io=>{
          const iz=from(os,i,io);
          const goal=E(r=>C(form("val",f,i,r),form("stage",f,i,r)));
          const pr=eqSub(sym(iz),t=>C(form("val",f,t,z),form("stage",f,t,z)),ai(vz,s0));
          return ei(goal,z,pr);
        }));
        return use(ai(g,steps),sg=>fn(f,sg,vz));
      });
    }
    function graphOne(z,o,n,ez,os,nn,ne,su0,inj,fn){
      const zo=into(os,z,ref(z)),def0=emptyDef(z,o,ez,os);
      return withBinaryGraph(z,o,z,o,n,nn,ne,inj,(f,g,vz,vo)=>{
        return use(def0,d0=>{
          const s0=stageZero(f,z,ez),s1=stageOne(f,z,o,zo,su0,vz,d0);
          const steps=ui(i=>ii(M(i,n),inN=>{
            const goal=E(r=>C(form("val",f,i,r),form("stage",f,i,r)));
            return oe(from(nn,i,inN),goal,
              iz=>ei(goal,z,eqSub(sym(iz),t=>C(form("val",f,t,z),form("stage",f,t,z)),ai(vz,s0))),
              io=>ei(goal,o,eqSub(sym(io),t=>C(form("val",f,t,o),form("stage",f,t,o)),ai(vo,s1))));
          }));
          return use(ai(g,steps),sg=>fn(f,sg,vz,vo));
        });
      });
    }
    const stageZeroProof=qs(2,(f,z)=>ii(Empty(z),ez=>stageZero(f,z,ez)));
    const graph0=use(pairInjective,inj=>qs(2,(z,o)=>ii(Empty(z),ez=>ii(form("singleton",o,z),os=>{
      const goal=E(f=>C(form("stageGraph",f,o),form("val",f,z,z)));
      return graphZero(z,o,ez,os,inj,(f,sg,vz)=>ei(goal,f,ai(sg,vz)));
    }))));
    const graph1=use(pairInjective,inj=>qs(3,(z,o,n)=>ii(Empty(z),ez=>ii(form("singleton",o,z),os=>ii(form("unordered",n,z,o),nn=>ii(N(Q(z,o)),ne=>ii(form("successor",z,o),su0=>{
      const goal=E(f=>C(C(form("stageGraph",f,n),form("val",f,z,z)),form("val",f,o,o)));
      return graphOne(z,o,n,ez,os,nn,ne,su0,inj,(f,sg,vz,vo)=>ei(goal,f,ai(ai(sg,vz),vo)));
    })))))));
    const lEmpty=use(pairInjective,inj=>use(omegaExists,owEx=>ui(x=>ii(Empty(x),ex=>{
      const goal=form("L",x);
      return open(owEx,(w,ow)=>withOrdinals(ow,w,a=>{
        const {z,o,n,zero,ss,tt,ne,su0,su1}=a;
        const ord=ordOne(z,o,zero,ss);
        const xo=into(ss,x,emptyEq(x,z,ex,zero));
        return graphOne(z,o,n,zero,ss,tt,ne,su0,inj,(f,sg,vz,vo)=>{
          const aBody=replace(goal[2],goal[1],o),dGoal=aBody[2];
          const dBody=replace(dGoal[2],dGoal[1],n),fGoal=dBody[2];
          const fBody=replace(fGoal[2],fGoal[1],f),rGoal=fBody[2];
          return ei(goal,o,ai(ord,ei(dGoal,n,ai(su1,ei(fGoal,f,ai(sg,ei(rGoal,o,ai(vo,xo))))))));
        });
      }));
    }))));
    const lNonempty=use(lEmpty,le=>open(ax({name:"empty"}),(z,ez)=>{
      const goal=E(x=>C(form("L",x),Empty(x)));
      return ei(goal,z,ai(app(ue(le,z),ez),ez));
    }));
    Object.assign(proofs,{def_zero_singleton:defZero,zero_stage_rule:stageZeroProof,zero_stage_graph:graph0,one_stage_graph:graph1,L_empty:lEmpty,L_contains_empty:lNonempty});
  }
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}


function runF(){
  const defs=definition("v",true),proofs=buildF(defs),earlier=buildE(defs),out={};
  function check(name,p,guard=false,def=null){
    const checked=kernel(0,[],p.proof,guard,"ZF",def);
    if(!same(checked.goal,p.goal))throw Error("goal mismatch "+name);
    out[name]={nodes:checked.visits,proof_bytes:JSON.stringify(p.proof).length};
  }
  for(const [name,p] of Object.entries(proofs))check(name,p);
  const infl=proofs.def_inflation;
  const conditional=earlier.L_transitivity_conditional;
  if(!same(infl.goal,conditional.goal[1]))throw Error("inflation target mismatch");
  const stage=earlier.stage_transitivity_conditional;
  if(!same(infl.goal,stage.goal[1]))throw Error("stage target mismatch");
  const stageP={goal:stage.goal[2],proof:["iE",stage.proof,infl.proof]};
  const lP={goal:conditional.goal[2],proof:["iE",conditional.proof,infl.proof]};
  const exactL=["A",[">",defs.L,["A",[">",["M",0,1],defs.L]]]];
  if(!same(exactL,lP.goal))throw Error("exact L transitivity target mismatch");
  check("stage_transitivity",stageP);
  check("L_transitivity",lP);
  const c=classProofs(),T=c.generic.find(x=>x.name==="extensionality").premises[0];
  const px=["conv",inst(defs.L,1),["aL",["h",0]]];
  const sx=["iE",["uE",["closed",lP.proof],1],px];
  const sy=["iE",["uE",sx,0],["aR",["h",0]]];
  const tP={goal:T,proof:["uI",["uI",["iI",["&",["G",1],["M",0,1]],["conv",["G",0],sy]]]]};
  check("L_transitivity_guard",tP,true,defs.L);
  const certs=[];
  for(const name of ["extensionality","foundation"]){
    const g=c.generic.find(x=>x.name===name),spec={name};
    if(g.premises.length!==1||!same(T,g.premises[0]))throw Error("wrong generic closure premise");
    const proof=["iE",g.proof,tP.proof];
    check("L_"+name,{goal:c.goal(name),proof},true,defs.L);
    certs.push({spec,proof});
  }
  const opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:certs};
  const composite=["aI",...certs.map(c=>["axiom",c.spec])];
  const compiled=compile(0,[],composite,opts);
  if(!same(compiled.target.goal,["&",...certs.map(x=>c.goal(x.spec.name))]))throw Error("compiler goal");
  let rejected=0;
  const controls=[
    ()=>kernel(0,[],conditional.proof[2],false,"ZF"),
    ()=>kernel(0,[],["iE",conditional.proof,proofs.pair_exists.proof],false,"ZF"),
    ()=>kernel(0,[],infl.proof,false,"CL"),
    ()=>kernel(0,[],tP.proof,true,c.def),
    ()=>compile(0,[],["axiom",{name:"choice"}],opts),
    ()=>compile(0,[],["axiom",{name:"pairing"}],opts),
    ()=>compile(0,[],["axiom",{name:"empty"}],opts)
  ];
  // Wrong class must be checked using ZF policy and the actual alternate definition.
  controls[3]=()=>kernel(0,[],tP.proof,true,"ZF",c.def);
  for(const fn of controls){if(!rejects(fn))throw Error("negative control passed");rejected++;}
  return {experiment:"ACE-03F",scope:"closed object proofs for pinned L predicate, checked by executable ZF kernel",proofs:out,closed_L_axiom_certificates:certs.map(c=>c.spec.name),composite_source_nodes:compiled.source.visits,composite_target_nodes:compiled.target.visits,negative_controls:rejected,remaining:"adequacy, stage recursion and other L axioms; proof checker soundness"};
}

export { buildF };
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(runF(),null,2));
