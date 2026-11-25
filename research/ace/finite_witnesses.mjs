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
  function withTupleRelation(a,n,name,args,fn){
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
          const g=form(name,dummy,...args);
          return replace(g[2][1][2],g[1],s);
        }
        const v=fresh(),ps=args,spec={name:"separation",params:ps.length,body:db(condition(v),[v,...ps])};
        const sep=us(ax(spec),...ps.slice().reverse(),p3);
        return open(sep,(r,rp)=>{
          const exact=ui(s=>ai(ii(M(s,r),sr=>ar(from(rp,s,sr))),ii(condition(s),cp=>into(rp,s,ai(bound(s,al(cp)),cp)))));
          return use(exact,re=>fn(r,re));
        });
      })));
    }));
  }

  const withRelation=(a,n,i,j,fn)=>withTupleRelation(a,n,"relMem",[n,a,i,j],fn);
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


  if(extended==="relations"||extended==="infinity"||extended==="power"||(extended&&typeof extended==="object"&&extended.mode==="compiler")){
    function withAnd(p,q,fn){
      const x=fresh(),spec={name:"separation",params:1,body:db(M(x,q),[x,q])};
      return open(us(ax(spec),q,p),(r,rp)=>fn(r,rp));
    }
    const eqExists=qs(4,(a,n,i,j)=>withTupleRelation(a,n,"relEq",[n,a,i,j],(r,rp)=>ei(E(r=>form("relEq",r,n,a,i,j)),r,rp)));
    const negExists=qs(3,(a,n,p)=>withTupleRelation(a,n,"relNeg",[p,n,a],(r,rp)=>ei(E(r=>form("relNeg",r,p,n,a)),r,rp)));
    const andExists=qs(2,(p,q)=>withAnd(p,q,(r,rp)=>ei(E(r=>form("relAnd",r,p,q)),r,rp)));
    const exExists=qs(4,(a,n,p,i)=>withTupleRelation(a,n,"relEx",[p,n,a,i],(r,rp)=>ei(E(r=>form("relEx",r,p,n,a,i)),r,rp)));

    const Graph=(f,d)=>form("graph",f,d),Val=(f,i,r)=>form("val",f,i,r),Succ=(b,d)=>form("successor",b,d);
    const noSelf=ui(b=>ii(M(b,b),bb=>withSingleton(b,(s,sp)=>{
      const bs=into(sp,b,ref(b)),nonempty=ei(E(x=>M(x,s)),b,bs);
      return open(app(ue(ax({name:"foundation"}),s),nonempty),(x,xp)=>{
        const xb=from(sp,x,al(xp)),bx=eqSub(sym(xb),z=>M(b,z),bb);
        return app(app(ue(ar(xp),b),bx),bs);
      });
    })));
    const valDomain=use(pairInjective,inj=>qs(4,(f,d,i,r)=>ii(Graph(f,d),g=>ii(Val(f,i,r),v=>open(v,(p,pv)=>{
      return open(app(ue(al(g),p),al(pv)),(j,jp)=>open(ar(jp),(y,py)=>{
        const eq=al(app(us(inj,p,i,r,j,y),ar(pv),py));
        return eqSub(sym(eq),t=>M(t,d),al(jp));
      }));
    })))));
    function withAdjoin(a,b,fn){
      return withSingleton(b,(s,sp)=>withSetPair(a,s,(t,tp)=>withUnion(t,(u,up)=>{
        const ta=into(tp,a,ol(ref(a),Q(a,s))),ts=into(tp,s,or(Q(s,a),ref(s)));
        const proof=ui(x=>{
          const goal=["|",M(x,a),Q(x,b)];
          const left=ii(M(x,u),xu=>open(from(up,x,xu),(v,vp)=>oe(from(tp,v,al(vp)),goal,
            va=>ol(eqSub(va,z=>M(x,z),ar(vp)),Q(x,b)),vs=>or(M(x,a),from(sp,x,eqSub(vs,z=>M(x,z),ar(vp)))))));
          const right=ii(goal,p=>oe(p,M(x,u),xa=>into(up,x,ei(ar(ue(up,x)).goal[1],a,ai(ta,xa))),xb=>into(up,x,ei(ar(ue(up,x)).goal[1],s,ai(ts,into(sp,x,xb))))));
          return ai(left,right);
        });
        return use(proof,pr=>fn(u,pr));
      })));
    }
    const equiv=(f,g,b)=>A(i=>I(M(i,b),A(y=>B(Val(f,i,y),Val(g,i,y)))));
    function append(f,b,d,r,sd,g0,inj,dom,ns,fn){
      const nb=ue(ns,b);
      return withPair(b,r,(p,pp)=>withAdjoin(f,p,(g,gp)=>{
        const valCases=(i,y,v)=>open(v,(w,wp)=>{
          const goal=["|",Val(f,i,y),C(Q(i,b),Q(y,r))];
          return oe(from(gp,w,al(wp)),goal,
            wf=>ol(ei(Val(f,i,y),w,ai(wf,ar(wp))),goal[2]),
            eq=>or(goal[1],app(us(inj,p,i,y,b,r),eqSub(eq,t=>form("pair",t,i,y),ar(wp)),pp)));
        });
        const oldToNew=(i,y,v)=>open(v,(w,wp)=>ei(Val(g,i,y),w,ai(into(gp,w,ol(al(wp),Q(w,p))),ar(wp))));
        const newValue=ei(Val(g,b,r),p,ai(into(gp,p,or(M(p,f),ref(p))),pp));
        const oldEquiv=ui(i=>ii(M(i,b),ib=>ui(y=>ai(
          ii(Val(f,i,y),v=>oldToNew(i,y,v)),
          ii(Val(g,i,y),v=>oe(valCases(i,y,v),Val(f,i,y),q=>q,eq=>fe(app(nb,eqSub(al(eq),t=>M(t,b),ib)),Val(f,i,y))))))));
        return use(oldEquiv,eqv=>{
          const entries=ui(w=>ii(M(w,g),wg=>{
            const goal=E(i=>C(M(i,d),E(y=>form("pair",w,i,y))));
            return oe(from(gp,w,wg),goal,
              wf=>open(app(ue(al(g0),w),wf),(i,ip)=>ei(goal,i,ai(into(sd,i,ol(al(ip),Q(i,b))),ar(ip)))),
              eq=>{
                const bd=into(sd,b,or(M(b,b),ref(b)));
                return ei(goal,b,ai(bd,ei(replace(goal[2],goal[1],b)[2],r,eqSub(sym(eq),t=>form("pair",t,b,r),pp))));
              });
          }));
          const total=ui(i=>ii(M(i,d),id=>{
            const goal=E(y=>C(Val(g,i,y),A(z=>I(Val(g,i,z),Q(z,y)))));
            return oe(from(sd,i,id),goal,
              ib=>open(app(ue(ar(g0),i),ib),(y,yp)=>{
                const v=app(al(ue(app(ue(eqv,i),ib),y)),al(yp));
                const u=ui(z=>ii(Val(g,i,z),vz=>app(ue(ar(yp),z),app(ar(ue(app(ue(eqv,i),ib),z)),vz))));
                return ei(goal,y,ai(v,u));
              }),
              eq=>{
                const iv=eqSub(sym(eq),t=>Val(g,t,r),newValue);
                const un=ui(y=>ii(Val(g,i,y),vy=>{
                  const vb=eqSub(eq,t=>Val(g,t,y),vy);
                  return oe(valCases(b,y,vb),Q(y,r),old=>fe(app(nb,app(us(dom,f,b,b,y),g0,old)),Q(y,r)),both=>ar(both));
                }));
                return ei(goal,r,ai(iv,un));
              });
          }));
          return use(ai(entries,total),gg=>use(newValue,nv=>fn(g,gg,eqv,nv)));
        });
      }));
    }
    const appendExists=use(pairInjective,inj=>use(valDomain,dom=>use(noSelf,ns=>{
      return qs(4,(f,b,d,r)=>ii(Graph(f,b),gf=>ii(Succ(b,d),sd=>{
        const goal=E(g=>C(C(Graph(g,d),equiv(f,g,b)),Val(g,b,r)));
        return append(f,b,d,r,sd,gf,inj,dom,ns,(g,gg,eqv,nv)=>ei(goal,g,ai(ai(gg,eqv),nv)));
      })));
    })));
    function withNats(owEx,count,fn){
      return open(owEx,(w,ow)=>open(al(al(ow)),(z,zp)=>{
        const values=[z],inW=[al(zp)],succ=[],zero=ar(zp);
        function next(){
          if(values.length===count+1){
            function mem(i,j){
              if(!(i<j))throw Error("nat membership index");
              const p=j===i+1?or(M(values[i],values[i]),ref(values[i])):ol(mem(i,j-1),Q(values[i],values[j-1]));
              return into(succ[j-1],values[i],p);
            }
            function split(j,x,m,goal,cases){
              if(j===0)return fe(app(ue(zero,x),m),goal);
              return oe(from(succ[j-1],x,m),goal,old=>split(j-1,x,old,goal,cases),eq=>cases(j-1,eq));
            }
            return fn({w,ow,values,inW,succ,zero,mem,split});
          }
          const i=values.length-1;
          return open(app(ue(ar(al(ow)),values[i]),inW[i]),(x,xp)=>{
            values.push(x);inW.push(al(xp));succ.push(ar(xp));
            return next();
          });
        }
        return next();
      }));
    }
    function withFiniteGraph(ns,vals,ap,fn){
      const n=ns.values,z=n[0],g0=ai(
        ui(p=>ii(M(p,z),pz=>fe(app(ue(ns.zero,p),pz),E(i=>C(M(i,z),E(y=>form("pair",p,i,y))))))),
        ui(i=>ii(M(i,z),iz=>fe(app(ue(ns.zero,i),iz),E(y=>C(Val(z,i,y),A(v=>I(Val(z,i,v),Q(v,y)))))))));
      return use(g0,g=>{
        function extend(k,f,fg,vs){
          if(k===vals.length)return fn(f,fg,vs);
          return open(app(us(ap,f,n[k],n[k+1],vals[k]),fg,ns.succ[k]),(g,gp)=>{
            const gg=al(al(gp)),eqv=ar(al(gp)),nv=ar(gp);
            const next=vs.map((p,i)=>app(al(ue(app(ue(eqv,n[i]),ns.mem(i,k)),vals[i])),p));
            next.push(nv);
            function bindVs(j,bs){
              if(j===next.length)return extend(k+1,g,gg,bs);
              return use(next[j],v=>bindVs(j+1,[...bs,v]));
            }
            return bindVs(0,[]);
          });
        }
        return extend(0,z,g,[]);
      });
    }
    function withFiniteTuple(ns,a,vals,inside,ap,fn){
      const n=ns.values,arity=vals.length;
      return withFiniteGraph(ns,vals,ap,(s,g,vs)=>{
        const range=ui(i=>ii(M(i,n[arity]),im=>{
          const goal=E(v=>C(M(v,a),Val(s,i,v)));
          return ns.split(arity,i,im,goal,(j,eq)=>ei(goal,vals[j],ai(inside[j],eqSub(sym(eq),t=>Val(s,t,vals[j]),vs[j]))));
        }));
        return use(ai(g,range),tu=>fn(s,tu,vs));
      });
    }
    const tuple3=use(omegaExists,ow=>use(appendExists,ap=>qs(4,(a,x,y,z)=>{
      return ii(M(x,a),xa=>ii(M(y,a),ya=>ii(M(z,a),za=>withNats(ow,3,ns=>{
        const n=ns.values;
        return withFiniteTuple(ns,a,[x,y,z],[xa,ya,za],ap,(s,tu,vs)=>{
          const body=(n0,n1,n2,n3,s)=>C(C(form("tuple",s,n3,a),C(Val(s,n0,x),Val(s,n1,y))),Val(s,n2,z));
          const goal=E(n0=>E(n1=>E(n2=>E(n3=>E(s=>body(n0,n1,n2,n3,s))))));
          // This explicit test theorem also pins the index witnesses to
          // zero and successive ordinals, via separate graph proofs below.
          const a1=replace(goal[2],goal[1],n[0]),a2=replace(a1[2],a1[1],n[1]),a3=replace(a2[2],a2[1],n[2]),a4=replace(a3[2],a3[1],n[3]);
          return ei(goal,n[0],ei(a1,n[1],ei(a2,n[2],ei(a3,n[3],ei(a4,s,ai(ai(tu,ai(vs[0],vs[1])),vs[2]))))));
        });
      }))));
    })));

    const PairSet=(p,x,y)=>form("unordered",p,x,y);
    const UnionSet=(a,u)=>A(x=>B(M(x,u),E(y=>C(M(y,a),M(x,y)))));
    const classical=p=>dn(ii(N(["|",p,N(p)]),h=>app(h,or(p,ii(p,hp=>app(h,ol(hp,N(p))))))));
    function distinct(ns,i,j,nsf){
      const n=ns.values;
      if(i===j)throw Error("distinct same index");
      return ii(Q(n[i],n[j]),eq=>{
        const a=Math.min(i,j),b=Math.max(i,j),m=ns.mem(a,b);
        const ab=i===a?eq:sym(eq);
        return app(ue(nsf,n[b]),eqSub(ab,t=>M(t,n[b]),m));
      });
    }
    function agreeKnown(ns,k,change,s,b,st,bt,vals,sv,bv,nsf){
      const n=ns.values;
      const S=(i,v)=>Val(s,i,v),BV=(i,v)=>Val(b,i,v);
      return ui(j=>ii(M(j,n[k]),jn=>ii(N(Q(n[change],j)),neq=>ui(v=>{
        const goal=B(S(j,v),BV(j,v));
        return ns.split(k,j,jn,goal,(i,eq)=>{
          if(i===change)return fe(app(neq,sym(eq)),goal);
          const im=ns.mem(i,k);
          function move(source,target,sg,knownSrc,knownTgt,p){
            const at=eqSub(eq,t=>Val(source,t,v),p);
            const ve=valueUnique(al(sg),source,n[i],im,vals[i],v,knownSrc,at);
            return eqSub(sym(eq),t=>Val(target,t,v),eqSub(ve,t=>Val(target,n[i],t),knownTgt));
          }
          return ai(ii(S(j,v),p=>move(s,b,st,sv[i],bv[i],p)),ii(BV(j,v),p=>move(b,s,bt,bv[i],sv[i],p)));
        });
      }))));
    }
    function agreementValue(ns,k,change,i,s,b,agree,v,p,nsf,reverse){
      const n=ns.values,at=app(ue(agree,n[i]),ns.mem(i,k),distinct(ns,change,i,nsf));
      return app((reverse?al:ar)(ue(at,v)),p);
    }
    function atomIntro(ns,k,s,i,j,u,v,st,ua,va,sv,tv,property,rp){
      const p=ar(ue(rp,s)).goal[1][2],pBody=replace(p[2],p[1],u),q=pBody[2];
      const cert=ei(p,u,ai(ua,ei(q,v,ai(va,ai(ai(sv,tv),property)))));
      return into(rp,s,ai(st,cert));
    }
    function atomElim(ns,k,s,i,j,u,v,st,sv,tv,sr,rp,op){
      const cond=from(rp,s,sr);
      return open(ar(cond),(x,xp)=>open(ar(xp),(y,yp)=>{
        const vx=al(al(ar(yp))),vy=ar(al(ar(yp))),xy=ar(ar(yp));
        const xu=valueUnique(al(st),s,ns.values[i],ns.mem(i,k),x,u,vx,sv);
        const yv=valueUnique(al(st),s,ns.values[j],ns.mem(j,k),y,v,vy,tv);
        return eqSub(yv,t=>op(u,t),eqSub(xu,t=>op(t,y),xy));
      }));
    }
    function withProgram(ns,a,k,instructions,ap,rels,fn){
      const n=ns.values,arity=n[k],m=instructions.length;
      function choose(at,rs,rps){
        if(at===m){
          return withFiniteGraph(ns,rs,ap,(f,g,vs)=>{
            function entryAt(j){
              const st=form("entry",f,n[j],rs[j],arity,a);
              const leaves=[st[1][1][1][1],st[1][1][1][2],st[1][1][2],st[1][2],st[2]];
              const [op,i,t]=instructions[j];
              let at,pr;
              if(op==="eq"||op==="mem"){
                at=op==="eq"?0:1;
                const leaf=leaves[at],inner=replace(leaf[2],leaf[1],n[i])[2];
                pr=ei(leaf,n[i],ai(ns.mem(i,k),ei(inner,n[t],ai(ns.mem(t,k),rps[j]))));
              }else if(op==="neg"){
                at=2;
                const leaf=leaves[at],inner=replace(leaf[2],leaf[1],n[i])[2];
                pr=ei(leaf,n[i],ai(ns.mem(i,j),ei(inner,rs[i],ai(vs[i],rps[j]))));
              }else if(op==="and"){
                at=3;
                const leaf=leaves[at],inner=replace(leaf[2],leaf[1],n[i])[2];
                const p=replace(inner[2],inner[1],n[t])[2],q=replace(p[2],p[1],rs[i]);
                pr=ei(leaf,n[i],ai(ns.mem(i,j),ei(inner,n[t],ai(ns.mem(t,j),ei(p,rs[i],ei(q,rs[t],ai(ai(vs[i],vs[t]),rps[j])))))));
              }else if(op==="exists"){
                at=4;
                const leaf=leaves[at],inner=replace(leaf[2],leaf[1],n[i])[2],p=replace(inner[2],inner[1],n[t])[2];
                pr=ei(leaf,n[i],ai(ns.mem(i,j),ei(inner,n[t],ai(ns.mem(t,k),ei(p,rs[i],ai(vs[i],rps[j]))))));
              }else throw Error("bad instruction");
              let branch=at===0?pr:or(leaves.slice(0,at).reduce((a,b)=>["|",a,b]),pr);
              for(let l=at+1;l<leaves.length;l++)branch=ol(branch,leaves[l]);
              return branch;
            }
            const valid=ui(i=>ii(M(i,n[m]),im=>{
              const goal=E(r=>C(Val(f,i,r),form("entry",f,i,r,arity,a)));
              return ns.split(m,i,im,goal,(j,eq)=>{
                const p=eqSub(sym(eq),t=>C(Val(f,t,rs[j]),form("entry",f,t,rs[j],arity,a)),ai(vs[j],entryAt(j)));
                return ei(goal,rs[j],p);
              });
            }));
            return use(ai(g,valid),vp=>fn(f,vp,rs,rps,vs));
          });
        }
        const [op,i,j]=instructions[at];
        let ex;
        if(op==="eq"||op==="mem")ex=us(rels[op],a,arity,n[i],n[j]);
        else if(op==="neg")ex=us(rels.neg,a,arity,rs[i]);
        else if(op==="and")ex=us(rels.and,rs[i],rs[j]);
        else if(op==="exists")ex=us(rels.exists,a,arity,rs[i],n[j]);
        else throw Error("bad instruction");
        return open(ex,(r,rp)=>choose(at+1,[...rs,r],[...rps,rp]));
      }
      return choose(0,[],[]);
    }
    function finishDef(ns,a,x,k,m,f,valid,rs,vs,b,bt,slice){
      const n=ns.values,z=n[0],r=rs[m-1],goal=D(a,x),owGoal=goal[2];
      const owBody=replace(owGoal[2],owGoal[1],ns.w);
      const nGoal=owBody[2],nBody=replace(nGoal[2],nGoal[1],n[k]);
      const mGoal=nBody[2],mBody=replace(mGoal[2],mGoal[1],n[m]);
      const fGoal=mBody[2][2],fBody=replace(fGoal[2],fGoal[1],f);
      const ls=fBody[2],lsBody=replace(ls[2],ls[1],n[m-1]);
      const rGoal=lsBody[2][2],rBody=replace(rGoal[2],rGoal[1],r);
      const zGoal=rBody[2],zBody=replace(zGoal[2],zGoal[1],z),bGoal=zBody[2][2];
      const base=ei(bGoal,b,ai(bt,slice));
      const atZero=ei(zGoal,z,ai(ns.mem(0,k),ai(ns.zero,base)));
      const atR=ei(rGoal,r,ai(vs[m-1],atZero));
      const last=ei(ls,n[m-1],ai(ns.mem(m-1,m),ai(ns.succ[m-1],atR)));
      const pF=ei(fGoal,f,ai(valid,last));
      const nk=ei(E(i=>M(i,n[k])),z,ns.mem(0,k)),nm=ei(E(i=>M(i,n[m])),z,ns.mem(0,m));
      const pM=ei(mGoal,n[m],ai(ns.inW[m],ai(ai(nk,nm),pF)));
      const pN=ei(nGoal,n[k],ai(ns.inW[k],pM));
      return or(goal[1],ei(owGoal,ns.w,ai(ns.ow,pN)));
    }
    const pairInstructions=[["eq",0,1],["eq",0,2],["neg",0],["neg",1],["and",2,3],["neg",4]];
    function pairDefWitness(ns,a,x,y,p,xa,ya,pp,ap,nsf,rels){
      const n=ns.values,k=3,m=pairInstructions.length;
      return withProgram(ns,a,k,pairInstructions,ap,rels,(f,valid,rs,rps,vs)=>{
        return withFiniteTuple(ns,a,[x,x,y],[xa,xa,ya],ap,(b,bt,bv)=>{
          function sliceAt(u){
            const target=form("slice",p,rs[5],a,n[k],n[0],b);
            const g=replace(target[2],target[1],u),witness=g[1][2][2];
            const left=ii(M(u,p),up=>{
              const choices=from(pp,u,up);
              const ua=oe(choices,M(u,a),ux=>eqSub(sym(ux),t=>M(t,a),xa),uy=>eqSub(sym(uy),t=>M(t,a),ya));
              return use(ua,uu=>withFiniteTuple(ns,a,[u,x,y],[uu,xa,ya],ap,(s,st,sv)=>{
                const notAnd=ii(M(s,rs[4]),sa=>{
                  const negs=from(rps[4],s,sa);
                  const q=oe(choices,F,ux=>{
                    const pos=atomIntro(ns,k,s,0,1,u,x,st,uu,xa,sv[0],sv[1],ux,rps[0]);
                    return app(ar(from(rps[2],s,al(negs))),pos);
                  },uy=>{
                    const pos=atomIntro(ns,k,s,0,2,u,y,st,uu,ya,sv[0],sv[2],uy,rps[1]);
                    return app(ar(from(rps[3],s,ar(negs))),pos);
                  });
                  return q;
                });
                const sr=into(rps[5],s,ai(st,notAnd));
                const agree=agreeKnown(ns,k,0,s,b,st,bt,[u,x,y],sv,bv,nsf);
                return ai(uu,ei(witness,s,ai(sr,ai(sv[0],agree))));
              }));
            });
            const right=ii(g[2][1],q=>{
              return open(ar(q),(s,sw)=>{
                const sr=al(sw),s0=al(ar(sw)),agree=ar(ar(sw)),cond=from(rps[5],s,sr),st=al(cond);
                const sx=agreementValue(ns,k,0,1,s,b,agree,x,bv[1],nsf,false);
                const sy=agreementValue(ns,k,0,2,s,b,agree,y,bv[2],nsf,false);
                const want=["|",Q(u,x),Q(u,y)];
                const proof=oe(classical(M(s,rs[0])),want,r0=>ol(atomElim(ns,k,s,0,1,u,x,st,s0,sx,r0,rps[0],Q),Q(u,y)),nr0=>{
                  return oe(classical(M(s,rs[1])),want,r1=>or(Q(u,x),atomElim(ns,k,s,0,2,u,y,st,s0,sy,r1,rps[1],Q)),nr1=>{
                    const r2=into(rps[2],s,ai(st,nr0)),r3=into(rps[3],s,ai(st,nr1));
                    return fe(app(ar(cond),into(rps[4],s,ai(r2,r3))),want);
                  });
                });
                return into(pp,u,proof);
              });
            });
            return ai(left,right);
          }
          return finishDef(ns,a,p,k,m,f,valid,rs,vs,b,bt,ui(sliceAt));
        });
      });
    }
    const pairDefinable=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(eqExists,eq=>use(negExists,neg=>use(andExists,and=>{
      return qs(4,(a,x,y,p)=>ii(M(x,a),xa=>ii(M(y,a),ya=>ii(PairSet(p,x,y),pp=>{
        return withNats(ow,6,ns=>pairDefWitness(ns,a,x,y,p,xa,ya,pp,ap,nsf,{eq,neg,and}));
      }))));
    }))))));

    const unionInstructions=[["mem",0,2],["mem",2,1],["and",0,1],["exists",2,2]];
    function unionDefWitness(ns,a,x,p,ta,xa,pp,ap,nsf,rels){
      const n=ns.values,k=3,m=unionInstructions.length;
      return withProgram(ns,a,k,unionInstructions,ap,rels,(f,valid,rs,rps,vs)=>{
        return withFiniteTuple(ns,a,[x,x,x],[xa,xa,xa],ap,(b,bt,bv)=>{
          function sliceAt(u){
            const target=form("slice",p,rs[3],a,n[k],n[0],b);
            const g=replace(target[2],target[1],u),witness=g[1][2][2];
            const left=ii(M(u,p),up=>{
              return open(from(pp,u,up),(v,vp)=>{
                const vx=al(vp),uv=ar(vp);
                const va=app(ue(app(ue(ta,x),xa),v),vx);
                const ua=app(ue(app(ue(ta,v),va),u),uv);
                return use(va,vA=>use(ua,uA=>{
                  return withFiniteTuple(ns,a,[u,x,x],[uA,xa,xa],ap,(s,st,sv)=>{
                    return withFiniteTuple(ns,a,[u,x,v],[uA,xa,vA],ap,(t,tt,tv)=>{
                      const r0=atomIntro(ns,k,t,0,2,u,v,tt,uA,vA,tv[0],tv[2],uv,rps[0]);
                      const r1=atomIntro(ns,k,t,2,1,v,x,tt,vA,xa,tv[2],tv[1],vx,rps[1]);
                      const r2=into(rps[2],t,ai(r0,r1));
                      const agree=agreeKnown(ns,k,2,s,t,st,tt,[u,x,x],sv,tv,nsf);
                      const ex=ar(ue(rps[3],s)).goal[1][2];
                      const sr=into(rps[3],s,ai(st,ei(ex,t,ai(r2,agree))));
                      const baseAgree=agreeKnown(ns,k,0,s,b,st,bt,[u,x,x],sv,bv,nsf);
                      return ai(uA,ei(witness,s,ai(sr,ai(sv[0],baseAgree))));
                    });
                  });
                }));
              });
            });
            const right=ii(g[2][1],q=>{
              return open(ar(q),(s,sw)=>{
                const sr=al(sw),s0=al(ar(sw)),agree=ar(ar(sw));
                const cond=from(rps[3],s,sr);
                const sx=agreementValue(ns,k,0,1,s,b,agree,x,bv[1],nsf,false);
                return open(ar(cond),(t,tp)=>{
                  const both=from(rps[2],t,al(tp)),r0=al(both),r1=ar(both),st=al(from(rps[0],t,r0)),ag=ar(tp);
                  const t0=agreementValue(ns,k,2,0,s,t,ag,u,s0,nsf,true);
                  const t1=agreementValue(ns,k,2,1,s,t,ag,x,sx,nsf,true);
                  return open(app(ue(ar(st),n[2]),ns.mem(2,k)),(v,vp)=>{
                    const t2=ar(vp);
                    const uv=atomElim(ns,k,t,0,2,u,v,st,t0,t2,r0,rps[0],M);
                    const vx=atomElim(ns,k,t,2,1,v,x,st,t2,t1,r1,rps[1],M);
                    return into(pp,u,ei(ar(ue(pp,u)).goal[1],v,ai(vx,uv)));
                  });
                });
              });
            });
            return ai(left,right);
          }
          return finishDef(ns,a,p,k,m,f,valid,rs,vs,b,bt,ui(sliceAt));
        });
      });
    }
    const unionDefinable=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(relationExists,mem=>use(andExists,and=>use(exExists,exists=>{
      return qs(3,(a,x,p)=>ii(trans(a),ta=>ii(M(x,a),xa=>ii(UnionSet(x,p),pp=>{
        return withNats(ow,4,ns=>unionDefWitness(ns,a,x,p,ta,xa,pp,ap,nsf,{mem,and,exists}));
      }))));
    }))))));
    Object.assign(proofs,{equality_relation_exists:eqExists,negation_relation_exists:negExists,intersection_relation_exists:andExists,existential_relation_exists:exExists,foundation_no_self:noSelf,value_in_domain:valDomain,graph_append_exists:appendExists,ternary_tuple_exists:tuple3,pair_definable:pairDefinable,union_definable:unionDefinable});


    if(extended&&typeof extended==="object"&&extended.mode==="compiler"){
      const {formula,params}=extended;
      function well(p,k){
        if(!Array.isArray(p))return false;const [op,a,b]=p;
        if(op==="F")return p.length===1;
        if(op==="="||op==="M")return p.length===3&&[a,b].every(i=>Number.isSafeInteger(i)&&i>=0&&i<k);
        if(op==="A"||op==="E")return p.length===2&&well(a,k+1);
        return ["&","|",">"].includes(op)&&p.length===3&&well(a,k)&&well(b,k);
      }
      if(!Number.isInteger(params)||params<0||params>3||!well(formula,params+1))throw Error("compiler scope/arity");
      const instructions=[];let width=params+1;
      function emit(op,...args){instructions.push([op,...args]);return instructions.length-1;}
      function lower(p,env,depth=0){
        const [op,a,b]=p,t={p,env,op};
        if(op==="F")t.idx=emit("neg",emit("eq",0,0));
        else if(op==="M"||op==="=")t.idx=emit(op==="M"?"mem":"eq",env[a],env[b]);
        else if(op==="A"||op==="E"){
          const slot=params+1+depth;width=Math.max(width,slot+1);t.slot=slot;
          t.child=lower(a,[slot,...env],depth+1);
          t.idx=op==="E"?emit("exists",t.child.idx,slot):emit("neg",emit("exists",emit("neg",t.child.idx),slot));
        }else{
          t.left=lower(a,env,depth);t.right=lower(b,env,depth);
          const i=t.left.idx,j=t.right.idx;
          t.idx=op==="&"?emit("and",i,j):op==="|"?emit("neg",emit("and",emit("neg",i),emit("neg",j))):emit("neg",emit("and",i,emit("neg",j)));
        }
        return t;
      }
      const tree=lower(formula,Array.from({length:params+1},(_,i)=>i)),k=width,m=instructions.length;
      if(k>6||m>20)throw Error("compiler finite resource cap");
      function changed(vs,i,x){return vs.map((v,j)=>j===i?x:v);}
      function sem(j,a,vals){
        const [op,i,l]=instructions[j];
        if(op==="eq")return Q(vals[i],vals[l]);
        if(op==="mem")return M(vals[i],vals[l]);
        if(op==="neg")return N(sem(i,a,vals));
        if(op==="and")return C(sem(i,a,vals),sem(l,a,vals));
        if(op==="exists")return E(v=>C(M(v,a),sem(i,a,changed(vals,l,v))));
        throw Error("semantic opcode");
      }
      function restrictN(p,a){const [o,x,y]=p;if(o==="A")return [o,x,I(M(x,a),restrictN(y,a))];if(o==="E")return [o,x,C(M(x,a),restrictN(y,a))];if(["&","|",">"].includes(o))return [o,restrictN(x,a),restrictN(y,a)];return p;}
      function local(t,a,vals){return restrictN(named(t.p,t.env.map(i=>vals[i])),a);}
      // Check exact local formula equivalence to the instruction semantics.
      function bridge(t,a,vals){
        const orig=local(t,a,vals),norm=sem(t.idx,a,vals),op=t.op;
        if(op==="M"||op==="=")return ai(ii(orig,p=>p),ii(norm,p=>p));
        if(op==="F")return ai(ii(orig,p=>fe(p,norm)),ii(norm,p=>app(p,ref(vals[0]))));
        if(op==="A"||op==="E"){
          const child=(v)=>bridge(t.child,a,changed(vals,t.slot,v));
          if(op==="E"){
            return ai(ii(orig,p=>open(p,(v,vp)=>ei(norm,v,ai(al(vp),app(al(child(v)),ar(vp)))))),
              ii(norm,p=>open(p,(v,vp)=>ei(orig,v,ai(al(vp),app(ar(child(v)),ar(vp)))))));
          }
          const fw=ii(orig,p=>ii(norm[1],bad=>open(bad,(v,vp)=>{
            return app(ar(vp),app(al(child(v)),app(ue(p,v),al(vp))));
          })));
          const bw=ii(norm,p=>ui(v=>ii(M(v,a),va=>{
            const g=local(t.child,a,changed(vals,t.slot,v));
            return dn(ii(N(g),ng=>{
              const ns=ii(sem(t.child.idx,a,changed(vals,t.slot,v)),q=>app(ng,app(ar(child(v)),q)));
              return app(p,ei(norm[1],v,ai(va,ns)));
            }));
          })));
          return ai(fw,bw);
        }
        return use(bridge(t.left,a,vals),l=>use(bridge(t.right,a,vals),r=>{
          if(op==="&")return ai(ii(orig,p=>ai(app(al(l),al(p)),app(al(r),ar(p)))),ii(norm,p=>ai(app(ar(l),al(p)),app(ar(r),ar(p)))));
          if(op==="|"){
            const fw=ii(orig,p=>ii(norm[1],bad=>oe(p,F,x=>app(al(bad),app(al(l),x)),y=>app(ar(bad),app(al(r),y)))));
            const bw=ii(norm,p=>dn(ii(N(orig),no=>{
              const nl=ii(sem(t.left.idx,a,vals),x=>app(no,ol(app(ar(l),x),orig[2])));
              const nr=ii(sem(t.right.idx,a,vals),y=>app(no,or(orig[1],app(ar(r),y))));
              return app(p,ai(nl,nr));
            })));
            return ai(fw,bw);
          }
          const fw=ii(orig,p=>ii(norm[1],bad=>app(ar(bad),app(al(r),app(p,app(ar(l),al(bad)))))));
          const bw=ii(norm,p=>ii(orig[1],x=>dn(ii(N(orig[2]),ny=>{
            const nr=ii(sem(t.right.idx,a,vals),y=>app(ny,app(ar(r),y)));
            return app(p,ai(app(al(l),x),nr));
          }))));
          return ai(fw,bw);
        }));
      }
      function tupleProofs(ns,a,s,st,vals,ins,vs,fn){
        if(vals.length===k)return fn(vals,ins,vs);
        const i=vals.length;
        return open(app(ue(ar(st),ns.values[i]),ns.mem(i,k)),(v,p)=>tupleProofs(ns,a,s,st,[...vals,v],[...ins,al(p)],[...vs,ar(p)],fn));
      }
      function withKnown(ns,a,s,st,vals,ins,vs,fn){
        if(vals.length===k)return fn(vals,ins,vs);
        const i=vals.length;
        return ui(v=>ii(M(v,a),va=>ii(Val(s,ns.values[i],v),sv=>withKnown(ns,a,s,st,[...vals,v],[...ins,va],[...vs,sv],fn))));
      }
      function instantiate(p,s,st,vals,ins,vs){
        let q=app(ue(p,s),st);
        for(let i=0;i<k;i++)q=app(ue(q,vals[i]),ins[i],vs[i]);
        return q;
      }
      function relationTheorems(ns,a,rs,rps,ap,nsf,fn){
        function loop(j,types,truths){
          if(j===m)return fn(types,truths);
          const [op,i,l]=instructions[j],r=rs[j],rp=rps[j];
          const type=ui(s=>ii(M(s,r),sr=>{
            const p=from(rp,s,sr);
            return op==="and"?app(ue(types[i],s),al(p)):al(p);
          }));
          const theorem=ui(s=>ii(form("tuple",s,ns.values[k],a),st=>withKnown(ns,a,s,st,[],[],[],(vals,ins,vs)=>{
            const goal=sem(j,a,vals);
            if(op==="eq"||op==="mem"){
              const o=op==="eq"?Q:M;
              return ai(ii(M(s,r),p=>atomElim(ns,k,s,i,l,vals[i],vals[l],st,vs[i],vs[l],p,rp,o)),
                ii(goal,p=>atomIntro(ns,k,s,i,l,vals[i],vals[l],st,ins[i],ins[l],vs[i],vs[l],p,rp)));
            }
            if(op==="neg"){
              const ch=instantiate(truths[i],s,st,vals,ins,vs);
              return ai(ii(M(s,r),p=>ii(goal[1],q=>app(ar(from(rp,s,p)),app(ar(ch),q)))),
                ii(goal,p=>into(rp,s,ai(st,ii(M(s,rs[i]),q=>app(p,app(al(ch),q)))))));
            }
            if(op==="and"){
              const cl=instantiate(truths[i],s,st,vals,ins,vs),cr=instantiate(truths[l],s,st,vals,ins,vs);
              return ai(ii(M(s,r),p=>{const both=from(rp,s,p);return ai(app(al(cl),al(both)),app(al(cr),ar(both)));}),
                ii(goal,p=>into(rp,s,ai(app(ar(cl),al(p)),app(ar(cr),ar(p))))));
            }
            const fw=ii(M(s,r),p=>open(ar(from(rp,s,p)),(t,tp)=>{
              const tt=app(ue(types[i],t),al(tp)),agree=ar(tp);
              return open(app(ue(ar(tt),ns.values[l]),ns.mem(l,k)),(v,vp)=>{
                const tv=vals.map((x,c)=>c===l?ar(vp):agreementValue(ns,k,l,c,s,t,agree,x,vs[c],nsf,true));
                const vls=changed(vals,l,v),is=changed(ins,l,al(vp));
                const ch=instantiate(truths[i],t,tt,vls,is,tv);
                return ei(goal,v,ai(al(vp),app(al(ch),al(tp))));
              });
            }));
            const bw=ii(goal,p=>open(p,(v,vp)=>{
              const vls=changed(vals,l,v),is=changed(ins,l,al(vp));
              return withFiniteTuple(ns,a,vls,is,ap,(t,tt,tv)=>{
                const ch=instantiate(truths[i],t,tt,vls,is,tv);
                const tr=app(ar(ch),ar(vp)),ag=agreeKnown(ns,k,l,s,t,st,tt,vals,vs,tv,nsf);
                const ex=ar(ue(rp,s)).goal[1][2];
                return into(rp,s,ai(st,ei(ex,t,ai(tr,ag))));
              });
            }));
            return ai(fw,bw);
          })));
          return use(type,ty=>use(theorem,th=>loop(j+1,[...types,ty],[...truths,th])));
        }
        return loop(0,[],[]);
      }
      function localAt(a,u,ps){return restrictN(named(formula,[u,...ps]),a);}
      const specSet=(a,p,ps)=>A(u=>B(M(u,p),C(M(u,a),localAt(a,u,ps))));
      function compiledDef(ns,a,p,ps,pms,seed,seedMem,pp,ap,nsf,rels){
        return withProgram(ns,a,k,instructions,ap,rels,(f,valid,rs,rps,vs)=>{
          return relationTheorems(ns,a,rs,rps,ap,nsf,(types,truths)=>{
            const base=[seed,...ps,...Array(k-params-1).fill(seed)],baseIn=[seedMem,...pms,...Array(k-params-1).fill(seedMem)];
            return withFiniteTuple(ns,a,base,baseIn,ap,(b,bt,bv)=>{
              const slice=ui(u=>{
                const target=form("slice",p,rs[m-1],a,ns.values[k],ns.values[0],b),g=replace(target[2],target[1],u),witness=g[1][2][2];
                const left=ii(M(u,p),up=>{
                  const cond=from(pp,u,up),ua=al(cond),loc=ar(cond),vals=changed(base,0,u),ins=changed(baseIn,0,ua);
                  return withFiniteTuple(ns,a,vals,ins,ap,(s,st,sv)=>{
                    const br=bridge(tree,a,vals),eq=instantiate(truths[m-1],s,st,vals,ins,sv);
                    const sr=app(ar(eq),app(al(br),loc)),ag=agreeKnown(ns,k,0,s,b,st,bt,vals,sv,bv,nsf);
                    return ai(ua,ei(witness,s,ai(sr,ai(sv[0],ag))));
                  });
                });
                const right=ii(g[2][1],q=>open(ar(q),(s,sw)=>{
                  const sr=al(sw),s0=al(ar(sw)),ag=ar(ar(sw)),st=app(ue(types[m-1],s),sr);
                  const vals=changed(base,0,u),ins=changed(baseIn,0,al(q));
                  const sv=[s0,...base.slice(1).map((v,i)=>agreementValue(ns,k,0,i+1,s,b,ag,v,bv[i+1],nsf,false))];
                  const eq=instantiate(truths[m-1],s,st,vals,ins,sv),br=bridge(tree,a,vals);
                  return into(pp,u,ai(al(q),app(ar(br),app(al(eq),sr))));
                }));
                return ai(left,right);
              });
              return finishDef(ns,a,p,k,m,f,valid,rs,vs,b,bt,slice);
            });
          });
        });
      }
      function bindParams(a,ps,ms,fn){return ps.length===params?fn(ps,ms):ui(v=>ii(M(v,a),va=>bindParams(a,[...ps,v],[...ms,va],fn)));}
      const generalDef=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(relationExists,mem=>use(eqExists,eq=>use(negExists,neg=>use(andExists,and=>use(exExists,exists=>{
        return ui(a=>bindParams(a,[],[],(ps,pms)=>ui(p=>ii(specSet(a,p,ps),pp=>{
          const some=E(x=>M(x,a)),goal=D(a,p);
          function solve(seed,seedMem){return withNats(ow,Math.max(k,m),ns=>compiledDef(ns,a,p,ps,pms,seed,seedMem,pp,ap,nsf,{mem,eq,neg,and,exists}));}
          if(params>0)return solve(ps[0],pms[0]);
          return oe(classical(some),goal,yes=>open(yes,solve),no=>{
            const empty=ui(x=>ii(M(x,p),xp=>app(no,ei(some,x,al(from(pp,x,xp))))));
            return ol(empty,goal[2]);
          });
        }))));
      }))))))));
      Object.assign(proofs,{compiled_formula_definable:generalDef});
    }
    if(extended==="power"){
      const subsetInstructions=[["mem",2,0],["mem",2,1],["neg",1],["and",0,2],["exists",3,2],["neg",4]];
      const relativePower=(a,x,p)=>A(y=>B(M(y,p),C(M(y,a),subset(y,x))));
      function subsetWitness(ns,a,x,p,ta,xa,pp,ap,nsf,rels){
        const n=ns.values,k=3,m=subsetInstructions.length;
        return withProgram(ns,a,k,subsetInstructions,ap,rels,(f,valid,rs,rps,vs)=>{
          return withFiniteTuple(ns,a,[x,x,x],[xa,xa,xa],ap,(b,bt,bv)=>{
            const slice=ui(u=>{
              const target=form("slice",p,rs[5],a,n[k],n[0],b);
              const g=replace(target[2],target[1],u),witness=g[1][2][2];
              const left=ii(M(u,p),up=>{
                const info=from(pp,u,up),ua=al(info),sub=ar(info);
                return withFiniteTuple(ns,a,[u,x,x],[ua,xa,xa],ap,(s,st,sv)=>{
                  const noBad=ii(M(s,rs[4]),bad=>{
                    const exists=ar(from(rps[4],s,bad));
                    return open(exists,(t,tp)=>{
                      const both=from(rps[3],t,al(tp)),r0=al(both),r2=ar(both);
                      const neg=from(rps[2],t,r2),tt=al(neg),ag=ar(tp);
                      const t0=agreementValue(ns,k,2,0,s,t,ag,u,sv[0],nsf,true);
                      const t1=agreementValue(ns,k,2,1,s,t,ag,x,sv[1],nsf,true);
                      return open(app(ue(ar(tt),n[2]),ns.mem(2,k)),(v,vp)=>{
                        const va=al(vp),t2=ar(vp);
                        const vu=atomElim(ns,k,t,2,0,v,u,tt,t2,t0,r0,rps[0],M);
                        const vx=app(ue(sub,v),vu);
                        const r1=atomIntro(ns,k,t,2,1,v,x,tt,va,xa,t2,t1,vx,rps[1]);
                        return app(ar(neg),r1);
                      });
                    });
                  });
                  const sr=into(rps[5],s,ai(st,noBad));
                  const agree=agreeKnown(ns,k,0,s,b,st,bt,[u,x,x],sv,bv,nsf);
                  return ai(ua,ei(witness,s,ai(sr,ai(sv[0],agree))));
                });
              });
              const right=ii(g[2][1],q=>{
                const ua=al(q);
                return open(ar(q),(s,sw)=>{
                  const sr=al(sw),s0=al(ar(sw)),agree=ar(ar(sw)),cond=from(rps[5],s,sr),st=al(cond);
                  const sx=agreementValue(ns,k,0,1,s,b,agree,x,bv[1],nsf,false);
                  const sub=ui(v=>ii(M(v,u),vu=>{
                    const va=app(ue(app(ue(ta,u),ua),v),vu);
                    return dn(ii(N(M(v,x)),nvx=>{
                      return withFiniteTuple(ns,a,[u,x,v],[ua,xa,va],ap,(t,tt,tv)=>{
                        const r0=atomIntro(ns,k,t,2,0,v,u,tt,va,ua,tv[2],tv[0],vu,rps[0]);
                        const nr1=ii(M(t,rs[1]),r1=>app(nvx,atomElim(ns,k,t,2,1,v,x,tt,tv[2],tv[1],r1,rps[1],M)));
                        const r2=into(rps[2],t,ai(tt,nr1));
                        const r3=into(rps[3],t,ai(r0,r2));
                        const ag=agreeKnown(ns,k,2,s,t,st,tt,[u,x,v],[s0,sx,null],tv,nsf);
                        const ex=ar(ue(rps[4],s)).goal[1][2];
                        const bad=into(rps[4],s,ai(st,ei(ex,t,ai(r3,ag))));
                        return app(ar(cond),bad);
                      });
                    }));
                  }));
                  return into(pp,u,ai(ua,sub));
                });
              });
              return ai(left,right);
            });
            return finishDef(ns,a,p,k,m,f,valid,rs,vs,b,bt,slice);
          });
        });
      }
      const subsetDefinable=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(relationExists,mem=>use(negExists,neg=>use(andExists,and=>use(exExists,exists=>{
        return qs(3,(a,x,p)=>ii(trans(a),ta=>ii(M(x,a),xa=>ii(relativePower(a,x,p),pp=>{
          return withNats(ow,6,ns=>subsetWitness(ns,a,x,p,ta,xa,pp,ap,nsf,{mem,neg,and,exists}));
        }))));
      })))))));
      Object.assign(proofs,{relative_power_definable:subsetDefinable});
    }
    if(extended==="infinity"){
      const succInstructions=[["mem",0,1],["eq",0,1],["neg",0],["neg",1],["and",2,3],["neg",4]];
      function successorDefWitness(ns,a,x,p,ta,xa,pp,ap,nsf,rels){
        const n=ns.values,k=2,m=succInstructions.length;
        return withProgram(ns,a,k,succInstructions,ap,rels,(f,valid,rs,rps,vs)=>{
          return withFiniteTuple(ns,a,[x,x],[xa,xa],ap,(b,bt,bv)=>{
            const slice=ui(u=>{
              const target=form("slice",p,rs[5],a,n[k],n[0],b);
              const g=replace(target[2],target[1],u),witness=g[1][2][2];
              const left=ii(M(u,p),up=>{
                const choices=from(pp,u,up);
                const ua=oe(choices,M(u,a),ux=>app(ue(app(ue(ta,x),xa),u),ux),eq=>eqSub(sym(eq),t=>M(t,a),xa));
                return use(ua,uu=>withFiniteTuple(ns,a,[u,x],[uu,xa],ap,(s,st,sv)=>{
                  const notAnd=ii(M(s,rs[4]),sa=>{
                    const negs=from(rps[4],s,sa);
                    return oe(choices,F,ux=>{
                      const pos=atomIntro(ns,k,s,0,1,u,x,st,uu,xa,sv[0],sv[1],ux,rps[0]);
                      return app(ar(from(rps[2],s,al(negs))),pos);
                    },eq=>{
                      const pos=atomIntro(ns,k,s,0,1,u,x,st,uu,xa,sv[0],sv[1],eq,rps[1]);
                      return app(ar(from(rps[3],s,ar(negs))),pos);
                    });
                  });
                  const sr=into(rps[5],s,ai(st,notAnd));
                  const agree=agreeKnown(ns,k,0,s,b,st,bt,[u,x],sv,bv,nsf);
                  return ai(uu,ei(witness,s,ai(sr,ai(sv[0],agree))));
                }));
              });
              const right=ii(g[2][1],q=>open(ar(q),(s,sw)=>{
                const sr=al(sw),s0=al(ar(sw)),agree=ar(ar(sw)),cond=from(rps[5],s,sr),st=al(cond);
                const sx=agreementValue(ns,k,0,1,s,b,agree,x,bv[1],nsf,false);
                const want=["|",M(u,x),Q(u,x)];
                const pr=oe(classical(M(s,rs[0])),want,r0=>ol(atomElim(ns,k,s,0,1,u,x,st,s0,sx,r0,rps[0],M),Q(u,x)),nr0=>
                  oe(classical(M(s,rs[1])),want,r1=>or(M(u,x),atomElim(ns,k,s,0,1,u,x,st,s0,sx,r1,rps[1],Q)),nr1=>{
                    const r2=into(rps[2],s,ai(st,nr0)),r3=into(rps[3],s,ai(st,nr1));
                    return fe(app(ar(cond),into(rps[4],s,ai(r2,r3))),want);
                  }));
                return into(pp,u,pr);
              }));
              return ai(left,right);
            });
            return finishDef(ns,a,p,k,m,f,valid,rs,vs,b,bt,slice);
          });
        });
      }
      const successorDefinable=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(relationExists,mem=>use(eqExists,eq=>use(negExists,neg=>use(andExists,and=>{
        return qs(3,(a,x,p)=>ii(trans(a),ta=>ii(M(x,a),xa=>ii(Succ(x,p),pp=>{
          return withNats(ow,6,ns=>successorDefWitness(ns,a,x,p,ta,xa,pp,ap,nsf,{mem,eq,neg,and}));
        }))));
      })))))));
      function selfDefWitness(ns,a,x,xa,ap,nsf,eq){
        const n=ns.values,k=1,m=1;
        return withProgram(ns,a,k,[["eq",0,0]],ap,{eq},(f,valid,rs,rps,vs)=>{
          return withFiniteTuple(ns,a,[x],[xa],ap,(b,bt,bv)=>{
            const slice=ui(u=>{
              const target=form("slice",a,rs[0],a,n[1],n[0],b),g=replace(target[2],target[1],u),witness=g[1][2][2];
              const left=ii(M(u,a),ua=>withFiniteTuple(ns,a,[u],[ua],ap,(s,st,sv)=>{
                const sr=atomIntro(ns,1,s,0,0,u,u,st,ua,ua,sv[0],sv[0],ref(u),rps[0]);
                const agree=agreeKnown(ns,1,0,s,b,st,bt,[u],sv,bv,nsf);
                return ai(ua,ei(witness,s,ai(sr,ai(sv[0],agree))));
              }));
              return ai(left,ii(g[2][1],p=>al(p)));
            });
            return finishDef(ns,a,a,k,m,f,valid,rs,vs,b,bt,slice);
          });
        });
      }
      const selfDefinable=use(omegaExists,ow=>use(appendExists,ap=>use(noSelf,nsf=>use(eqExists,eq=>ui(a=>{
        const ex=E(x=>M(x,a)),goal=D(a,a);
        return oe(classical(ex),goal,
          some=>open(some,(x,xa)=>withNats(ow,1,ns=>selfDefWitness(ns,a,x,xa,ap,nsf,eq))),
          none=>ol(ui(x=>ii(M(x,a),xa=>app(none,ei(ex,x,xa)))),goal[2]));
      })))));
      Object.assign(proofs,{successor_definable:successorDefinable,self_definable:selfDefinable});
    }

  }
  if(extended===true){
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
