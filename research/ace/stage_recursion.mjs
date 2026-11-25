import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
function buildI(defs,prior,finite,extended=false){
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
  const Val=(f,i,r)=>form("val",f,i,r),Graph=(f,d)=>form("graph",f,d),SG=(f,d)=>form("stageGraph",f,d),Stage=(f,b,r)=>form("stage",f,b,r),Succ=(a,b)=>form("successor",a,b),Ord=a=>form("ordinal",a);
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
  const from=(p,x,px)=>app(al(ue(p,x)),px);
  const into=(p,x,px)=>app(ar(ue(p,x)),px);
  const extEq=(a,b,fn)=>app(us(ax({name:"extensionality"}),a,b),ui(fn));
  const em=p=>dn(ii(N(["|",p,N(p)]),h=>app(h,or(p,ii(p,hp=>app(h,ol(hp,N(p))))))));
  function shiftHyps(p,k){
    if(!Array.isArray(p))return p;
    if(p[0]==="h")return ["h",p[1]+k];
    return p.map(x=>shiftHyps(x,k));
  }
  function imported(p){return P(named(p.goal,[]),(_,h)=>shiftHyps(p.proof,h.length));}
  const pairInj=imported(finite.pair_injective),pairEx=imported(finite.pair_exists);
  const defEx=imported(prior.def_exists),noCycle=imported(prior.no_two_cycle),coh=imported(prior.stage_graph_coherence),unique=imported(prior.stage_graph_unique),restrict=imported(prior.stage_graph_restriction),succTrans=imported(prior.ordinal_successor_transitivity);
  const withSetPair=(a,b,fn)=>open(us(ax({name:"pairing"}),a,b),fn);
  const withUnion=(a,fn)=>open(ue(ax({name:"union"}),a),fn);
  function withSingleton(a,fn){
    return withSetPair(a,a,(s,sp)=>{
      const proof=ui(x=>ai(ii(M(x,s),xs=>oe(from(sp,x,xs),Q(x,a),q=>q,q=>q)),ii(Q(x,a),q=>into(sp,x,ol(q,Q(x,a))))));
      return use(proof,single=>fn(s,single));
    });
  }
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
  const successorExists=ui(b=>withAdjoin(b,b,(d,su)=>ei(E(d=>Succ(b,d)),d,su)));
  const succUnique=qs(3,(b,d,e)=>ii(Succ(b,d),sd=>ii(Succ(b,e),se=>extEq(d,e,x=>ai(ii(M(x,d),xd=>into(se,x,from(sd,x,xd))),ii(M(x,e),xe=>into(sd,x,from(se,x,xe))))))));
  const domainLemma=use(pairInj,inj=>qs(4,(f,d,i,r)=>ii(Graph(f,d),g=>ii(Val(f,i,r),v=>open(v,(p,pv)=>{
    return open(app(ue(al(g),p),al(pv)),(j,jp)=>open(ar(jp),(y,py)=>{
      const eq=al(app(us(inj,p,i,r,j,y),ar(pv),py));
      return eqSub(sym(eq),t=>M(t,d),al(jp));
    }));
  })))));
  const reflSub=ui(a=>ui(x=>ii(M(x,a),p=>p)));
  function earlier(td,b,bd,i,ib){return app(ue(app(ue(td,b),bd),i),ib);}
  const eqvVals=(f,g,b)=>A(i=>I(M(i,b),A(r=>B(Val(f,i,r),Val(g,i,r)))));
  function transfer(f,g,b,r,eqv,st){
    const target=Stage(g,b,r);
    return oe(st,target,ss=>open(ss,(i,ip)=>open(ar(ar(ip)),(s,sp)=>{
      const v=app(al(ue(app(ue(eqv,i),al(ip)),s)),al(sp));
      const inn=replace(target[1][2],target[1][1],i)[2][2];
      return ol(ei(target[1],i,ai(al(ip),ai(al(ar(ip)),ei(inn,s,ai(v,ar(sp)))))),target[2]);
    })),ls=>{
      const old=ar(ls),newU=target[2][2];
      const union=ui(x=>{
        function move(p,goal,reverse){
          return open(p,(i,ip)=>open(ar(ip),(s,sp)=>{
            const eq=ue(app(ue(eqv,i),al(ip)),s),v=app(reverse?ar(eq):al(eq),al(sp));
            const inn=replace(goal[2],goal[1],i)[2];
            return ei(goal,i,ai(al(ip),ei(inn,s,ai(v,ar(sp)))));
          }));
        }
        const ex=replace(newU[2],newU[1],x)[2][1];
        return ai(ii(M(x,r),xr=>move(from(old,x,xr),ex,false)),ii(ex,p=>into(old,x,move(p,ar(ue(old,x)).goal[1],true))));
      });
      return or(target[1],ai(al(ls),union));
    });
  }
  const stageTransfer=qs(4,(f,g,b,r)=>ii(eqvVals(f,g,b),eq=>ii(Stage(f,b,r),st=>transfer(f,g,b,r,eq,st))));
  function withLimitValue(f,b,g,fn){
    const i=fresh(),v=fresh(),spec={name:"replacement",params:1,body:db(Val(f,i,v),[v,i,f])};
    const img=app(us(ax(spec),f,b),ar(g));
    return open(img,(s,sp)=>withUnion(s,(r,rp)=>{
      const lim=Stage(f,b,r)[2][2];
      const proof=ui(x=>{
        const ex=replace(lim[2],lim[1],x)[2][1];
        const left=ii(M(x,r),xr=>open(from(rp,x,xr),(y,yp)=>open(from(sp,y,al(yp)),(j,jp)=>{
          const inn=replace(ex[2],ex[1],j)[2];
          return ei(ex,j,ai(al(jp),ei(inn,y,ai(ar(jp),ar(yp)))));
        })));
        const right=ii(ex,p=>open(p,(i,ip)=>open(ar(ip),(y,yp)=>{
          const sy=into(sp,y,ei(ar(ue(sp,y)).goal[1],i,ai(al(ip),al(yp))));
          return into(rp,x,ei(ar(ue(rp,x)).goal[1],y,ai(sy,ar(yp))));
        })));
        return ai(left,right);
      });
      return use(proof,p=>fn(r,p));
    }));
  }
  const limitValue=qs(2,(f,b)=>ii(Graph(f,b),g=>withLimitValue(f,b,g,(r,p)=>ei(E(r=>Stage(f,b,r)[2][2]),r,p))));
  function withStageValue(f,b,g,fn){
    const pred=E(i=>C(M(i,b),Succ(i,b)));
    const goal=E(r=>Stage(f,b,r));
    const existence=oe(em(pred),goal,sp=>{
      return open(sp,(i,ip)=>open(app(ue(ar(g),i),al(ip)),(a,ap)=>open(ue(defEx,a),(r,dr)=>{
        const st=Stage(f,b,r),inn=replace(st[1][2],st[1][1],i)[2][2];
        const sr=ol(ei(st[1],i,ai(al(ip),ai(ar(ip),ei(inn,a,ai(al(ap),dr))))),st[2]);
        return ei(goal,r,sr);
      })));
    },lp=>withLimitValue(f,b,g,(r,p)=>ei(goal,r,or(Stage(f,b,r)[1],ai(lp,p)))));
    return open(existence,fn);
  }
  const stageTotal=qs(2,(f,b)=>ii(Graph(f,b),g=>withStageValue(f,b,g,(r,p)=>ei(E(r=>Stage(f,b,r)),r,p))));

  function extendHistory(f,b,d,tb,sd,sf,inj,dom,nc,tot,tr){
    const g0=al(sf),noSelf=ii(M(b,b),bb=>app(us(nc,b,b),bb,bb));
    return use(noSelf,nb=>open(app(us(tot,f,b),g0),(r,rs)=>{
      return open(us(pairEx,b,r),(p,pp)=>{
        return withAdjoin(f,p,(g,gp)=>{
          const valCases=(i,y,v)=>open(v,(w,wp)=>{
            const goal=["|",Val(f,i,y),C(Q(i,b),Q(y,r))];
            return oe(from(gp,w,al(wp)),goal,
              wf=>ol(ei(Val(f,i,y),w,ai(wf,ar(wp))),goal[2]),
              eq=>or(goal[1],app(us(inj,p,i,y,b,r),eqSub(eq,t=>form("pair",t,i,y),ar(wp)),pp)));
          });
          const oldToNew=(i,y,v)=>open(v,(w,wp)=>{
            const wg=into(gp,w,ol(al(wp),Q(w,p)));
            return ei(Val(g,i,y),w,ai(wg,ar(wp)));
          });
          const newValue=ei(Val(g,b,r),p,ai(into(gp,p,or(M(p,f),ref(p))),pp));
          const oldEquiv=ui(i=>ii(M(i,b),ib=>ui(y=>ai(
            ii(Val(f,i,y),v=>oldToNew(i,y,v)),
            ii(Val(g,i,y),v=>oe(valCases(i,y,v),Val(f,i,y),q=>q,eq=>fe(app(nb,eqSub(al(eq),t=>M(t,b),ib)),Val(f,i,y))))))));
          return use(oldEquiv,eqv=>{
            const entries=ui(w=>ii(M(w,g),wg=>{
              const goal=E(i=>C(M(i,d),E(y=>form("pair",w,i,y))));
              return oe(from(gp,w,wg),goal,
                wf=>open(app(ue(al(g0),w),wf),(i,ip)=>{
                  const id=into(sd,i,ol(al(ip),Q(i,b)));
                  return ei(goal,i,ai(id,ar(ip)));
                }),
                eq=>{
                  const bd=into(sd,b,or(M(b,b),ref(b)));
                  const sub=replace(goal[2],goal[1],b)[2];
                  return ei(goal,b,ai(bd,ei(sub,r,eqSub(sym(eq),t=>form("pair",t,b,r),pp))));
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
            const steps=ui(i=>ii(M(i,d),id=>{
              const goal=E(y=>C(Val(g,i,y),Stage(g,i,y)));
              return oe(from(sd,i,id),goal,
                ib=>open(app(ue(ar(sf),i),ib),(y,yp)=>{
                  const v=app(al(ue(app(ue(eqv,i),ib),y)),al(yp));
                  const local=ui(j=>ii(M(j,i),ji=>app(ue(eqv,j),earlier(tb,i,ib,j,ji))));
                  const st=app(us(tr,f,g,i,y),local,ar(yp));
                  return ei(goal,y,ai(v,st));
                }),
                eq=>{
                  const st=app(us(tr,f,g,b,r),eqv,rs);
                  const v=eqSub(sym(eq),t=>C(Val(g,t,r),Stage(g,t,r)),ai(newValue,st));
                  return ei(goal,r,v);
                });
            }));
            return ei(E(z=>SG(z,d)),g,ai(ai(entries,total),steps));
          });
        });
      });
    }));
  }
  const extend=use(pairInj,inj=>use(domainLemma,dom=>use(noCycle,nc=>use(stageTotal,tot=>use(stageTransfer,tr=>{
    return qs(3,(f,b,d)=>ii(trans(b),tb=>ii(Succ(b,d),sd=>ii(SG(f,b),sf=>extendHistory(f,b,d,tb,sd,sf,inj,dom,nc,tot,tr)))));
  })))));
  const emptyGraph=ui(d=>ii(Empty(d),ed=>open(ax({name:"empty"}),(f,ef)=>{
    const entries=ui(p=>ii(M(p,f),pf=>fe(app(ue(ef,p),pf),E(i=>C(M(i,d),E(y=>form("pair",p,i,y)))))));
    const total=ui(i=>ii(M(i,d),id=>fe(app(ue(ed,i),id),E(y=>C(Val(f,i,y),A(z=>I(Val(f,i,z),Q(z,y))))))));
    const stages=ui(i=>ii(M(i,d),id=>fe(app(ue(ed,i),id),E(y=>C(Val(f,i,y),Stage(f,i,y))))));
    return ei(E(f=>SG(f,d)),f,ai(ai(entries,total),stages));
  })));

  const good=(h,e,d)=>C(C(trans(e),subset(e,d)),SG(h,e));
  const goodFamily=(H,d)=>A(h=>I(M(h,H),E(e=>good(h,e,d))));
  const coverFamily=(H,d)=>A(i=>I(M(i,d),E(h=>C(M(h,H),E(e=>C(good(h,e,d),M(i,e)))))));
  function glue(H,d,ok,cover,dom,co,tr){
    return withUnion(H,(u,up)=>{
      function fromFamily(h,p,hH,ph){
        return into(up,p,ei(ar(ue(up,p)).goal[1],h,ai(hH,ph)));
      }
      function fromValue(h,i,r,hH,v){
        return open(v,(p,pv)=>ei(Val(u,i,r),p,ai(fromFamily(h,p,hH,al(pv)),ar(pv))));
      }
      function openValue(i,r,v,fn){
        return open(v,(p,pv)=>open(from(up,p,al(pv)),(h,hp)=>{
          const hv=ei(Val(h,i,r),p,ai(ar(hp),ar(pv)));
          return open(app(ue(ok,h),al(hp)),(e,ep)=>{
            const ie=app(us(dom,h,e,i,r),al(ar(ep)),hv);
            return fn(h,e,al(hp),ep,ie,hv);
          });
        }));
      }
      // A union value on a member history's domain agrees with that
      // history. Existence of a value comes from its exact graph.
      function localEq(h,e,hH,ep){
        return ui(i=>ii(M(i,e),ie0=>ui(r=>ai(
          ii(Val(h,i,r),hv=>fromValue(h,i,r,hH,hv)),
          ii(Val(u,i,r),uv=>openValue(i,r,uv,(j,c,jH,cp,ic,jv)=>{
            return open(app(ue(ar(ar(ep)),i),ie0),(y,yp)=>{
              const eqs=app(us(co,j,h,c,e),al(al(cp)),al(al(ep)),ar(cp),ar(ep));
              const eq=app(ue(app(ue(app(ue(eqs,i),ic,ie0),r),jv),y),al(yp));
              return eqSub(sym(eq),z=>Val(h,i,z),al(yp));
            });
          }))
        ))));
      }
      function covered(i,id,fn){
        return open(app(ue(cover,i),id),(h,hp)=>open(ar(hp),(e,ep)=>fn(h,e,al(hp),al(ep),ar(ep))));
      }
      const entries=ui(p=>ii(M(p,u),pu=>{
        return open(from(up,p,pu),(h,hp)=>open(app(ue(ok,h),al(hp)),(e,ep)=>{
          return open(app(ue(al(al(ar(ep))),p),ar(hp)),(i,ip)=>{
            const id=app(ue(ar(al(ep)),i),al(ip));
            return ei(E(i=>C(M(i,d),E(y=>form("pair",p,i,y)))),i,ai(id,ar(ip)));
          });
        }));
      }));
      const total=ui(i=>ii(M(i,d),id=>covered(i,id,(h,e,hH,ep,ie0)=>{
        const eqv=localEq(h,e,hH,ep);
        return open(app(ue(ar(al(ar(ep))),i),ie0),(r,rp)=>{
          return use(app(ue(eqv,i),ie0),at=>{
            const uv=app(al(ue(at,r)),al(rp));
            const uniq=ui(y=>ii(Val(u,i,y),yv=>app(ue(ar(rp),y),app(ar(ue(at,y)),yv))));
            return ei(E(r=>C(Val(u,i,r),A(y=>I(Val(u,i,y),Q(y,r))))),r,ai(uv,uniq));
          });
        });
      })));
      const steps=ui(i=>ii(M(i,d),id=>covered(i,id,(h,e,hH,ep,ie0)=>{
        return open(app(ue(ar(ar(ep)),i),ie0),(r,rp)=>{
          const eqv=localEq(h,e,hH,ep);
          return use(eqv,ev=>{
            const uv=app(al(ue(app(ue(ev,i),ie0),r)),al(rp));
            const sub=ui(j=>ii(M(j,i),ji=>app(ue(ev,j),earlier(al(al(ep)),i,ie0,j,ji))));
            const st=app(us(tr,h,u,i,r),sub,ar(rp));
            return ei(E(r=>C(Val(u,i,r),Stage(u,i,r))),r,ai(uv,st));
          });
        });
      })));
      return ei(E(f=>SG(f,d)),u,ai(ai(entries,total),steps));
    });
  }
  const glueHistories=use(domainLemma,dom=>use(coh,co=>use(stageTransfer,tr=>{
    return qs(2,(H,d)=>ii(goodFamily(H,d),ok=>ii(coverFamily(H,d),cv=>glue(H,d,ok,cv,dom,co,tr))));
  })));
  function boundedInduction(property,paramCount){
    function quantify(ps){
      if(ps.length<paramCount)return ui(p=>quantify([...ps,p]));
      const PAt=x=>named(property,[x,...ps]);
      const step=a=>A(y=>I(M(y,a),I(A(z=>I(M(z,y),PAt(z))),PAt(y))));
      return ui(a=>ii(trans(a),ta=>ii(step(a),st=>ui(x=>ii(M(x,a),xa=>{
        const v=fresh(),spec={name:"separation",params:paramCount,body:db(N(PAt(v)),[v,...ps])};
        let sep=ax(spec);
        for(const p of ps.slice().reverse())sep=ue(sep,p);
        sep=ue(sep,a);
        const nn=ii(N(PAt(x)),nx=>{
          return ee(sep,F,(bad,sb)=>{
            const xb=ie(ar(ue(sb,x)),ai(xa,nx));
            const nz=E(y=>M(y,bad));
            const found=ie(ue(ax({name:"foundation"}),bad),ei(nz,x,xb));
            return ee(found,F,(y,fy)=>{
              const by=ie(al(ue(sb,y)),al(fy)),ya=al(by),ny=ar(by);
              const pred=ui(z=>ii(M(z,y),zy=>{
                const za=ie(ue(ie(ue(ta,y),ya),z),zy);
                return dn(ii(N(PAt(z)),nz=>{
                  const zb=ie(ar(ue(sb,z)),ai(za,nz));
                  return ie(ie(ue(ar(fy),z),zy),zb);
                }));
              }));
              return ie(ny,ie(ie(ue(st,y),ya),pred));
            });
          });
        });
        return dn(nn);
      })))));
    }
    return quantify([]);
  }

  const Hist=(i,h)=>E(e=>C(Succ(i,e),SG(h,e)));
  const Prop=i=>I(Ord(i),E(h=>Hist(i,h)));
  const histUnique=use(succUnique,su=>use(unique,un=>use(succTrans,st=>{
    return qs(3,(i,h,g)=>ii(trans(i),ti=>ii(Hist(i,h),hh=>ii(Hist(i,g),gg=>{
      return open(hh,(d,dp)=>open(gg,(e,ep)=>{
        const de=app(us(su,i,d,e),al(dp),al(ep));
        const td=app(us(st,i,d),ti,al(dp));
        return app(us(un,h,g,d),td,ar(dp),eqSub(sym(de),x=>SG(g,x),ar(ep)));
      }));
    }))));
  })));
  function ordinalMember(b,i,ob,ib){
    const ti=app(ue(ar(ob),i),ib);
    const members=ui(j=>ii(M(j,i),ji=>app(ue(ar(ob),j),earlier(al(ob),i,ib,j,ji))));
    return ai(ti,members);
  }
  const ordinalMemberProof=qs(2,(b,i)=>ii(Ord(b),ob=>ii(M(i,b),ib=>ordinalMember(b,i,ob,ib))));
  function histStep(b,ob,ih,hu,gl,ext,suc,st){
    function getHist(i,ib){return app(app(ue(ih,i),ib),ordinalMember(b,i,ob,ib));}
    function histGood(i,ib,h,hh){
      return open(hh,(e,ep)=>{
        const ti=app(ue(ar(ob),i),ib);
        const te=app(us(st,i,e),ti,al(ep));
        const inc=ui(j=>ii(M(j,e),je=>oe(from(al(ep),j,je),M(j,b),ji=>earlier(al(ob),i,ib,j,ji),eq=>eqSub(sym(eq),z=>M(z,b),ib))));
        const ie0=into(al(ep),i,or(M(i,i),ref(i)));
        return ei(E(e=>C(good(h,e,b),M(i,e))),e,ai(ai(ai(te,inc),ar(ep)),ie0));
      });
    }
    const i0=fresh(),h0=fresh(),spec={name:"replacement",params:0,body:db(Hist(i0,h0),[h0,i0])};
    const total=ui(i=>ii(M(i,b),ib=>open(getHist(i,ib),(h,hh)=>{
      const ti=app(ue(ar(ob),i),ib);
      const un=ui(g=>ii(Hist(i,g),gg=>app(us(hu,i,g,h),ti,gg,hh)));
      return ei(E(h=>C(Hist(i,h),A(g=>I(Hist(i,g),Q(g,h))))),h,ai(hh,un));
    })));
    return open(app(ue(ax(spec),b),total),(H,img)=>{
      const ok=ui(h=>ii(M(h,H),hH=>open(from(img,h,hH),(i,ip)=>{
        return open(histGood(i,al(ip),h,ar(ip)),(e,ep)=>ei(E(e=>good(h,e,b)),e,al(ep)));
      })));
      const cv=ui(i=>ii(M(i,b),ib=>open(getHist(i,ib),(h,hh)=>{
        const hH=into(img,h,ei(ar(ue(img,h)).goal[1],i,ai(ib,hh)));
        const hg=histGood(i,ib,h,hh);
        return ei(E(h=>C(M(h,H),E(e=>C(good(h,e,b),M(i,e))))),h,ai(hH,hg));
      })));
      return open(app(us(gl,H,b),ok,cv),(f,sf)=>{
        return open(ue(suc,b),(d,sd)=>{
          return open(app(us(ext,f,b,d),al(ob),sd,sf),(g,sg)=>{
            return ei(E(h=>Hist(b,h)),g,ei(Hist(b,g),d,ai(sd,sg)));
          });
        });
      });
    });
  }
  const b0=fresh(),existInd=boundedInduction(db(Prop(b0),[b0]),0);
  const successorHistoryExistence=use(histUnique,hu=>use(glueHistories,gl=>use(extend,ext=>use(successorExists,suc=>use(succTrans,st=>{
    return ui(b=>ii(Ord(b),ob=>{
      return open(ue(suc,b),(d,sd)=>{
        const td=app(us(st,b,d),al(ob),sd);
        const step=ui(i=>ii(M(i,d),id=>ii(A(j=>I(M(j,i),Prop(j))),ih=>ii(Ord(i),oi=>histStep(i,oi,ih,hu,gl,ext,suc,st)))));
        const all=app(ue(existInd,d),td,step);
        const bd=into(sd,b,or(M(b,b),ref(b)));
        return app(app(ue(all,b),bd),ob);
      });
    }));
  })))));
  const historyExists=use(successorHistoryExistence,he=>use(restrict,re=>ui(b=>ii(Ord(b),ob=>{
    return open(app(ue(he,b),ob),(g,gh)=>open(gh,(d,dh)=>{
      const inc=ui(i=>ii(M(i,b),ib=>into(al(dh),i,ol(ib,Q(i,b)))));
      return open(app(us(re,g,d,b),al(ob),inc,ar(dh)),(f,fp)=>ei(E(f=>SG(f,b)),f,al(fp)));
    }));
  }))));
  const historyExistsUnique=use(historyExists,he=>use(unique,un=>ui(b=>ii(Ord(b),ob=>{
    return open(app(ue(he,b),ob),(f,sf)=>{
      const uq=ui(g=>ii(SG(g,b),sg=>app(us(un,g,f,b),al(ob),sg,sf)));
      return ei(E(f=>C(SG(f,b),A(g=>I(SG(g,b),Q(g,f))))),f,ai(sf,uq));
    });
  }))));

  const stageWitness=(b,r)=>E(d=>C(Succ(b,d),E(f=>C(SG(f,d),Val(f,b,r)))));
  const ordinalValueExists=use(successorHistoryExistence,he=>ui(b=>ii(Ord(b),ob=>{
    return open(app(ue(he,b),ob),(f,fh)=>open(fh,(d,dh)=>{
      const bd=into(al(dh),b,or(M(b,b),ref(b)));
      return open(app(ue(ar(al(ar(dh))),b),bd),(r,rp)=>{
        const witness=stageWitness(b,r),inner=replace(witness[2],witness[1],d)[2];
        return ei(E(r=>stageWitness(b,r)),r,ei(witness,d,ai(al(dh),ei(inner,f,ai(ar(dh),al(rp))))));
      });
    }));
  })));
  const ordinalValueUnique=use(coh,co=>use(succTrans,st=>qs(3,(b,r,s)=>ii(Ord(b),ob=>ii(stageWitness(b,r),rw=>ii(stageWitness(b,s),sw=>{
    return open(rw,(d,dp)=>open(ar(dp),(f,fp)=>open(sw,(e,ep)=>open(ar(ep),(g,gp)=>{
      const td=app(us(st,b,d),al(ob),al(dp)),te=app(us(st,b,e),al(ob),al(ep));
      const bd=into(al(dp),b,or(M(b,b),ref(b))),be=into(al(ep),b,or(M(b,b),ref(b)));
      const eq=app(us(co,f,g,d,e),td,te,al(fp),al(gp));
      return app(ue(app(ue(app(ue(eq,b),bd,be),r),ar(fp)),s),ar(gp));
    }))));
  }))))));
  const stageMembersL=qs(2,(b,r)=>ii(Ord(b),ob=>ii(stageWitness(b,r),rw=>ui(x=>ii(M(x,r),xr=>{
    return open(rw,(d,dp)=>open(ar(dp),(f,fp)=>{
      const goal=form("L",x);
      const aBody=replace(goal[2],goal[1],b),dGoal=aBody[2];
      const dBody=replace(dGoal[2],dGoal[1],d),fGoal=dBody[2];
      const fBody=replace(fGoal[2],fGoal[1],f),rGoal=fBody[2];
      return ei(goal,b,ai(ob,ei(dGoal,d,ai(al(dp),ei(fGoal,f,ai(al(fp),ei(rGoal,r,ai(ar(fp),xr))))))));
    }));
  })))));
  const proofs={successor_exists:successorExists,successor_unique:succUnique,value_in_domain:domainLemma,subset_reflexive:reflSub,stage_value_transport:stageTransfer,limit_value_exists:limitValue,stage_value_exists:stageTotal,stage_history_extension:extend,empty_history_exists:emptyGraph,compatible_history_union:glueHistories,successor_history_unique:histUnique,ordinal_member:ordinalMemberProof,history_existence_induction:existInd,successor_history_exists:successorHistoryExistence,ordinal_history_exists:historyExists,ordinal_history_exists_unique:historyExistsUnique,ordinal_stage_value_exists:ordinalValueExists,ordinal_stage_value_unique:ordinalValueUnique,stage_members_constructible:stageMembersL};

  if(extended){
    const ordinalSucc=use(succTrans,st=>qs(2,(a,d)=>ii(Ord(a),oa=>ii(Succ(a,d),sd=>{
      const td=app(us(st,a,d),al(oa),sd);
      const members=ui(x=>ii(M(x,d),xd=>oe(from(sd,x,xd),trans(x),xa=>app(ue(ar(oa),x),xa),eq=>eqSub(sym(eq),trans,al(oa)))));
      return ai(td,members);
    }))));
    const unionSpec=(a,b,c)=>A(x=>B(M(x,c),["|",M(x,a),M(x,b)]));
    function withBinaryUnion(a,b,fn){
      return withSetPair(a,b,(p,pp)=>withUnion(p,(c,cp)=>{
        const ap=into(pp,a,ol(ref(a),Q(a,b))),bp=into(pp,b,or(Q(b,a),ref(b)));
        const spec=ui(x=>{
          const left=ii(M(x,c),xc=>open(from(cp,x,xc),(y,yp)=>{
            const want=["|",M(x,a),M(x,b)];
            return oe(from(pp,y,al(yp)),want,
              ya=>ol(eqSub(ya,t=>M(x,t),ar(yp)),M(x,b)),
              yb=>or(M(x,a),eqSub(yb,t=>M(x,t),ar(yp))));
          }));
          const right=ii(["|",M(x,a),M(x,b)],p=>{
            const ex=ar(ue(cp,x)).goal[1];
            return oe(p,M(x,c),xa=>into(cp,x,ei(ex,a,ai(ap,xa))),xb=>into(cp,x,ei(ex,b,ai(bp,xb))));
          });
          return ai(left,right);
        });
        return use(spec,sp=>fn(c,sp));
      }));
    }
    const binaryUnionExists=qs(2,(a,b)=>withBinaryUnion(a,b,(c,cp)=>ei(E(c=>unionSpec(a,b,c)),c,cp)));
    function ordUnion(a,b,c,oa,ob,cp){
      const tr=ui(x=>ii(M(x,c),xc=>ui(y=>ii(M(y,x),yx=>{
        return oe(from(cp,x,xc),M(y,c),
          xa=>into(cp,y,ol(app(ue(app(ue(al(oa),x),xa),y),yx),M(y,b))),
          xb=>into(cp,y,or(M(y,a),app(ue(app(ue(al(ob),x),xb),y),yx))));
      }))));
      const members=ui(x=>ii(M(x,c),xc=>oe(from(cp,x,xc),trans(x),
        xa=>app(ue(ar(oa),x),xa),xb=>app(ue(ar(ob),x),xb))));
      return ai(tr,members);
    }
    const ordinalUnion=qs(3,(a,b,c)=>ii(Ord(a),oa=>ii(Ord(b),ob=>ii(unionSpec(a,b,c),cp=>ordUnion(a,b,c,oa,ob,cp)))));
    function stageW(w,fn){return open(w,(d,dp)=>open(ar(dp),(f,fp)=>fn(d,f,al(dp),al(fp),ar(fp))));}
    const stageTransP=imported({goal:prior.stage_transitivity_conditional.goal[2],proof:["iE",prior.stage_transitivity_conditional.proof,finite.def_inflation.proof]});
    const crossMonoP=imported({goal:prior.cross_graph_monotonicity_conditional.goal[2],proof:["iE",prior.cross_graph_monotonicity_conditional.proof,finite.def_inflation.proof]});
    const ordinalValueTrans=use(stageTransP,st=>use(succTrans,su=>qs(2,(b,r)=>ii(Ord(b),ob=>ii(stageWitness(b,r),rw=>{
      return stageW(rw,(d,f,sd,sf,vr)=>{
        const td=app(us(su,b,d),al(ob),sd),bd=into(sd,b,or(M(b,b),ref(b)));
        const stages=app(us(st,f,d),td,sf);
        return app(ue(app(ue(stages,b),bd),r),vr);
      });
    })))));
    function stageIncl(a,b,r,s,oa,ob,rw,sw,ab,cm,st){
      return stageW(rw,(d,f,sd,sf,vr)=>stageW(sw,(e,g,se,sg,vs)=>{
        const td=app(us(st,a,d),al(oa),sd),te=app(us(st,b,e),al(ob),se);
        const ad=into(sd,a,or(M(a,a),ref(a))),be=into(se,b,or(M(b,b),ref(b)));
        const mo=app(us(cm,f,g,d,e),td,te,sf,sg);
        return app(ue(app(ue(app(ue(app(ue(mo,a),ad),b),be,ab),r),vr),s),vs);
      }));
    }
    const ordinalValueMono=use(crossMonoP,cm=>use(succTrans,st=>qs(4,(a,b,r,s)=>ii(Ord(a),oa=>ii(Ord(b),ob=>ii(stageWitness(a,r),rw=>ii(stageWitness(b,s),sw=>ii(M(a,b),ab=>stageIncl(a,b,r,s,oa,ob,rw,sw,ab,cm,st)))))))));
    function unpackL(x,lx,fn){
      return open(lx,(a,ap)=>open(ar(ap),(d,dp)=>open(ar(dp),(f,fp)=>open(ar(fp),(r,rp)=>{
        const w=stageWitness(a,r),inner=replace(w[2],w[1],d)[2];
        const wp=ei(w,d,ai(al(dp),ei(inner,f,ai(al(fp),al(rp)))));
        return fn(a,r,al(ap),wp,ar(rp),d,al(dp));
      }))));
    }
    const lCommon=use(ordinalSucc,os=>use(ordinalValueExists,ov=>use(ordinalValueMono,om=>use(ordinalValueTrans,ot=>{
      return qs(2,(x,y)=>ii(form("L",x),lx=>ii(form("L",y),ly=>{
        return unpackL(x,lx,(a,r,oa,rw,xr,d,sd)=>unpackL(y,ly,(b,s,ob,sw,ys,e,se)=>{
          const od=app(us(os,a,d),oa,sd),oe0=app(us(os,b,e),ob,se);
          return withBinaryUnion(d,e,(c,cp)=>{
            const oc=ordUnion(d,e,c,od,oe0,cp);
            const ac=into(cp,a,ol(into(sd,a,or(M(a,a),ref(a))),M(a,e)));
            const bc=into(cp,b,or(M(b,d),into(se,b,or(M(b,b),ref(b)))));
            return open(app(ue(ov,c),oc),(t,tw)=>{
              const rt=app(us(om,a,c,r,t),oa,oc,rw,tw,ac),st=app(us(om,b,c,s,t),ob,oc,sw,tw,bc);
              const tt=app(us(ot,c,t),oc,tw);
              const body=(c,t)=>C(C(C(Ord(c),stageWitness(c,t)),trans(t)),C(M(x,t),M(y,t)));
              const goal=E(c=>E(t=>body(c,t)));
              return ei(goal,c,ei(replace(goal[2],goal[1],c),t,ai(ai(ai(oc,tw),tt),ai(app(ue(rt,x),xr),app(ue(st,y),ys)))));
            });
          });
        }));
      })));
    }))));
    const predUnique=imported(prior.successor_predecessor_unique);
    function valueEq(sg,i,id,x,y,vx,vy){
      return open(app(ue(ar(al(sg)),i),id),(v,uv)=>{
        return chain(app(ue(ar(uv),x),vx),sym(app(ue(ar(uv),y),vy)));
      });
    }
    const successorDef=use(coh,co=>use(succTrans,st=>use(predUnique,pu=>{
      return qs(4,(a,b,r,s)=>ii(Ord(a),oa=>ii(Ord(b),ob=>ii(Succ(a,b),ab=>ii(stageWitness(a,r),rw=>ii(stageWitness(b,s),sw=>{
        return stageW(rw,(d,f,sd,sf,vr)=>stageW(sw,(e,g,se,sg,vs)=>{
          const td=app(us(st,a,d),al(oa),sd),te=app(us(st,b,e),al(ob),se);
          const ad=into(sd,a,or(M(a,a),ref(a))),be=into(se,b,or(M(b,b),ref(b)));
          const aa=into(ab,a,or(M(a,a),ref(a))),ae=into(se,a,ol(aa,Q(a,b)));
          const eq=app(us(co,f,g,d,e),td,te,sf,sg);
          return open(app(ue(ar(sg),b),be),(t,tp)=>{
            const ts=valueEq(sg,b,be,t,s,al(tp),vs);
            const goal=Def(r,t),stage=ar(tp);
            const dr=oe(stage,goal,ss=>open(ss,(i,ip)=>open(ar(ar(ip)),(v,vp)=>{
              const ia=app(us(pu,i,a,b),al(ar(ip)),ab);
              const av=eqSub(ia,z=>Val(g,z,v),al(vp));
              const rv=app(ue(app(ue(app(ue(eq,a),ad,ae),r),vr),v),av);
              return eqSub(sym(rv),z=>Def(z,t),ar(vp));
            })),ls=>{
              const ex=al(ls).goal[1];
              return fe(app(al(ls),ei(ex,a,ai(aa,ab))),goal);
            });
            return eqSub(ts,z=>Def(r,z),dr);
          });
        }));
      }))))));
    })));
    const definableConstructible=use(ordinalSucc,os=>use(successorExists,se=>use(ordinalValueExists,ov=>use(successorDef,sd=>use(stageMembersL,ml=>{
      return qs(3,(a,r,x)=>ii(Ord(a),oa=>ii(stageWitness(a,r),rw=>ii(D(r,x),dx=>{
        return open(ue(se,a),(b,ab)=>{
          const ob=app(us(os,a,b),oa,ab);
          return open(app(ue(ov,b),ob),(s,sw)=>{
            const df=app(us(sd,a,b,r,s),oa,ob,ab,rw,sw);
            const xs=into(df,x,dx);
            return app(ue(app(us(ml,b,s),ob,sw),x),xs);
          });
        });
      }))));
    })))));
    Object.assign(proofs,{ordinal_successor:ordinalSucc,binary_union_exists:binaryUnionExists,ordinal_binary_union:ordinalUnion,ordinal_stage_value_transitive:ordinalValueTrans,ordinal_stage_value_monotone:ordinalValueMono,common_constructible_stage:lCommon,successor_stage_def:successorDef,definable_subset_constructible:definableConstructible});
  }
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}


import { readFileSync } from 'node:fs';

function runI(pinned){
  const defs=definition("v",true),prior=buildE(defs,true),finite=buildF(defs),p=buildI(defs,prior,finite),out={};
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  for(const [name,v] of Object.entries(p)){
    const r=kernel(0,[],v.proof,false,"ZF");
    if(!same(r.goal,v.goal))throw Error("goal mismatch "+name);
    out[name]={nodes:r.visits,proof_bytes:JSON.stringify(v.proof).length};
  }
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){
      const f=i=>i<d?i:indices[i-d]+d;
      return [op,f(a),f(b)];
    }
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b];
  const all=(n,p)=>{for(let i=0;i<n;i++)p=A(p);return p;};
  const imp=(...ps)=>ps.reduceRight((a,b)=>I(b,a));
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const SG=(f,d)=>embed(defs.stageGraph,[f,d]),V=(f,i,r)=>embed(defs.val,[f,i,r]);
  const Succ=(b,d)=>embed(defs.successor,[b,d]),Ord=b=>embed(defs.ordinal,[b]);
  const Graph=(f,b)=>embed(defs.graph,[f,b]),Stage=(f,b,r)=>embed(defs.stage,[f,b,r]);
  const Hist=(b,h)=>E(C(Succ(b+1,0),SG(h+1,0)));
  const W=(b,r)=>E(C(Succ(b+1,0),E(C(SG(0,1),V(0,b+2,r+2)))));
  const goals={
    stage_value_exists:all(2,I(Graph(1,0),E(Stage(2,1,0)))),
    stage_history_extension:all(3,imp(trans(1),Succ(1,0),SG(2,1),E(SG(0,1)))),
    successor_history_exists:A(I(Ord(0),E(Hist(1,0)))),
    ordinal_history_exists:A(I(Ord(0),E(SG(0,1)))),
    ordinal_history_exists_unique:A(I(Ord(0),E(C(SG(0,1),A(I(SG(0,2),Q(0,1))))))),
    ordinal_stage_value_exists:A(I(Ord(0),E(W(1,0)))),
    ordinal_stage_value_unique:all(3,imp(Ord(2),W(2,1),W(2,0),Q(1,0))),
    stage_members_constructible:all(2,imp(Ord(1),W(1,0),A(I(M(0,1),defs.L))))
  };
  for(const [name,goal] of Object.entries(goals))if(!same(p[name].goal,goal))throw Error("independent goal mismatch "+name);
  const controls=[
    ()=>kernel(0,[],p.ordinal_history_exists_unique.proof,false,"CL"),
    ()=>kernel(0,[],p.compatible_history_union.proof,false,"CL"),
    ()=>kernel(0,[],p.limit_value_exists.proof,false,"CL"),
    ()=>kernel(0,[],p.stage_history_extension.proof,false,"logic"),
    ()=>kernel(0,[],["iE",p.ordinal_history_exists.proof,p.empty_history_exists.proof],false,"ZF"),
    ()=>kernel(0,[],["iE",p.ordinal_stage_value_exists.proof,p.successor_exists.proof],false,"ZF")
  ];
  for(const t of controls)if(!rejects(t))throw Error("negative control accepted");
  return {experiment:"ACE-03I",scope:"closed pure set-language derivations of exact ordinal stage recursion; executable ZF checker",proofs:out,independent_goal_checks:Object.keys(goals).length,negative_controls:controls.length,pinned_L_unchanged:true,remaining:"ordinal comparison, constructible pair and union closure, other L axioms, uniform adequacy and checker soundness"};
}

const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
console.log(JSON.stringify(runI(pinned),null,2));
