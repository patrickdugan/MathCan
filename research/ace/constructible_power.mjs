import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects, inst, expandClass, classProofs, compile } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
function buildL(defs,prior,finite,stages,extended=false){
  let serial=0;
  const fresh=()=>`q${serial++}`,M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b],F=["F"],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],N=p=>I(p,F);
  const bind=(op,f)=>{const x=fresh();return [op,x,f(x)];};
  const A=f=>bind("A",f),E=f=>bind("E",f);
  function named(p,env){
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="G")return [op,env[a]];
    if(op==="M"||op==="=")return [op,env[a],env[b]];
    if(op==="A"||op==="E"){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env){
    const [op,a,b]=p;
    if(op==="F")return F;
    if(op==="G"){const i=env.indexOf(a);if(i<0)throw Error("unbound guard variable");return [op,i];}
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
    if(op==="G")return [op,a===x?y:a];
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


  const se=imported(stages.successor_exists),su=imported(stages.successor_unique),st=imported(prior.ordinal_successor_transitivity);
  const om=imported(stages.ordinal_member),nc=imported(prior.no_two_cycle),os=imported(stages.ordinal_successor);
  const ov=imported(stages.ordinal_stage_value_exists),mono=imported(stages.ordinal_stage_value_monotone);
  const sm=imported(stages.stage_members_constructible),ot=imported(stages.ordinal_stage_value_transitive),dc=imported(stages.definable_subset_constructible);
  const L=x=>form("L",x);
  const W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  const noSelf=ui(x=>ii(M(x,x),xx=>app(us(nc,x,x),xx,xx)));
  const cmp=(a,b)=>["|",M(a,b),["|",Q(a,b),M(b,a)]];
  const cmpP=a=>I(Ord(a),A(b=>I(Ord(b),cmp(a,b))));
  const v0=fresh(),cmpInd=boundedInduction(db(cmpP(v0),[v0]),0);
  function comparisonStep(a,oa,ih,b,ob){
    const target=cmp(a,b);
    return oe(em(M(b,a)),target,ba=>or(M(a,b),or(Q(a,b),ba)),nba=>{
      const ab=ui(x=>ii(M(x,a),xa=>{
        const ox=app(us(om,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),b),ob);
        return oe(cx,M(x,b),xb=>xb,rest=>oe(rest,M(x,b),eq=>{
          return fe(app(nba,eqSub(eq,z=>M(z,a),xa)),M(x,b));
        },bx=>fe(app(nba,app(ue(app(ue(al(oa),x),xa),b),bx)),M(x,b))));
      }));
      const bad=E(y=>C(M(y,b),N(M(y,a))));
      return oe(em(bad),target,some=>{
        const y0=fresh(),spec={name:"separation",params:1,body:db(N(M(y0,a)),[y0,a])};
        return open(us(ax(spec),a,b),(c,cp)=>{
          const ne=open(some,(y,yp)=>ei(E(x=>M(x,c)),y,into(cp,y,yp)));
          return open(app(ue(ax({name:"foundation"}),c),ne),(y,yp)=>{
            const bc=from(cp,y,al(yp)),yb=al(bc),nya=ar(bc),oy=app(us(om,b,y),ob,yb);
            const ya=ui(z=>ii(M(z,y),zy=>dn(ii(N(M(z,a)),nza=>{
              const zb=app(ue(app(ue(al(ob),y),yb),z),zy);
              const zc=into(cp,z,ai(zb,nza));
              return app(app(ue(ar(yp),z),zy),zc);
            }))));
            const ay=ui(x=>ii(M(x,a),xa=>{
              const ox=app(us(om,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),y),oy);
              return oe(cx,M(x,y),xy=>xy,rest=>oe(rest,M(x,y),eq=>fe(app(nya,eqSub(eq,z=>M(z,a),xa)),M(x,y)),yx=>fe(app(nya,app(ue(app(ue(al(oa),x),xa),y),yx)),M(x,y))));
            }));
            const eq=extEq(a,y,x=>ai(ii(M(x,a),xa=>app(ue(ay,x),xa)),ii(M(x,y),xy=>app(ue(ya,x),xy))));
            return ol(eqSub(sym(eq),z=>M(z,b),yb),target[2]);
          });
        });
      },none=>{
        const ba=ui(y=>ii(M(y,b),yb=>dn(ii(N(M(y,a)),nya=>app(none,ei(bad,y,ai(yb,nya)))))));
        const eq=extEq(a,b,x=>ai(ii(M(x,a),xa=>app(ue(ab,x),xa)),ii(M(x,b),xb=>app(ue(ba,x),xb))));
        return or(M(a,b),ol(eq,M(b,a)));
      });
    });
  }
  const compare=use(cmpInd,ind=>ui(a=>ii(Ord(a),oa=>{
    return open(ue(se,a),(d,sd)=>{
      const td=app(us(st,a,d),al(oa),sd),ad=into(sd,a,or(M(a,a),ref(a)));
      const step=ui(i=>ii(M(i,d),id=>ii(A(j=>I(M(j,i),cmpP(j))),ih=>ii(Ord(i),oi=>ui(b=>ii(Ord(b),ob=>comparisonStep(i,oi,ih,b,ob)))))));
      return app(app(ue(app(ue(ind,d),td,step),a),ad),oa);
    });
  })));
  const Appears=(x,a)=>C(Ord(a),E(r=>C(W(a,r),M(x,r))));
  const Rank=(x,a)=>C(Appears(x,a),A(i=>I(M(i,a),N(Appears(x,i)))));
  function unpackL(x,lx,fn){
    return open(lx,(a,ap)=>open(ar(ap),(d,dp)=>open(ar(dp),(f,fp)=>open(ar(fp),(r,rp)=>{
      const w=W(a,r),inner=replace(w[2],w[1],d)[2];
      const wp=ei(w,d,ai(al(dp),ei(inner,f,ai(al(fp),al(rp)))));
      const appear=ai(al(ap),ei(Appears(x,a)[2],r,ai(wp,ar(rp))));
      return fn(a,d,al(dp),appear);
    }))));
  }
  const leastRank=ui(x=>ii(L(x),lx=>unpackL(x,lx,(a,d,sd,ap)=>{
    const v=fresh(),spec={name:"separation",params:1,body:db(Appears(x,v),[v,x])};
    return open(us(ax(spec),x,d),(c,cp)=>{
      const ad=into(sd,a,or(M(a,a),ref(a)));
      const ac=into(cp,a,ai(ad,ap));
      const ne=ei(E(y=>M(y,c)),a,ac);
      const td=app(us(st,a,d),al(al(ap)),sd);
      return open(app(ue(ax({name:"foundation"}),c),ne),(b,bp)=>{
        const bv=from(cp,b,al(bp)),bd=al(bv),appear=ar(bv);
        const minimal=ui(i=>ii(M(i,b),ib=>ii(Appears(x,i),ia=>{
          const id=app(ue(app(ue(td,b),bd),i),ib),ic=into(cp,i,ai(id,ia));
          return app(app(ue(ar(bp),i),ib),ic);
        })));
        return ei(E(b=>Rank(x,b)),b,ai(appear,minimal));
      });
    });
  })));
  const rankUnique=use(compare,cmp0=>qs(3,(x,a,b)=>ii(Rank(x,a),ra=>ii(Rank(x,b),rb=>{
    const cc=app(ue(app(ue(cmp0,a),al(al(ra))),b),al(al(rb)));
    return oe(cc,Q(a,b),ab=>fe(app(app(ue(ar(rb),a),ab),al(ra)),Q(a,b)),rest=>oe(rest,Q(a,b),eq=>eq,ba=>fe(app(app(ue(ar(ra),b),ba),al(rb)),Q(a,b))));
  }))));
  const rankExistsUnique=use(leastRank,lr=>use(rankUnique,ru=>ui(x=>ii(L(x),lx=>{
    return open(app(ue(lr,x),lx),(a,ra)=>{
      const uq=ui(b=>ii(Rank(x,b),rb=>app(us(ru,x,b,a),rb,ra)));
      return ei(E(a=>C(Rank(x,a),A(b=>I(Rank(x,b),Q(b,a))))),a,ai(ra,uq));
    });
  }))));

  const RankSucc=(x,j)=>E(a=>C(Rank(x,a),Succ(a,j)));
  const rankSuccUnique=use(rankUnique,ru=>qs(3,(x,j,k)=>ii(RankSucc(x,j),rj=>ii(RankSucc(x,k),rk=>{
    return open(rj,(a,ap)=>open(rk,(b,bp)=>{
      const ab=app(us(ru,x,a,b),al(ap),al(bp));
      return app(us(su,b,j,k),eqSub(ab,t=>Succ(t,j),ar(ap)),ar(bp));
    }));
  }))));
  const rankSuccTotal=use(leastRank,lr=>use(rankSuccUnique,ru=>ui(x=>ii(L(x),lx=>{
    return open(app(ue(lr,x),lx),(a,ra)=>open(ue(se,a),(j,jp)=>{
      const rj=ei(RankSucc(x,j),a,ai(ra,jp));
      const uq=ui(k=>ii(RankSucc(x,k),rk=>app(us(ru,x,k,j),rk,rj)));
      return ei(E(j=>C(RankSucc(x,j),A(k=>I(RankSucc(x,k),Q(k,j))))),j,ai(rj,uq));
    }));
  }))));
  const allL=a=>A(x=>I(M(x,a),L(x)));
  const ordinalFamily=a=>A(x=>I(M(x,a),Ord(x)));
  const unionSpec=(a,b)=>A(x=>B(M(x,b),E(y=>C(M(y,a),M(x,y)))));
  function ordinalUnion(a,b,of,ub){
    const tr=ui(x=>ii(M(x,b),xb=>ui(y=>ii(M(y,x),yx=>{
      return open(from(ub,x,xb),(i,ip)=>{
        const oi=app(ue(of,i),al(ip));
        const yi=app(ue(app(ue(al(oi),x),ar(ip)),y),yx);
        return into(ub,y,ei(ar(ue(ub,y)).goal[1],i,ai(al(ip),yi)));
      });
    }))));
    const each=ui(x=>ii(M(x,b),xb=>open(from(ub,x,xb),(i,ip)=>{
      const oi=app(ue(of,i),al(ip));
      return app(ue(ar(oi),x),ar(ip));
    })));
    return ai(tr,each);
  }
  const ordinalUnionProof=qs(2,(a,b)=>ii(ordinalFamily(a),of=>ii(unionSpec(a,b),ub=>ordinalUnion(a,b,of,ub))));
  const withUnion=(a,fn)=>open(ue(ax({name:"union"}),a),fn);
  const Bound=(a,c,r)=>C(C(Ord(c),W(c,r)),subset(a,r));
  function boundSet(a,al0,rs,ou,ve,mo){
    const x0=fresh(),j0=fresh(),spec={name:"replacement",params:0,body:db(RankSucc(x0,j0),[j0,x0])};
    const functional=ui(x=>ii(M(x,a),xa=>app(ue(rs,x),app(ue(al0,x),xa))));
    return open(app(ue(ax(spec),a),functional),(R,Rp)=>{
      const ords=ui(j=>ii(M(j,R),jr=>open(from(Rp,j,jr),(x,xp)=>open(ar(xp),(i,ip)=>{
        return app(us(os,i,j),al(al(al(ip))),ar(ip));
      }))));
      return withUnion(R,(c,uc)=>{
        const oc=app(us(ou,R,c),ords,uc);
        return use(oc,ord=>open(app(ue(ve,c),ord),(r,rw)=>{
          const inc=ui(x=>ii(M(x,a),xa=>{
            return open(app(ue(rs,x),app(ue(al0,x),xa)),(j,jp)=>{
              const jR=into(Rp,j,ei(ar(ue(Rp,j)).goal[1],x,ai(xa,al(jp))));
              return open(al(jp),(i,ip)=>{
                const rank=al(ip),succ=ar(ip),oi=al(al(rank));
                const ij=into(succ,i,or(M(i,i),ref(i)));
                const ic=into(uc,i,ei(ar(ue(uc,i)).goal[1],j,ai(jR,ij)));
                return open(ar(al(rank)),(s,sp)=>{
                  const sr=app(us(mo,i,c,s,r),oi,ord,al(sp),rw,ic);
                  return app(ue(sr,x),ar(sp));
                });
              });
            });
          }));
          const goal=E(c=>E(r=>Bound(a,c,r)));
          return ei(goal,c,ei(replace(goal[2],goal[1],c),r,ai(ai(ord,rw),inc)));
        }));
      });
    });
  }
  const constructibleSetBound=use(rankSuccTotal,rs=>use(ordinalUnionProof,ou=>use(ov,ve=>use(mono,mo=>ui(a=>ii(allL(a),al0=>boundSet(a,al0,rs,ou,ve,mo)))))));
  const proofs={ordinal_comparison_induction:cmpInd,ordinal_comparison:compare,least_constructible_rank:leastRank,least_rank_unique:rankUnique,least_rank_exists_unique:rankExistsUnique,rank_successor_unique:rankSuccUnique,rank_successor_total:rankSuccTotal,ordinal_family_union:ordinalUnionProof,constructible_set_stage_bound:constructibleSetBound};
  const withSetPair=(a,b,fn)=>open(us(ax({name:"pairing"}),a,b),fn);
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

  if(extended){
    const relativePower=(a,x,p)=>A(y=>B(M(y,p),C(M(y,a),subset(y,x))));
    const constructiblePower=(x,p)=>A(y=>B(M(y,p),C(L(y),subset(y,x))));
    function withRelativePower(x,fn){
      return open(ue(ax({name:"power"}),x),(p0,p0p)=>{
        const v=fresh(),spec={name:"separation",params:0,body:db(L(v),[v])};
        return open(ue(ax(spec),p0),(p,pp)=>{
          const exact=ui(y=>ai(ii(M(y,p),yp=>{
            const info=from(pp,y,yp);
            return ai(ar(info),from(p0p,y,al(info)));
          }),ii(C(L(y),subset(y,x)),q=>into(pp,y,ai(into(p0p,y,ar(q)),al(q))))));
          return use(exact,ep=>fn(p,ep));
        });
      });
    }
    const ambientRelativePower=ui(x=>withRelativePower(x,(p,pp)=>ei(E(p=>constructiblePower(x,p)),p,pp)));
    const pdef=imported(finite.relative_power_definable);
    const powerClosure=use(ambientRelativePower,arp=>use(constructibleSetBound,cb=>use(pdef,pd=>{
      return ui(x=>ii(L(x),lx=>{
        return open(ue(arp,x),(p,pp)=>{
          return withAdjoin(p,x,(u,up)=>{
            const ul=ui(y=>ii(M(y,u),yu=>oe(from(up,y,yu),L(y),yp=>al(from(pp,y,yp)),yx=>eqSub(sym(yx),L,lx))));
            return open(app(ue(cb,u),ul),(b,bp)=>open(bp,(a,ap)=>{
              const ob=al(al(ap)),aw=ar(al(ap)),inc=ar(ap);
              const xa=app(ue(inc,x),into(up,x,or(M(x,p),ref(x))));
              const ta=app(us(ot,b,a),ob,aw);
              const ps=ui(y=>ai(ii(M(y,p),yp=>{
                const ya=app(ue(inc,y),into(up,y,ol(yp,Q(y,x))));
                return ai(ya,ar(from(pp,y,yp)));
              }),ii(C(M(y,a),subset(y,x)),q=>{
                const ly=app(ue(app(us(sm,b,a),ob,aw),y),al(q));
                return into(pp,y,ai(ly,ar(q)));
              })));
              const dp=app(us(pd,a,x,p),ta,xa,ps);
              const lp=app(us(dc,b,a,p),ob,aw,dp);
              return ei(E(p=>C(L(p),constructiblePower(x,p))),p,ai(lp,pp));
            }));
          });
        });
      }));
    })));
    Object.assign(proofs,{ambient_relative_powerset_exists:ambientRelativePower,constructible_powerset_closure:powerClosure});
    const G=x=>["G",x];
    function relN(p){
      const [op,a,b]=p;
      if(op==="A")return [op,a,I(G(a),relN(b))];
      if(op==="E")return [op,a,C(G(a),relN(b))];
      if(["&","|",">"].includes(op))return [op,relN(a),relN(b)];
      return p;
    }
    const T=A(a=>A(x=>I(C(G(a),M(x,a)),G(x))));
    const PC=A(x=>I(G(x),E(p=>C(G(p),A(y=>B(M(y,p),C(G(y),subset(y,x))))))));
    const target=relN(ax({name:"power"}).goal);
    const generic=ii(T,t=>ii(PC,pc=>ui(x=>ii(G(x),gx=>{
      return open(app(ue(pc,x),gx),(p,pp)=>{
        const gp=al(pp),power=ar(pp);
        const local=ui(y=>ii(G(y),gy=>{
          const subrel=A(z=>I(G(z),I(M(z,y),M(z,x))));
          const left=ii(M(y,p),yp=>{
            const sub=ar(from(power,y,yp));
            return ui(z=>ii(G(z),gz=>ue(sub,z)));
          });
          const right=ii(subrel,sr=>{
            const sub=ui(z=>ii(M(z,y),zy=>{
              const gz=app(us(t,y,z),ai(gy,zy));
              return app(ue(sr,z),gz,zy);
            }));
            return into(power,y,ai(gy,sub));
          });
          return ai(left,right);
        }));
        const want=replace(target[2][2],target[1],x);
        return ei(want,p,ai(gp,local));
      });
    }))));
    Object.assign(proofs,{power_from_transitivity_and_relative_powerset:generic});

  }
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}


import { readFileSync } from 'node:fs';

function runL(pinned,part){
  const defs=definition("v",true);
  if(!same(defs.L,pinned))throw Error("pinned L mismatch");
  const finite=buildF(defs,part==="ranks"?false:"power"),out={};
  function check(name,p,g=false,def=null){
    const r=kernel(0,[],p.proof,g,"ZF",def);
    if(!same(r.goal,p.goal))throw Error("goal mismatch "+name);
    out[name]={nodes:r.visits,proof_bytes:JSON.stringify(p.proof).length};
  }
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b],G=i=>["G",i],N=p=>I(p,["F"]);
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){const f=i=>i<d?i:indices[i-d]+d;return [op,f(a),f(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const D=(a,x)=>embed(defs.definable,[a,x]),Succ=(a,b)=>embed(defs.successor,[a,b]),Ord=a=>embed(defs.ordinal,[a]),L=a=>embed(defs.L,[a]);
  const W=(b,r)=>E(C(Succ(b+1,0),E(C(embed(defs.stageGraph,[0,1]),embed(defs.val,[0,b+2,r+2])))));
  const Appears=(x,a)=>C(Ord(a),E(C(W(a+1,0),M(x+1,0))));
  const Rank=(x,a)=>C(Appears(x,a),A(I(M(0,a+1),N(Appears(x+1,0)))));
  const RankSucc=(x,j)=>E(C(Rank(x+1,0),Succ(0,j+1)));
  const imp=(...ps)=>ps.reduceRight((a,b)=>I(b,a));
  const RP=(guard,x,p)=>A(B(M(0,p+1),C(guard(0),sub(0,x+1))));
  function exact(p,want,name){if(!same(p.goal,want))throw Error("independent goal mismatch "+name);}
  function rejectsAll(tests){for(const t of tests)if(!rejects(t))throw Error("negative control accepted");return tests.length;}
  if(part==="finite"){
    const v=finite.relative_power_definable;
    exact(v,A(A(A(imp(trans(2),M(1,2),RP(y=>M(y,3),1,0),D(2,0))))),"relative_power_definable");
    check("relative_power_definable",v);
    return {proofs:out,independent_goal_checks:1,negative_controls:rejectsAll([()=>kernel(0,[],v.proof,false,"CL")])};
  }
  const prior=buildE(defs,true),stages=buildI(defs,prior,buildF(defs),true),p=buildL(defs,prior,finite,stages,part==="power");
  if(part==="ranks"){
    const names=["ordinal_comparison_induction","ordinal_comparison","least_constructible_rank","least_rank_unique","least_rank_exists_unique","rank_successor_unique","rank_successor_total","ordinal_family_union","constructible_set_stage_bound"];
    for(const n of names)check(n,p[n]);
    exact(p.ordinal_comparison,A(I(Ord(0),A(I(Ord(0),["|",M(1,0),["|",Q(1,0),M(0,1)]])))),"ordinal_comparison");
    exact(p.least_rank_exists_unique,A(I(L(0),E(C(Rank(1,0),A(I(Rank(2,0),Q(0,1))))))),"least_rank_exists_unique");
    exact(p.rank_successor_total,A(I(L(0),E(C(RankSucc(1,0),A(I(RankSucc(2,0),Q(0,1))))))),"rank_successor_total");
    exact(p.constructible_set_stage_bound,A(I(A(I(M(0,1),L(0))),E(E(C(C(Ord(1),W(1,0)),sub(2,0)))))),"constructible_set_stage_bound");
    return {proofs:out,independent_goal_checks:4,negative_controls:rejectsAll([()=>kernel(0,[],p.least_rank_exists_unique.proof,false,"CL"),()=>kernel(0,[],p.constructible_set_stage_bound.proof,false,"CL")])};
  }
  if(part!=="power")throw Error("bad replay part");
  const pure=p.constructible_powerset_closure,generic=p.power_from_transitivity_and_relative_powerset;
  const PC=A(I(G(0),E(C(G(0),RP(G,1,0)))));
  const T=classProofs().generic.find(x=>x.name==="union").premises[0];
  exact(p.ambient_relative_powerset_exists,A(E(RP(L,1,0))),"ambient_relative_powerset_exists");
  exact(pure,expandClass(PC,defs.L),"constructible_powerset_closure");
  const spec={name:"power"};
  function relLocal(p){
    const [op,a,b]=p;
    if(op==="A")return A(I(G(0),relLocal(a)));
    if(op==="E")return E(C(G(0),relLocal(a)));
    if(["&","|",">"].includes(op))return [op,relLocal(a),relLocal(b)];
    return p;
  }
  const goal=relLocal(kernel(0,[],["axiom",spec],false,"ZF").goal);
  exact(generic,I(T,I(PC,goal)),"generic Power Set");
  check("ambient_relative_powerset_exists",p.ambient_relative_powerset_exists);
  check("generic_power",generic,true);
  const guarded=["conv",PC,["closed",pure.proof]];
  const tr=prior.L_transitivity_conditional,inf=finite.def_inflation;
  if(!same(tr.goal[1],inf.goal))throw Error("inflation mismatch");
  const lp=["iE",tr.proof,inf.proof];
  const tx=["conv",inst(defs.L,1),["aL",["h",0]]];
  const sx=["iE",["uE",["closed",lp],1],tx],sy=["iE",["uE",sx,0],["aR",["h",0]]];
  const tg=["uI",["uI",["iI",C(G(1),M(0,1)),["conv",G(0),sy]]]];
  const proof=["iE",["iE",generic.proof,tg],guarded],cert={spec,proof};
  const opts={sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[cert]};
  const compiled=compile(0,[],["axiom",spec],opts);
  if(!same(compiled.target.goal,goal))throw Error("compiler goal mismatch");
  const count=rejectsAll([()=>compile(0,[],["axiom",spec],{...opts,certificates:[]}),()=>compile(0,[],["axiom",{name:"choice"}],{...opts,certificates:[]}),()=>kernel(0,[],["conv",PC,["closed",["axiom",{name:"empty"}]]],true,"ZF",defs.L)]);
  if(same(expandClass(PC,classProofs().def),pure.goal))throw Error("wrong class expansion matched");
  return {proofs:{...out,constructible_powerset_closure:{proof_bytes:JSON.stringify(pure.proof).length},power_axiom:{nodes:compiled.target.visits-1,proof_bytes:JSON.stringify(proof).length}},independent_goal_checks:3,negative_controls:count,closed_L_axiom_certificate:"power",source_nodes:compiled.source.visits,target_nodes:compiled.target.visits};
}

const pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
const part=process.argv[2];
if(!part)throw Error('choose finite, ranks or power');
console.log(JSON.stringify(runL(pinned,part),null,2));
