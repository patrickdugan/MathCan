import { pathToFileURL } from "node:url";
import { definition } from './constructible_definition.mjs';
import { kernel, same } from './zf_interface.mjs';
function buildE(defs,extended=false){
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
  const definableProof=(a,x,d)=>ui(y=>ii(M(y,x),mem=>{
    const goal=M(y,a);
    function follow(p,path){
      if(!path.length)return al(ie(al(ue(p,y)),mem));
      const [step,...tail]=path;
      if(step==="l")return follow(al(p),tail);
      if(step==="r")return follow(ar(p),tail);
      return ee(p,goal,(_,q)=>follow(q,tail));
    }
    return oe(d,goal,p=>fe(ie(ue(p,y),mem),goal),
      p=>follow(p,["e","r","e","r","e","r","r","e","r","e","r","r","e","r","e","r","r","e","r"]));
  }));
  const subsetD=ui(a=>ui(x=>ii(D(a,x),d=>definableProof(a,x,d))));
  const emptyD=ui(a=>ui(x=>ii(Empty(x),p=>ol(p,D(a,x)[2]))));
  const defMembers=ui(a=>ui(b=>ii(Def(a,b),d=>{
    return ui(x=>ii(M(x,b),mem=>definableProof(a,x,ie(al(ue(d,x)),mem))));
  })));
  const defEmpty=ui(a=>ui(b=>ii(Def(a,b),d=>{
    return ui(x=>ii(Empty(x),p=>ie(ar(ue(d,x)),ol(p,D(a,x)[2]))));
  })));
  const defTrans=ui(a=>ui(b=>ii(Def(a,b),d=>ii(subset(a,b),inc=>{
    return ui(x=>ii(M(x,b),mx=>ui(y=>ii(M(y,x),my=>{
      const s=definableProof(a,x,ie(al(ue(d,x)),mx));
      return ie(ue(inc,y),ie(ue(s,y),my));
    }))));
  }))));
  const unionSpec=(a,b)=>A(x=>{const r=E(y=>C(M(y,a),M(x,y)));return C(I(M(x,b),r),I(r,M(x,b)));});
  const unionTrans=ui(a=>ui(b=>ii(unionSpec(a,b),u=>ii(A(x=>I(M(x,a),trans(x))),family=>{
    return ui(x=>ii(M(x,b),mx=>ui(y=>ii(M(y,x),my=>{
      return ee(ie(al(ue(u,x)),mx),M(y,b),(z,w)=>{
        const yz=ie(ue(ie(ue(ie(ue(family,z),al(w)),x),ar(w)),y),my);
        const ex=ar(ue(u,y)).goal[1];return ie(ar(ue(u,y)),ei(ex,z,ai(al(w),yz)));
      });
    }))));
  }))));
  const ax=spec=>P(named(kernel(0,[],["axiom",spec],false,"ZF").goal,[]),()=>["axiom",spec]);
  const dn=p=>P(p.goal[1][1],(e,h)=>["dne",p.emit(e,h)]);
  const defExists=ui(a=>{
    const x=fresh(),spec={name:"separation",params:1,body:db(D(a,x),[x,a])};
    const goal=E(b=>Def(a,b));
    return ee(ue(ax({name:"power"}),a),goal,(power,pw)=>{
      const sep=ue(ue(ax(spec),a),power);
      return ee(sep,goal,(b,sp)=>{
        const cert=ui(x=>{
          const forward=ii(M(x,b),mx=>ar(ie(al(ue(sp,x)),mx)));
          const backward=ii(D(a,x),dx=>{
            const sub=definableProof(a,x,dx);
            return ie(ar(ue(sp,x)),ai(ie(ar(ue(pw,x)),sub),dx));
          });
          return ai(forward,backward);
        });
        return ei(goal,b,cert);
      });
    });
  });
  const defUnique=ui(a=>ui(b=>ui(c=>ii(Def(a,b),dbb=>ii(Def(a,c),dcc=>{
    return ie(ue(ue(ax({name:"extensionality"}),b),c),ui(x=>{
      return ai(ii(M(x,b),mx=>ie(ar(ue(dcc,x)),ie(al(ue(dbb,x)),mx))),
        ii(M(x,c),mx=>ie(ar(ue(dbb,x)),ie(al(ue(dcc,x)),mx))));
    }));
  })))));
  // Bounded induction on an arbitrary transitive set, for any fixed pure
  // set formula P(x, parameters). Use Separation to form the bad set
  // and Foundation to choose a minimal bad element.
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
  const boundedTrans=boundedInduction(["A",[">",["M",0,1],["A",[">",["M",0,1],["M",0,2]]]]],0);
  const boundedMembership=boundedInduction(["M",0,1],1);
  const boundedL=boundedInduction(defs.L,0);
  const or=(g,p)=>P(["|",g,p.goal],(e,h)=>["oR",db(g,e),p.emit(e,h)]);
  function eqSub(eq,prop,proof){
    const v=fresh(),g=prop(v);
    return P(replace(g,v,eq.goal[2]),(e,h)=>["eqS",db(g,[v,...e]),eq.emit(e,h),proof.emit(e,h)]);
  }
  const Val=(f,b,r)=>named(defs.val,[f,b,r]);
  const SG=(f,d)=>named(defs.stageGraph,[f,d]);
  const stageProp=(f,b)=>A(r=>I(Val(f,b,r),trans(r)));
  const inflation=A(a=>A(b=>I(Def(a,b),I(trans(a),subset(a,b)))));
  const f0=fresh(),b0=fresh(),stageInd=boundedInduction(db(stageProp(f0,b0),[b0,f0]),1);
  const apply2=(p,a,b)=>ue(ue(p,a),b);
  const ref=x=>P(Q(x,x),(e,h)=>["refl",e.indexOf(x)]);
  const qs=(n,fn,vars=[])=>vars.length===n?fn(...vars):ui(x=>qs(n,fn,[...vars,x]));
  function stageAt(inf,f,d,td,sg){
    const local=ui(b=>{
      return ii(M(b,d),bd=>{
        return ii(A(i=>I(M(i,b),stageProp(f,i))),ih=>{
          return ui(r=>{
            return ii(Val(f,b,r),vr=>{
              const result=trans(r);
              return ee(ie(ue(ar(al(sg)),b),bd),result,(v,uv)=>{
                return ee(ie(ue(ar(sg),b),bd),result,(s,vs)=>{
                  const ts=oe(ar(vs),trans(s),successor=>{
                    return ee(successor,trans(s),(i,si)=>{
                      return ee(ar(ar(si)),trans(s),(a,ad)=>{
                        const ta=ie(ue(ie(ue(ih,i),al(si)),a),al(ad));
                        const inc=ie(ie(apply2(inf,a,s),ar(ad)),ta);
                        return ie(ie(apply2(defTrans,a,s),ar(ad)),inc);
                      });
                    });
                  },limit=>{
                    const u=ar(limit);
                    return ui(x=>{
                      return ii(M(x,s),xs=>{
                        return ui(y=>{
                          return ii(M(y,x),yx=>{
                            return ee(ie(al(ue(u,x)),xs),M(y,s),(i,wi)=>{
                              return ee(ar(wi),M(y,s),(a,wa)=>{
                                const ta=ie(ue(ie(ue(ih,i),al(wi)),a),al(wa));
                                const ya=ie(ue(ie(ue(ta,x),ar(wa)),y),yx);
                                const ex=ar(ue(u,y)).goal[1];
                                const inner=replace(ex[2],ex[1],i);
                                return ie(ar(ue(u,y)),ei(ex,i,ai(al(wi),ei(inner[2],a,ai(al(wa),ya)))));
                              });
                            });
                          });
                        });
                      });
                    });
                  });
                  const sv=ie(ue(ar(uv),s),al(vs)),rv=ie(ue(ar(uv),r),vr);
                  const tv=eqSub(sv,trans,ts);
                  const sym=eqSub(rv,z=>Q(z,r),ref(r));
                  return eqSub(sym,trans,tv);
                });
              });
            });
          });
        });
      });
    });
    return ie(ie(ue(ue(stageInd,f),d),td),local);
  }
  const stageTrans=ii(inflation,inf=>qs(2,(f,d)=>ii(trans(d),td=>ii(SG(f,d),sg=>stageAt(inf,f,d,td,sg)))));
  const successorTrans=qs(2,(a,b)=>{
    return ii(trans(a),ta=>{
      return ii(named(defs.successor,[a,b]),su=>{
        return ui(x=>{
          return ii(M(x,b),xb=>{
            return ui(y=>{
              return ii(M(y,x),yx=>{
                return oe(ie(al(ue(su,x)),xb),M(y,b),
                  xa=>ie(ar(ue(su,y)),ol(ie(ue(ie(ue(ta,x),xa),y),yx),Q(y,a))),
                  eq=>ie(ar(ue(su,y)),ol(eqSub(eq,z=>M(y,z),yx),Q(y,a))));
              });
            });
          });
        });
      });
    });
  });
  const classTrans=ii(inflation,inf=>{
    return ui(x=>{
      return ii(named(defs.L,[x]),lx=>{
        return ui(y=>{
          return ii(M(y,x),yx=>{
            const goal=named(defs.L,[y]);
            return ee(lx,goal,(a,oa)=>{
              return ee(ar(oa),goal,(d,sd)=>{
                return ee(ar(sd),goal,(f,fg)=>{
                  return ee(ar(fg),goal,(r,vr)=>{
                    const td=ie(ie(apply2(successorTrans,a,d),al(al(oa))),al(sd));
                    const allStages=stageAt(inf,f,d,td,al(fg));
                    const ad=ie(ar(ue(al(sd),a)),or(M(a,a),ref(a)));
                    const tr=ie(ue(ie(ue(allStages,a),ad),r),al(vr));
                    const yr=ie(ue(ie(ue(tr,x),ar(vr)),y),yx);
                    const g1=replace(goal[2],goal[1],a),g2=replace(g1[2][2],g1[2][1],d);
                    const g3=replace(g2[2][2],g2[2][1],f);
                    const witness=ei(g3[2],r,ai(al(vr),yr));
                    return ei(goal,a,ai(al(oa),ei(g1[2],d,ai(al(sd),ei(g2[2],f,ai(al(fg),witness))))));
                  });
                });
              });
            });
          });
        });
      });
    });
  });
  const proofs={definable_subset:subsetD,empty_definable:emptyD,def_members_subset:defMembers,empty_in_def:defEmpty,successor_transitivity:defTrans,union_transitivity:unionTrans,def_exists:defExists,def_unique:defUnique,bounded_induction_transitivity:boundedTrans,bounded_induction_membership:boundedMembership,bounded_induction_L:boundedL,bounded_induction_stage:stageInd,stage_transitivity_conditional:stageTrans,ordinal_successor_transitivity:successorTrans,L_transitivity_conditional:classTrans};

  if(extended){
    const app=(p,...args)=>args.reduce((q,a)=>ie(q,a),p);
    const us=(p,...xs)=>xs.reduce((q,x)=>ue(q,x),p);
    const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
    const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
    const from=(p,x,px)=>app(al(ue(p,x)),px);
    const into=(p,x,px)=>app(ar(ue(p,x)),px);
    const Succ=(a,b)=>named(defs.successor,[a,b]);
    function open(p,fn){
      if(p.goal[0]!=="E")throw Error("expected exists "+p.goal[0]);
      const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
      return P(q.goal,(e,h)=>["eE",p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);
    }
    function use(p,fn){return ie(ii(p.goal,fn),p);}
    const noCycle=qs(2,(a,b)=>{
      return ii(M(a,b),ab=>ii(M(b,a),ba=>{
        return open(us(ax({name:"pairing"}),a,b),(s,sp)=>{
          const as=into(sp,a,ol(ref(a),Q(a,b))),bs=into(sp,b,or(Q(b,a),ref(b)));
          const nonempty=ei(E(x=>M(x,s)),a,as);
          return open(app(ue(ax({name:"foundation"}),s),nonempty),(z,zp)=>{
            return oe(from(sp,z,al(zp)),F,
              za=>app(app(ue(ar(zp),b),eqSub(sym(za),t=>M(b,t),ba)),bs),
              zb=>app(app(ue(ar(zp),a),eqSub(sym(zb),t=>M(a,t),ab)),as));
          });
        });
      }));
    });
    const succPredUnique=use(noCycle,nc=>{
      return qs(3,(a,b,c)=>{
        return ii(Succ(a,c),ac=>ii(Succ(b,c),bc=>{
          const am=into(ac,a,or(M(a,a),ref(a))),bm=into(bc,b,or(M(b,b),ref(b)));
          return oe(from(bc,a,am),Q(a,b),ab=>oe(from(ac,b,bm),Q(a,b),
            ba=>fe(app(us(nc,a,b),ab,ba),Q(a,b)),ba=>sym(ba)),eq=>eq);
        }));
      });
    });
    function valUnique(sg,i,im,x,y,vx,vy){
      return open(app(ue(ar(al(sg)),i),im),(v,uv)=>{
        return chain(app(ue(ar(uv),x),vx),sym(app(ue(ar(uv),y),vy)));
      });
    }
    const agreeAt=(f,g,e,b)=>I(M(b,e),A(r=>I(Val(f,b,r),A(s=>I(Val(g,b,s),Q(r,s))))));
    const f0=fresh(),g0=fresh(),e0=fresh(),b0=fresh();
    const agreeInd=boundedInduction(db(agreeAt(f0,g0,e0,b0),[b0,f0,g0,e0]),3);
    function agreeGraphs(f,g,d,e,td,te,sf,sg,pu){
      const step=ui(b=>{
        return ii(M(b,d),bd=>{
          return ii(A(i=>I(M(i,b),agreeAt(f,g,e,i))),ih=>{
            return ii(M(b,e),be=>{
              const inD=(i,ib)=>app(ue(app(ue(td,b),bd),i),ib);
              const inE=(i,ib)=>app(ue(app(ue(te,b),be),i),ib);
              function equalPrev(i,ib,a,c,va,vc){
                const p=app(ue(ih,i),ib,inE(i,ib));
                return app(ue(app(ue(p,a),va),c),vc);
              }
              function limitIn(x,other,lim1,lim2,member,reverse){
                return open(from(lim1,x,member),(i,iw)=>{
                  return open(ar(iw),(a,aw)=>{
                    const ib=al(iw),dom=reverse?inD(i,ib):inE(i,ib);
                    return open(app(ue(ar(other),i),dom),(c,cw)=>{
                      const eq=reverse?sym(equalPrev(i,ib,c,a,al(cw),al(aw))):equalPrev(i,ib,a,c,al(aw),al(cw));
                      const xc=eqSub(eq,z=>M(x,z),ar(aw));
                      const ex=ar(ue(lim2,x)).goal[1],body=replace(ex[2],ex[1],i);
                      return into(lim2,x,ei(ex,i,ai(ib,ei(body[2],c,ai(al(cw),xc)))));
                    });
                  });
                });
              }
              function sameStage(r,s,rf,sgp){
                const result=Q(r,s);
                function bothSucc(rfS,sgS){
                  return open(rfS,(i,ip)=>{
                    return open(sgS,(j,jp)=>{
                      const ij=app(us(pu,i,j,b),al(ar(ip)),al(ar(jp)));
                      return open(ar(ar(ip)),(a,ap)=>{
                        return open(ar(ar(jp)),(c,cp)=>{
                          const gic=eqSub(sym(ij),t=>Val(g,t,c),al(cp));
                          const ac=equalPrev(i,al(ip),a,c,al(ap),gic);
                          const cd=eqSub(ac,t=>Def(t,r),ar(ap));
                          return app(us(defUnique,c,r,s),cd,ar(cp));
                        });
                      });
                    });
                  });
                }
                function bothLimit(rfL,sgL){
                  const u=ar(rfL),v=ar(sgL);
                  const equiv=ui(x=>ai(
                    ii(M(x,r),xr=>limitIn(x,sg,u,v,xr,false)),
                    ii(M(x,s),xs=>limitIn(x,sf,v,u,xs,true))));
                  return app(us(ax({name:"extensionality"}),r,s),equiv);
                }
                function impossible(succ,lim){
                  return open(succ,(i,ip)=>app(al(lim),ei(al(lim).goal[1],i,ai(al(ip),al(ar(ip))))));
                }
                return oe(rf,result,
                  rfS=>oe(sgp,result,sgS=>bothSucc(rfS,sgS),sgL=>fe(impossible(rfS,sgL),result)),
                  rfL=>oe(sgp,result,sgS=>fe(impossible(sgS,rfL),result),sgL=>bothLimit(rfL,sgL)));
              }
              return ui(r=>{
                return ii(Val(f,b,r),vr=>{
                  return ui(s=>{
                    return ii(Val(g,b,s),vs=>{
                      return open(app(ue(ar(sf),b),bd),(a,af)=>{
                        return open(app(ue(ar(sg),b),be),(c,cg)=>{
                          const ac=sameStage(a,c,ar(af),ar(cg));
                          const ra=valUnique(sf,b,bd,r,a,vr,al(af));
                          const cs=valUnique(sg,b,be,c,s,al(cg),vs);
                          return chain(chain(ra,ac),cs);
                        });
                      });
                    });
                  });
                });
              });
            });
          });
        });
      });
      return app(us(agreeInd,f,g,e,d),td,step);
    }
    const coherence=use(succPredUnique,pu=>{
      return qs(4,(f,g,d,e)=>{
        return ii(trans(d),td=>ii(trans(e),te=>ii(SG(f,d),sf=>ii(SG(g,e),sg=>agreeGraphs(f,g,d,e,td,te,sf,sg,pu)))));
      });
    });

    const monoAt=(f,b)=>A(i=>I(M(i,b),A(r=>I(Val(f,i,r),A(s=>I(Val(f,b,s),subset(r,s)))))));
    const fm=fresh(),bm=fresh(),monoInd=boundedInduction(db(monoAt(fm,bm),[bm,fm]),1);
    function monoGraphs(inf,f,d,td,sf){
      return use(stageAt(inf,f,d,td,sf),allTrans=>{
        const step=ui(b=>{
          return ii(M(b,d),bd=>{
            return ii(A(j=>I(M(j,b),monoAt(f,j))),ih=>{
              return ui(i=>{
                return ii(M(i,b),ib=>{
                  const inD=(j,jb)=>app(ue(app(ue(td,b),bd),j),jb);
                  return ui(r=>{
                    return ii(Val(f,i,r),vr=>{
                      return ui(s=>{
                        return ii(Val(f,b,s),vs=>{
                          return open(app(ue(ar(sf),b),bd),(a,av)=>{
                            const result=subset(r,a);
                            const sub=oe(ar(av),result,ss=>{
                              return open(ss,(j,jp)=>{
                                return open(ar(ar(jp)),(c,cp)=>{
                                  const jc=app(ue(app(ue(allTrans,j),inD(j,al(jp))),c),al(cp));
                                  const ca=app(us(inf,c,a),ar(cp),jc);
                                  const order=from(al(ar(jp)),i,ib);
                                  const rc=oe(order,subset(r,c),ij=>{
                                    const p=app(ue(ih,j),al(jp));
                                    return app(ue(app(ue(app(ue(p,i),ij),r),vr),c),al(cp));
                                  },eq=>{
                                    const vj=eqSub(eq,t=>Val(f,t,r),vr);
                                    const rc=valUnique(sf,j,inD(j,al(jp)),r,c,vj,al(cp));
                                    return ui(x=>ii(M(x,r),xr=>eqSub(rc,t=>M(x,t),xr)));
                                  });
                                  return ui(x=>ii(M(x,r),xr=>app(ue(ca,x),app(ue(rc,x),xr))));
                                });
                              });
                            },lim=>{
                              const u=ar(lim);
                              return ui(x=>ii(M(x,r),xr=>{
                                const ex=ar(ue(u,x)).goal[1],body=replace(ex[2],ex[1],i);
                                return into(u,x,ei(ex,i,ai(ib,ei(body[2],r,ai(vr,xr)))));
                              }));
                            });
                            const as=valUnique(sf,b,bd,a,s,al(av),vs);
                            return eqSub(as,t=>subset(r,t),sub);
                          });
                        });
                      });
                    });
                  });
                });
              });
            });
          });
        });
        return app(us(monoInd,f,d),td,step);
      });
    }
    const mono=ii(inflation,inf=>qs(2,(f,d)=>ii(trans(d),td=>ii(SG(f,d),sf=>monoGraphs(inf,f,d,td,sf)))));

    const form=(name,...args)=>named(defs[name],args);
    const equivVals=(h,f,e)=>A(i=>I(M(i,e),A(r=>C(I(Val(h,i,r),Val(f,i,r)),I(Val(f,i,r),Val(h,i,r))))));
    function restriction(f,d,e,td,inc,sf){
      const qualify=p=>E(i=>C(M(i,e),E(y=>form("pair",p,i,y))));
      const v=fresh(),spec={name:"separation",params:1,body:db(qualify(v),[v,e])};
      return open(us(ax(spec),e,f),(h,hp)=>{
        function toF(i,r,p){
          return open(p,(w,wp)=>ei(Val(f,i,r),w,ai(al(from(hp,w,al(wp))),ar(wp))));
        }
        function toH(i,r,im,p){
          return open(p,(w,wp)=>{
            const qual=qualify(w),inner=replace(qual[2],qual[1],i)[2];
            const wh=into(hp,w,ai(al(wp),ei(qual,i,ai(im,ei(inner,r,ar(wp))))));
            return ei(Val(h,i,r),w,ai(wh,ar(wp)));
          });
        }
        const eqv=ui(i=>ii(M(i,e),im=>ui(r=>ai(ii(Val(h,i,r),p=>toF(i,r,p)),ii(Val(f,i,r),p=>toH(i,r,im,p))))));
        return use(eqv,ev=>{
          const graph=ai(ui(p=>ii(M(p,h),ph=>ar(from(hp,p,ph)))),ui(i=>ii(M(i,e),im=>{
            const id=app(ue(inc,i),im);
            return open(app(ue(ar(al(sf)),i),id),(r,rv)=>{
              const v=app(ar(ue(app(ue(ev,i),im),r)),al(rv));
              const unique=ui(s=>ii(Val(h,i,s),vs=>app(ue(ar(rv),s),app(al(ue(app(ue(ev,i),im),s)),vs))));
              const goal=E(y=>C(Val(h,i,y),A(z=>I(Val(h,i,z),Q(z,y)))));
              return ei(goal,r,ai(v,unique));
            });
          })));
          const steps=ui(b=>{
            return ii(M(b,e),be=>{
              const bd=app(ue(inc,b),be);
              const earlier=(i,ib)=>app(ue(app(ue(td,b),be),i),ib);
              return open(app(ue(ar(sf),b),bd),(r,rv)=>{
                const st=form("stage",h,b,r);
                const hv=app(ar(ue(app(ue(ev,b),be),r)),al(rv));
                function inLimit(x,u,goal,rev,p){
                  return open(from(u,x,p),(i,iw)=>open(ar(iw),(s,sv)=>{
                    const ib=al(iw),ie0=earlier(i,ib);
                    const eq=ue(app(ue(ev,i),ie0),s);
                    const v=app(rev?al(eq):ar(eq),al(sv));
                    const inner=replace(goal[2],goal[1],i)[2];
                    return ei(goal,i,ai(ib,ei(inner,s,ai(v,ar(sv)))));
                  }));
                }
                const stageH=oe(ar(rv),st,succ=>{
                  return open(succ,(i,ip)=>open(ar(ar(ip)),(a,ap)=>{
                    const ie0=earlier(i,al(ip)),av=app(ar(ue(app(ue(ev,i),ie0),a)),al(ap));
                    const inner=replace(st[1][2],st[1][1],i)[2][2];
                    return ol(ei(st[1],i,ai(al(ip),ai(al(ar(ip)),ei(inner,a,ai(av,ar(ap)))))),st[2]);
                  }));
                },lim=>{
                  const u=ar(lim),v=st[2][2];
                  const vv=ui(x=>{
                    const body=replace(v[2],v[1],x),ex=body[2][1];
                    const left=ii(M(x,r),xr=>inLimit(x,u,ex,false,xr));
                    const right=ii(ex,p=>{
                      const want=ar(ue(u,x)).goal[1];
                      return into(u,x,open(p,(i,iw)=>open(ar(iw),(s,sv)=>{
                        const ie0=earlier(i,al(iw)),fv=app(al(ue(app(ue(ev,i),ie0),s)),al(sv));
                        const inner=replace(want[2],want[1],i)[2];
                        return ei(want,i,ai(al(iw),ei(inner,s,ai(fv,ar(sv)))));
                      })));
                    });
                    return ai(left,right);
                  });
                  return or(st[1],ai(al(lim),vv));
                });
                return ei(E(a=>C(Val(h,b,a),form("stage",h,b,a))),r,ai(hv,stageH));
              });
            });
          });
          const goal=E(x=>C(SG(x,e),equivVals(x,f,e)));
          return ei(goal,h,ai(ai(graph,steps),ev));
        });
      });
    }
    const restrict=qs(3,(f,d,e)=>ii(trans(e),te=>ii(subset(e,d),inc=>ii(SG(f,d),sf=>restriction(f,d,e,te,inc,sf)))));
    Object.assign(proofs,{no_two_cycle:noCycle,successor_predecessor_unique:succPredUnique,bounded_induction_coherence:agreeInd,stage_graph_coherence:coherence,bounded_induction_monotonicity:monoInd,stage_graph_monotonicity_conditional:mono,stage_graph_restriction:restrict});
  }
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}


function runE(){
  const defs=definition("v",true),proofs=buildE(defs),out={};
  for(const [name,{goal,proof}] of Object.entries(proofs)){
    const checked=kernel(0,[],proof,false,"ZF");
    if(!same(checked.goal,goal))throw Error("goal mismatch "+name);
    out[name]={nodes:checked.visits,proof_bytes:JSON.stringify(proof).length};
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
  const M=(a,b)=>["M",a,b],I=(a,b)=>[">",a,b],A=p=>["A",p],E=p=>["E",p];
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const exactInflation=A(A(I(embed(defs.Def,[1,0]),I(trans(1),sub(1,0)))));
  const exactClass=A(I(defs.L,A(I(M(0,1),defs.L))));
  const exactExists=A(E(embed(defs.Def,[1,0])));
  const exactUnique=A(A(A(I(embed(defs.Def,[2,1]),I(embed(defs.Def,[2,0]),["=",1,0])))));
  for(const [name,want] of [["L_transitivity_conditional",I(exactInflation,exactClass)],["def_exists",exactExists],["def_unique",exactUnique]]){
    if(!same(proofs[name].goal,want))throw Error("independent target mismatch "+name);
  }
  const controls=[
    ()=>kernel(0,[],proofs.L_transitivity_conditional.proof[2],false,"ZF"),
    ()=>kernel(0,[],proofs.stage_transitivity_conditional.proof[2],false,"ZF"),
    ()=>kernel(0,[],proofs.def_exists.proof,false,"CL"),
    ()=>kernel(0,[],proofs.bounded_induction_L.proof,false,"logic"),
    ()=>kernel(0,[],["iE",proofs.L_transitivity_conditional.proof,proofs.def_exists.proof],false,"ZF")
  ];
  for(const fn of controls){let failed=false;try{fn();}catch(e){failed=true;}if(!failed)throw Error("bad proof accepted");}
  return {experiment:"ACE-03E",scope:"closed pure object-language proofs checked by executable ZF kernel; L transitivity conditional on inflation",proofs:out,independent_exact_goal_checks:3,negative_controls:controls.length,
    note:"proof byte totals are compact JSON tree bytes with duplicated formulas; no native Lean certification of object checker"};
}

export { buildE };
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(runE(),null,2));
