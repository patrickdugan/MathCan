import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
function buildK(defs,prior,finite,stages,extended=false){
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

  const os=imported(stages.ordinal_successor),se=imported(stages.successor_exists),su=imported(stages.successor_unique);
  const nc=imported(prior.no_two_cycle),om=imported(stages.ordinal_member);
  const ov=imported(stages.ordinal_stage_value_exists),sd=imported(stages.successor_stage_def);
  const ot=imported(stages.ordinal_stage_value_transitive),mono=imported(stages.ordinal_stage_value_monotone);
  const dc=imported(stages.definable_subset_constructible),co=imported(prior.stage_graph_coherence),st=imported(prior.ordinal_successor_transitivity);
  const selfD=imported(finite.self_definable),succD=imported(finite.successor_definable),owEx=imported(finite.omega_exists);
  const Ind=x=>form("inductive",x),Omega=x=>form("omega",x),L=x=>form("L",x);
  const W=(b,r)=>E(d=>C(Succ(b,d),E(f=>C(SG(f,d),Val(f,b,r)))));
  const noPred=b=>N(E(i=>C(M(i,b),Succ(i,b))));
  const noSelf=ui(b=>ii(M(b,b),bb=>app(us(nc,b,b),bb,bb)));
  function omegaOrdProof(w,ow){
    const pred=x=>C(Ord(x),subset(x,w));
    const v=fresh(),spec={name:"separation",params:1,body:db(pred(v),[v,w])};
    return open(us(ax(spec),w,w),(c,cp)=>{
      const base=open(al(al(ow)),(z,zp)=>{
        const zw=al(zp),ez=ar(zp);
        const tr=ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),subset(x,z))));
        const each=ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),trans(x))));
        const ord=ai(tr,each);
        const inc=ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),M(x,w))));
        const zc=into(cp,z,ai(zw,ai(ord,inc)));
        return ei(E(z=>C(M(z,c),Empty(z))),z,ai(zc,ez));
      });
      const step=ui(x=>ii(M(x,c),xc=>{
        const p=from(cp,x,xc),xw=al(p),ox=al(ar(p)),inc=ar(ar(p));
        return open(app(ue(ar(al(ow)),x),xw),(y,yp)=>{
          const yw=al(yp),xy=ar(yp),oy=app(us(os,x,y),ox,xy);
          const yinc=ui(z=>ii(M(z,y),zy=>oe(from(xy,z,zy),M(z,w),zx=>app(ue(inc,z),zx),eq=>eqSub(sym(eq),t=>M(t,w),xw))));
          const yc=into(cp,y,ai(yw,ai(oy,yinc)));
          return ei(E(y=>C(M(y,c),Succ(x,y))),y,ai(yc,xy));
        });
      }));
      const ind=ai(base,step),wc=app(ue(ar(ow),c),ind);
      const tr=ui(x=>ii(M(x,w),xw=>ar(ar(from(cp,x,app(ue(wc,x),xw))))));
      const each=ui(x=>ii(M(x,w),xw=>al(al(ar(from(cp,x,app(ue(wc,x),xw)))))));
      return ai(tr,each);
    });
  }
  const omegaOrdinal=ui(w=>ii(Omega(w),ow=>omegaOrdProof(w,ow)));
  const omegaLimit=use(noSelf,ns=>ui(w=>ii(Omega(w),ow=>ii(noPred(w)[1],p=>{
    return open(p,(i,ip)=>open(app(ue(ar(al(ow)),i),al(ip)),(j,jp)=>{
      const wj=app(us(su,i,w,j),ar(ip),ar(jp));
      const ww=eqSub(sym(wj),t=>M(t,w),al(jp));
      return app(ue(ns,w),ww);
    }));
  }))));
  function stageW(w,fn){return open(w,(d,dp)=>open(ar(dp),(f,fp)=>fn(d,f,al(dp),al(fp),ar(fp))));}
  function valueEq(sg,i,id,x,y,vx,vy){
    return open(app(ue(ar(al(sg)),i),id),(v,uv)=>{
      return chain(app(ue(ar(uv),x),vx),sym(app(ue(ar(uv),y),vy)));
    });
  }
  const limitMembers=(b,r)=>A(x=>B(M(x,r),E(i=>C(M(i,b),E(s=>C(W(i,s),M(x,s)))))));
  function limitProof(b,r,ob,np,rw){
    return stageW(rw,(d,f,bd,sf,vr)=>{
      const td=app(us(st,b,d),al(ob),bd),bin=into(bd,b,or(M(b,b),ref(b)));
      return open(app(ue(ar(sf),b),bin),(v,vp)=>{
        const eq=valueEq(sf,b,bin,v,r,al(vp),vr);
        const goal=limitMembers(b,v);
        const stv=oe(ar(vp),goal,sc=>{
          return open(sc,(i,ip)=>fe(app(np,ei(noPred(b)[1],i,ai(al(ip),al(ar(ip))))),goal));
        },lim=>{
          const old=ar(lim);
          return ui(x=>{
            const g=replace(goal[2],goal[1],x),ex=g[2][1];
            const left=ii(M(x,v),xv=>open(from(old,x,xv),(i,ip)=>open(ar(ip),(s,sp)=>{
              const ib=al(ip),oi=app(us(om,b,i),ob,ib);
              return open(app(ue(ov,i),oi),(t,tw)=>{
                return stageW(tw,(e,h,ie,sh,vt)=>{
                  const te=app(us(st,i,e),al(oi),ie);
                  const id=into(bd,i,ol(ib,Q(i,b))),iin=into(ie,i,or(M(i,i),ref(i)));
                  const eqs=app(us(co,f,h,d,e),td,te,sf,sh);
                  const et=app(ue(app(ue(app(ue(eqs,i),id,iin),s),al(sp)),t),vt);
                  const xt=eqSub(et,z=>M(x,z),ar(sp));
                  const inner=replace(ex[2],ex[1],i)[2];
                  return ei(ex,i,ai(ib,ei(inner,t,ai(tw,xt))));
                });
              });
            })));
            const right=ii(ex,p=>open(p,(i,ip)=>open(ar(ip),(s,sp)=>{
              const ib=al(ip),oi=app(us(om,b,i),ob,ib);
              const mo=app(us(mono,i,b,s,r),oi,ob,al(sp),rw,ib);
              const xr=app(ue(mo,x),ar(sp));
              return eqSub(sym(eq),z=>M(x,z),xr);
            })));
            return ai(left,right);
          });
        });
        return eqSub(eq,z=>limitMembers(b,z),stv);
      });
    });
  }
  const limitStageMembers=qs(2,(b,r)=>ii(Ord(b),ob=>ii(noPred(b),np=>ii(W(b,r),rw=>limitProof(b,r,ob,np,rw)))));

  function inductiveStage(w,r,ow,rw,ob,lim){
    const base=open(al(al(ow)),(z,zp)=>{
      const zw=al(zp),ez=ar(zp),oz=app(us(om,w,z),ob,zw);
      return open(app(ue(ar(al(ow)),z),zw),(j,jp)=>{
        const jw=al(jp),zj=ar(jp),oj=app(us(om,w,j),ob,jw);
        return open(app(ue(ov,z),oz),(v,vw)=>open(app(ue(ov,j),oj),(s,sw)=>{
          const df=app(us(sd,z,j,v,s),oz,oj,zj,vw,sw);
          const zd=ol(ez,D(v,z)[2]),zs=into(df,z,zd);
          const inc=app(us(mono,j,w,s,r),oj,ob,sw,rw,jw);
          const zr=app(ue(inc,z),zs);
          return ei(E(z=>C(M(z,r),Empty(z))),z,ai(zr,ez));
        }));
      });
    });
    const step=ui(x=>ii(M(x,r),xr=>{
      return open(from(lim,x,xr),(i,ip)=>open(ar(ip),(a,ap)=>{
        const iw=al(ip),aw=al(ap),xa=ar(ap),oi=app(us(om,w,i),ob,iw);
        const ta=app(us(ot,i,a),oi,aw);
        return open(ue(se,x),(y,xy)=>{
          const yd=app(us(succD,a,x,y),ta,xa,xy);
          return open(app(ue(ar(al(ow)),i),iw),(j,jp)=>{
            const jw=al(jp),ij=ar(jp),oj=app(us(om,w,j),ob,jw);
            return open(app(ue(ov,j),oj),(b,bw)=>{
              const df=app(us(sd,i,j,a,b),oi,oj,ij,aw,bw);
              const yb=into(df,y,yd);
              const ex=ar(ue(lim,y)).goal[1],inner=replace(ex[2],ex[1],j)[2];
              const yr=into(lim,y,ei(ex,j,ai(jw,ei(inner,b,ai(bw,yb)))));
              return ei(E(y=>C(M(y,r),Succ(x,y))),y,ai(yr,xy));
            });
          });
        });
      }));
    }));
    return ai(base,step);
  }
  const omegaStageInd=use(omegaOrdinal,oo=>use(omegaLimit,ol0=>use(limitStageMembers,lm=>{
    return qs(2,(w,r)=>ii(Omega(w),ow=>ii(W(w,r),rw=>{
      const ob=app(ue(oo,w),ow),np=app(ue(ol0,w),ow);
      return use(ob,ord=>use(app(us(lm,w,r),ord,np,rw),lim=>inductiveStage(w,r,ow,rw,ord,lim)));
    })));
  })));
  const stageInL=ui(w=>ii(Ord(w),ob=>ui(r=>ii(W(w,r),rw=>app(us(dc,w,r,r),ob,rw,ue(selfD,r))))));
  const omegaStageInL=use(omegaOrdinal,oo=>use(omegaStageInd,ind=>use(stageInL,sl=>{
    return open(owEx,(w,ow)=>{
      const ob=app(ue(oo,w),ow);
      return use(ob,ord=>open(app(ue(ov,w),ord),(r,rw)=>{
        const goal=E(r=>C(L(r),Ind(r)));
        return ei(goal,r,ai(app(ue(app(ue(sl,w),ord),r),rw),app(us(ind,w,r),ow,rw)));
      }));
    });
  })));
  const proofs={omega_ordinal:omegaOrdinal,omega_limit:omegaLimit,ordinal_limit_stage_members:limitStageMembers,omega_stage_inductive:omegaStageInd,ordinal_stage_constructible:stageInL,constructible_inductive_set:omegaStageInL};
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
