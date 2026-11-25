import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildLimit(defs,prior,stages,ranks,clauses,nextFormula,strictProof,limitProof,only=null,composition=null){
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



  if(!scoped(nextFormula,2,false)||!Array.isArray(clauses)||!clauses.length)throw Error("bad limit input");
  const strict=imported(strictProof),ou=imported(ranks.ordinal_family_union),nc=imported(prior.no_two_cycle);
  const ov=imported(stages.ordinal_stage_value_exists),mono=imported(stages.ordinal_stage_value_monotone),uniq=imported(stages.ordinal_stage_value_unique),compare=imported(ranks.ordinal_comparison),limMem=imported(limitProof);
  const Next=(a,b)=>named(nextFormula,[b,a]),L=x=>form("L",x),W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  const noPred=l=>N(E(i=>C(M(i,l),Succ(i,l))));
  const rangeGood=(a,R)=>C(C(A(v=>I(M(v,R),Ord(v))),M(a,R)),A(v=>I(M(v,R),E(r=>C(M(r,R),Next(v,r))))));
  const unionSpec=(R,l)=>A(x=>B(M(x,l),E(y=>C(M(y,R),M(x,y)))));
  const facts=(a,R,l)=>C(C(C(Ord(l),noPred(l)),unionSpec(R,l)),C(M(a,l),subset(R,l)));
  const unionLimit=qs(2,(a,R)=>ii(rangeGood(a,R),rg=>{
    const ords=al(al(rg)),aR=ar(al(rg)),closed=ar(rg);
    return open(ue(ax({name:"union"}),R),(l,lp)=>{
      const ol0=app(us(ou,R,l),ords,lp);
      const inc=ui(b=>ii(M(b,R),br=>open(app(ue(closed,b),br),(c,cp)=>{
        const bc=ar(app(us(strict,b,c),ar(cp)));
        return into(lp,b,ei(ar(ue(lp,b)).goal[1],c,ai(al(cp),bc)));
      })));
      return use(inc,ss=>{
        const np=ii(noPred(l)[1],p=>open(p,(i,ip)=>open(from(lp,i,al(ip)),(b,bp)=>{
          const bl=app(ue(ss,b),al(bp)),ib=ar(bp),sc=ar(ip);
          return oe(from(sc,b,bl),F,bi=>app(us(nc,i,b),ib,bi),eq=>{
            const ii0=eqSub(eq,z=>M(i,z),ib);
            return app(us(nc,i,i),ii0,ii0);
          });
        })));
        return ei(E(l=>facts(a,R,l)),l,ai(ai(ai(ol0,np),lp),ai(app(ue(ss,a),aR),ss)));
      });
    });
  }));
  function rel(p){const [op,a,b]=p;if(op==="A")return [op,a,I(L(a),rel(b))];if(op==="E")return [op,a,C(L(a),rel(b))];if(["&","|",">"].includes(op))return [op,rel(a),rel(b)];return p;}
  const Phi=(c,x,ps)=>rel(named(c.body,[x,...ps]));
  const exL=(c,ps)=>E(x=>C(L(x),Phi(c,x,ps))),exIn=(c,s,ps)=>E(x=>C(M(x,s),Phi(c,x,ps)));
  function clause(c,r,s,ps=[]){return ps.length===c.arity?I(exL(c,ps),exIn(c,s,ps)):A(i=>I(M(i,r),clause(c,r,s,[...ps,i])));}
  function conj(xs){return xs.reduce((p,q)=>C(p,q));}
  function conjP(xs){return xs.reduce((p,q)=>ai(p,q));}
  function split(p,n){return n===1?[p]:[...split(al(p),n-1),ar(p)];}
  function boundedParams(c,r,ps,ims,fn){return ps.length===c.arity?fn(ps,ims):ui(i=>ii(M(i,r),im=>boundedParams(c,r,[...ps,i],[...ims,im],fn)));}
  function commonParams(a,R,l,r,rg,lf,lim,ps,ims,fn){
    const ords=al(al(rg)),aR=ar(al(rg)),oa=app(ue(ords,a),aR),un=ar(al(lf));
    function loop(j,b,s,ob,bR,sw,ms){
      if(j===ps.length)return fn(b,s,ob,bR,sw,ms);
      const x=ps[j],xr=ims[j];
      return open(from(lim,x,xr),(i,ip)=>open(ar(ip),(t,tp)=>{
        const il=al(ip),tw=al(tp),xt=ar(tp);
        return open(from(un,i,il),(d,dp)=>{
          const dR=al(dp),id=ar(dp),od=app(ue(ords,d),dR);
          const oi=app(us(imported(stages.ordinal_member),l,i),al(al(al(lf))),il);
          return open(app(ue(ov,d),od),(u,uw)=>{
            const tu=app(us(mono,i,d,t,u),oi,od,tw,uw,id),xu=app(ue(tu,x),xt);
            const goal=E(b=>E(s=>C(C(C(Ord(b),M(b,R)),W(b,s)),conj(ps.slice(0,j+1).map(v=>M(v,s))))));
            function pack(b,s,ob,bR,sw,ms){return ei(goal,b,ei(replace(goal[2],goal[1],b),s,ai(ai(ai(ob,bR),sw),conjP(ms))));}
            const cc=app(ue(app(ue(compare,b),ob),d),od);
            const merged=oe(cc,goal,bd=>{
              const inc=app(us(mono,b,d,s,u),ob,od,sw,uw,bd);
              return pack(d,u,od,dR,uw,[...ms.map((p,k)=>app(ue(inc,ps[k]),p)),xu]);
            },rest=>oe(rest,goal,eq=>{
              const dw=eqSub(sym(eq),v=>W(v,u),uw);
              const us0=app(us(uniq,b,u,s),ob,dw,sw);
              return pack(b,s,ob,bR,sw,[...ms,eqSub(us0,v=>M(x,v),xu)]);
            },db0=>{
              const inc=app(us(mono,d,b,u,s),od,ob,uw,sw,db0);
              return pack(b,s,ob,bR,sw,[...ms,app(ue(inc,x),xu)]);
            }));
            return open(merged,(b2,bp)=>open(bp,(s2,sp)=>loop(j+1,b2,s2,al(al(al(sp))),ar(al(al(sp))),ar(al(sp)),split(ar(sp),j+1))));
          });
        });
      }));
    }
    return open(app(ue(ov,a),oa),(s,sw)=>loop(0,a,s,oa,aR,sw,[]));
  }
  function closure(a,R,l,r,rw,rg,lf,lim){
    const ol0=al(al(al(lf))),inL=ar(ar(lf)),closed=ar(rg);
    return conjP(clauses.map((c,idx)=>boundedParams(c,r,[],[],(ps,ims)=>ii(exL(c,ps),el=>{
      return commonParams(a,R,l,r,rg,lf,lim,ps,ims,(b,s,ob,bR,sw,ms)=>{
        return open(app(ue(closed,b),bR),(d,dp)=>{
          const dR=al(dp),nx=ar(dp),od=al(al(al(nx))),dl=app(ue(inL,d),dR);
          return open(ar(al(nx)),(p,pp)=>open(ar(pp),(q,qp)=>{
            const sp=app(us(uniq,b,s,p),ob,sw,al(pp));
            let wb=split(ar(qp),clauses.length)[idx];
            for(let j=0;j<ps.length;j++)wb=app(ue(wb,ps[j]),eqSub(sp,z=>M(ps[j],z),ms[j]));
            return open(app(wb,el),(x,xp)=>{
              const qr=app(us(mono,d,l,q,r),od,ol0,al(qp),rw,dl);
              return ei(exIn(c,r,ps),x,ai(app(ue(qr,x),al(xp)),ar(xp)));
            });
          }));
        });
      });
    }))));
  }
  const Reflect=(a,l,r)=>C(C(C(Ord(l),W(l,r)),M(a,l)),conj(clauses.map(c=>clause(c,r,r))));
  const rangeReflect=use(unionLimit,ul=>qs(2,(a,R)=>ii(rangeGood(a,R),rg=>{
    return open(app(us(ul,a,R),rg),(l,lf)=>{
      const ol0=al(al(al(lf))),np=ar(al(al(lf))),al0=al(ar(lf));
      return open(app(ue(ov,l),ol0),(r,rw)=>{
        const lm=app(us(limMem,l,r),ol0,np,rw);
        return use(lm,lim=>{
          const cl=closure(a,R,l,r,rw,rg,lf,lim);
          const goal=E(l=>E(r=>Reflect(a,l,r)));
          return ei(goal,l,ei(replace(goal[2],goal[1],l),r,ai(ai(ai(ol0,rw),al0),cl)));
        });
      });
    });
  })));
  const proofs={successor_closed_range_limit:unionLimit,range_implies_reflecting_stage:rangeReflect};
  if(composition){
    const {canonical,range,omegaExists,omegaOrdinal,transport,formula,arity}=composition;
    const can=imported(canonical),rng=imported(range),ox=imported(omegaExists),oo=imported(omegaOrdinal);
    const Omega=w=>form("omega",w);
    const stepTotal=ui(a=>ii(Ord(a),oa=>open(app(ue(can,a),oa),(b,bp)=>{
      const ob=al(app(us(strict,a,b),al(bp)));
      const goal=E(b=>C(C(Ord(b),Next(a,b)),A(c=>I(Next(a,c),Q(c,b)))));
      return ei(goal,b,ai(ai(ob,al(bp)),ar(bp)));
    })));
    const reflecting=use(stepTotal,total=>use(app(rng,total),rangeEx=>use(rangeReflect,reflect=>{
      return ui(a=>ii(Ord(a),oa=>open(ox,(w,ow)=>{
        const ordw=app(ue(oo,w),ow);
        return open(app(us(rangeEx,a,w),oa,ow,ordw),(R,rg)=>app(us(reflect,a,R),rg));
      })));
    })));
    Object.assign(proofs,{canonical_step_total:stepTotal,closed_reflecting_stage:reflecting});
    if(transport){
      const tv=imported(transport),sm=imported(stages.stage_members_constructible);
      function restrict(p,guard){const [op,a,b]=p;if(op==="A")return [op,a,I(guard(a),restrict(b,guard))];if(op==="E")return [op,a,C(guard(a),restrict(b,guard))];if(["&","|",">"].includes(op))return [op,restrict(a,guard),restrict(b,guard)];return p;}
      function agreement(r,ps=[]){if(ps.length===arity){const f=named(formula,ps);return B(restrict(f,x=>M(x,r)),restrict(f,L));}return A(x=>I(M(x,r),agreement(r,[...ps,x])));}
      const transported=use(reflecting,re=>use(tv,tv0=>ui(a=>ii(Ord(a),oa=>{
        return open(app(ue(re,a),oa),(l,lp)=>open(lp,(r,rp)=>{
          const ol0=al(al(al(rp))),rw=ar(al(al(rp))),al0=ar(al(rp)),cs=split(ar(rp),clauses.length);
          const inc=app(us(sm,l,r),ol0,rw);
          const eq=app(app(ue(tv0,r),inc),...cs);
          const goal=E(l=>E(r=>C(C(C(Ord(l),W(l,r)),M(a,l)),agreement(r))));
          return ei(goal,l,ei(replace(goal[2],goal[1],l),r,ai(ai(ai(ol0,rw),al0),eq)));
        }));
      }))));
      Object.assign(proofs,{fixed_formula_reflection:transported});
    }
  }

  return {proofs:Object.fromEntries(Object.entries(proofs).filter(([n])=>only===null||only.includes(n)).map(([n,p])=>[n,{goal:db(p.goal,[]),proof:p.emit([],[])}]))};
}
