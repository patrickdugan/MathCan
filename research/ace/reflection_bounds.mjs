import { definition } from './constructible_definition.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
import { buildL } from './constructible_power.mjs';
function buildM(defs,prior,stages,ranks,formula,arity,extended=false,only=null){
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

  if(!Number.isInteger(arity)||arity<0||arity>3||!scoped(formula,arity+1,false))throw Error("reflection input scope/arity");
  const se=imported(stages.successor_exists),su=imported(stages.successor_unique),st=imported(prior.ordinal_successor_transitivity);
  const os=imported(stages.ordinal_successor),ov=imported(stages.ordinal_stage_value_exists),mono=imported(stages.ordinal_stage_value_monotone);
  const compare=imported(ranks.ordinal_comparison),ordUnion=imported(ranks.ordinal_family_union);
  const L=x=>form("L",x);
  const W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  function relativize(p){
    const [op,a,b]=p;
    if(op==="A")return [op,a,I(L(a),relativize(b))];
    if(op==="E")return [op,a,C(L(a),relativize(b))];
    if(["&","|",">"].includes(op))return [op,relativize(a),relativize(b)];
    return p;
  }
  const Phi=(x,ps)=>relativize(named(formula,[x,...ps]));
  const existsL=ps=>E(x=>C(L(x),Phi(x,ps)));
  const existsIn=(r,ps)=>E(x=>C(M(x,r),Phi(x,ps)));
  const demand=(a,ps)=>C(Ord(a),E(r=>C(W(a,r),existsIn(r,ps))));
  const anyDemand=ps=>E(a=>demand(a,ps));
  const minimum=(a,ps)=>C(demand(a,ps),A(i=>I(M(i,a),N(demand(i,ps)))));
  const selected=(j,ps)=>C(Ord(j),["|",E(a=>C(minimum(a,ps),Succ(a,j))),C(N(anyDemand(ps)),Empty(j))]);
  function witnessDemand(ps,w){
    return open(w,(x,xp)=>open(al(xp),(a,ap)=>open(ar(ap),(d,dp)=>open(ar(dp),(f,fp)=>open(ar(fp),(r,rp)=>{
      const wp=W(a,r),inn=replace(wp[2],wp[1],d)[2];
      const rw=ei(wp,d,ai(al(dp),ei(inn,f,ai(al(fp),al(rp)))));
      const wi=ei(existsIn(r,ps),x,ai(ar(rp),ar(xp)));
      return ei(anyDemand(ps),a,ai(al(ap),ei(demand(a,ps)[2],r,ai(rw,wi))));
    })))));
  }
  const demandFromL=qs(arity,(...ps)=>ii(existsL(ps),w=>witnessDemand(ps,w)));
  const least=qs(arity,(...ps)=>ii(anyDemand(ps),w=>open(w,(a,ap)=>{
    return open(ue(se,a),(d,sd)=>{
      const v=fresh(),spec={name:"separation",params:arity,body:db(demand(v,ps),[v,...ps])};
      const ad=into(sd,a,or(M(a,a),ref(a)));
      const td=app(us(st,a,d),al(al(ap)),sd);
      return open(us(ax(spec),...ps.slice().reverse(),d),(c,cp)=>{
        const ac=into(cp,a,ai(ad,ap)),ne=ei(E(x=>M(x,c)),a,ac);
        return open(app(ue(ax({name:"foundation"}),c),ne),(b,bp)=>{
          const bv=from(cp,b,al(bp)),bd=al(bv),db0=ar(bv);
          const min=ui(i=>ii(M(i,b),ib=>ii(demand(i,ps),di=>{
            const id=app(ue(app(ue(td,b),bd),i),ib);
            return app(app(ue(ar(bp),i),ib),into(cp,i,ai(id,di)));
          })));
          return ei(E(b=>minimum(b,ps)),b,ai(db0,min));
        });
      });
    });
  })));
  const leastUnique=use(compare,cmp=>qs(arity,(...ps)=>qs(2,(a,b)=>ii(minimum(a,ps),ma=>ii(minimum(b,ps),mb=>{
    const cc=app(ue(app(ue(cmp,a),al(al(ma))),b),al(al(mb)));
    return oe(cc,Q(a,b),ab=>fe(app(app(ue(ar(mb),a),ab),al(ma)),Q(a,b)),rest=>oe(rest,Q(a,b),q=>q,ba=>fe(app(app(ue(ar(ma),b),ba),al(mb)),Q(a,b))));
  })))));
  function emptyOrdinal(z,ez){
    const tr=ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),subset(x,z))));
    const each=ui(x=>ii(M(x,z),xz=>fe(app(ue(ez,x),xz),trans(x))));
    return ai(tr,each);
  }
  function emptyEq(a,b,ea,eb){
    return extEq(a,b,x=>ai(ii(M(x,a),xa=>fe(app(ue(ea,x),xa),M(x,b))),ii(M(x,b),xb=>fe(app(ue(eb,x),xb),M(x,a)))));
  }
  const selUnique=use(leastUnique,lu=>qs(arity,(...ps)=>qs(2,(j,k)=>ii(selected(j,ps),sj=>ii(selected(k,ps),sk=>{
    const g=Q(j,k);
    return oe(ar(sj),g,jp=>oe(ar(sk),g,kp=>open(jp,(a,ap)=>open(kp,(b,bp)=>{
      const ab=app(us(lu,...ps,a,b),al(ap),al(bp));
      return app(us(su,b,j,k),eqSub(ab,t=>Succ(t,j),ar(ap)),ar(bp));
    })),kn=>open(jp,(a,ap)=>fe(app(al(kn),ei(anyDemand(ps),a,al(al(ap)))),g))),
    jn=>oe(ar(sk),g,kp=>open(kp,(b,bp)=>fe(app(al(jn),ei(anyDemand(ps),b,al(al(bp)))),g)),kn=>emptyEq(j,k,ar(jn),ar(kn))));
  })))));
  const selExists=use(least,lm=>qs(arity,(...ps)=>{
    const g=E(j=>selected(j,ps));
    return oe(em(anyDemand(ps)),g,w=>open(app(us(lm,...ps),w),(a,ap)=>open(ue(se,a),(j,jp)=>{
      const sel=selected(j,ps);
      const m=ei(sel[2][1],a,ai(ap,jp));
      return ei(g,j,ai(app(us(os,a,j),al(al(ap)),jp),ol(m,sel[2][2])));
    })),none=>open(ax({name:"empty"}),(z,ez)=>{
      const sel=selected(z,ps);
      return ei(g,z,ai(emptyOrdinal(z,ez),or(sel[2][1],ai(none,ez))));
    }));
  }));
  const selTotal=use(selExists,ex=>use(selUnique,uq=>qs(arity,(...ps)=>open(us(ex,...ps),(j,jp)=>{
    const un=ui(k=>ii(selected(k,ps),kp=>app(us(uq,...ps,k,j),kp,jp)));
    return ei(E(j=>C(selected(j,ps),A(k=>I(selected(k,ps),Q(k,j))))),j,ai(jp,un));
  }))));
  const inside=(j,ps)=>E(a=>C(M(a,j),demand(a,ps)));
  const selBounds=use(demandFromL,dl=>qs(arity,(...ps)=>ui(j=>ii(selected(j,ps),sj=>ii(existsL(ps),el=>{
    const goal=inside(j,ps);
    return oe(ar(sj),goal,sp=>open(sp,(a,ap)=>{
      const aj=into(ar(ap),a,or(M(a,a),ref(a)));
      return ei(goal,a,ai(aj,al(al(ap))));
    }),np=>fe(app(al(np),app(us(dl,...ps),el)),goal));
  })))));
  function agg(a,ps,j){
    if(ps.length===arity)return selected(j,ps);
    return C(Ord(j),A(x=>B(M(x,j),E(i=>C(M(i,a),E(k=>C(agg(a,[...ps,i],k),M(x,k))))))));
  }
  const totalGoal=(a,ps)=>E(j=>C(agg(a,ps,j),A(k=>I(agg(a,ps,k),Q(k,j)))));
  function totalAt(level,child){
    return ui(a=>qs(level,(...ps)=>{
      const i=fresh(),j=fresh(),params=[a,...ps],spec={name:"replacement",params:params.length,body:db(agg(a,[...ps,i],j),[j,i,...params])};
      const functional=ui(i=>ii(M(i,a),_=>us(child,a,...ps,i)));
      const img=app(us(ax(spec),...params.slice().reverse(),a),functional);
      return open(img,(R,Rp)=>{
        const allOrd=ui(j=>ii(M(j,R),jr=>open(from(Rp,j,jr),(i,ip)=>al(ar(ip)))));
        return open(ue(ax({name:"union"}),R),(c,cp)=>{
          const oc=app(us(ordUnion,R,c),allOrd,cp);
          const unionEq=ui(x=>{
            const formula=agg(a,ps,c)[2],body=replace(formula[2],formula[1],x),ex=body[2][1];
            const left=ii(M(x,c),xc=>open(from(cp,x,xc),(j,jp)=>open(from(Rp,j,al(jp)),(i,ip)=>{
              const inner=replace(ex[2],ex[1],i)[2];
              return ei(ex,i,ai(al(ip),ei(inner,j,ai(ar(ip),ar(jp)))));
            })));
            const right=ii(ex,p=>open(p,(i,ip)=>open(ar(ip),(j,jp)=>{
              const jr=into(Rp,j,ei(ar(ue(Rp,j)).goal[1],i,ai(al(ip),al(jp))));
              return into(cp,x,ei(ar(ue(cp,x)).goal[1],j,ai(jr,ar(jp))));
            })));
            return ai(left,right);
          });
          return use(ai(oc,unionEq),ac=>{
            const uq=ui(j=>ii(agg(a,ps,j),aj=>extEq(j,c,x=>ai(ii(M(x,j),p=>into(ar(ac),x,from(ar(aj),x,p))),ii(M(x,c),p=>into(ar(aj),x,from(ar(ac),x,p)))))));
            return ei(totalGoal(a,ps),c,ai(ac,uq));
          });
        });
      });
    }));
  }
  const totals=[];
  totals[arity]=use(selTotal,t=>ui(a=>qs(arity,(...ps)=>us(t,...ps))));
  for(let level=arity-1;level>=0;level--)totals[level]=use(totals[level+1],child=>totalAt(level,child));
  function boundedParams(a,ps,preds,fn){
    if(ps.length===arity)return fn(ps,preds);
    return ui(i=>ii(M(i,a),im=>boundedParams(a,[...ps,i],[...preds,im],fn)));
  }
  function bindTotals(level,ts,fn){
    if(level>arity)return fn(ts);
    return use(totals[level],p=>bindTotals(level+1,[...ts,p],fn));
  }
  function witnessBound(a,c,r,ac,oc,rw,ts,lb,mo){
    return boundedParams(a,[],[],(ps,ims)=>ii(existsL(ps),el=>{
      function descend(level,j,jp,up){
        if(level===arity){
          return open(app(us(lb,...ps,j),jp,el),(b,bp)=>{
            const bc=up(b,al(bp)),db0=ar(bp),ob=al(db0);
            return open(ar(db0),(s,sp)=>{
              const sr=app(us(mo,b,c,s,r),ob,oc,al(sp),rw,bc);
              return open(ar(sp),(x,xp)=>ei(existsIn(r,ps),x,ai(app(ue(sr,x),al(xp)),ar(xp))));
            });
          });
        }
        const i=ps[level],im=ims[level],prefix=ps.slice(0,level);
        return open(us(ts[level+1],a,...prefix,i),(k,kp)=>{
          const ck=al(kp);
          return descend(level+1,k,ck,(b,bk)=>{
            const ex=ar(ue(ar(jp),b)).goal[1],inner=replace(ex[2],ex[1],i)[2];
            const bj=into(ar(jp),b,ei(ex,i,ai(im,ei(inner,k,ai(ck,bk)))));
            return up(b,bj);
          });
        });
      }
      return descend(0,c,ac,(_,p)=>p);
    }));
  }
  const boundFormula=(a,r,ps=[])=>ps.length===arity?I(existsL(ps),existsIn(r,ps)):A(i=>I(M(i,a),boundFormula(a,r,[...ps,i])));
  const bound=bindTotals(0,[],ts=>use(selBounds,lb=>use(ov,ve=>use(mono,mo=>ui(a=>{
    return open(ue(ts[0],a),(c,cp)=>{
      const ac=al(cp),oc=al(ac);
      return open(app(ue(ve,c),oc),(r,rw)=>{
        const b=witnessBound(a,c,r,ac,oc,rw,ts,lb,mo);
        const goal=E(c=>E(r=>C(C(Ord(c),W(c,r)),boundFormula(a,r))));
        return ei(goal,c,ei(replace(goal[2],goal[1],c),r,ai(ai(oc,rw),b)));
      });
    });
  })))));
  const proofs={demand_from_constructible_witness:demandFromL,least_witness_stage:least,least_witness_stage_unique:leastUnique,witness_selector_unique:selUnique,witness_selector_total:selTotal,witness_selector_bounds:selBounds,parameter_aggregate_total:totals[0],finite_parameter_witness_bound:bound};

  if(extended){
    const ordSucc=imported(stages.ordinal_successor),binUnion=imported(stages.binary_union_exists),ordBin=imported(stages.ordinal_binary_union);
    const extension=use(bound,bd=>use(se,su0=>use(ordSucc,os0=>use(binUnion,bu=>use(ordBin,ou=>use(ov,ve=>use(mono,mo=>{
      return qs(2,(a,r)=>ii(Ord(a),oa=>ii(W(a,r),rw=>{
        return open(ue(bd,r),(c,cp)=>open(cp,(s,sp)=>{
          const oc=al(al(sp)),sw=ar(al(sp)),wb=ar(sp);
          return open(ue(su0,a),(d,sd)=>open(ue(su0,c),(e,ss)=>{
            const od=app(us(os0,a,d),oa,sd),oe0=app(us(os0,c,e),oc,ss);
            return open(us(bu,d,e),(b,bp)=>{
              const ob=app(us(ou,d,e,b),od,oe0,bp);
              const ab=into(bp,a,ol(into(sd,a,or(M(a,a),ref(a))),M(a,e)));
              const cb=into(bp,c,or(M(c,d),into(ss,c,or(M(c,c),ref(c)))));
              return open(app(ue(ve,b),ob),(t,tw)=>{
                const rt=app(us(mo,a,b,r,t),oa,ob,rw,tw,ab);
                const st0=app(us(mo,c,b,s,t),oc,ob,sw,tw,cb);
                const liftWitness=boundedParams(r,[],[],(ps,ims)=>ii(existsL(ps),el=>{
                  let q=wb;
                  for(let i=0;i<ps.length;i++)q=app(ue(q,ps[i]),ims[i]);
                  return open(app(q,el),(x,xp)=>ei(existsIn(t,ps),x,ai(app(ue(st0,x),al(xp)),ar(xp))));
                }));
                const goal=E(b=>E(t=>C(C(C(Ord(b),W(b,t)),M(a,b)),C(subset(r,t),boundFormula(r,t)))));
                return ei(goal,b,ei(replace(goal[2],goal[1],b),t,ai(ai(ai(ob,tw),ab),ai(rt,liftWitness))));
              });
            });
          }));
        }));
      })));
    })))))));
    Object.assign(proofs,{strict_stage_witness_extension:extension});
  }
  return Object.fromEntries(Object.entries(proofs).filter(([name])=>only===null||only.includes(name)).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
