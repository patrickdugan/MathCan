import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildReplacement(defs,body,params,reflected=false){
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



  const withUnion=(a,fn)=>open(ue(ax({name:"union"}),a),fn);
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


  if(!Number.isInteger(params)||params<0||params>2||!scoped(body,params+2,false))throw Error("replacement scope/arity");
  const L=x=>form("L",x),W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  function rel(p,guard){const [op,a,b]=p;if(op==="A")return [op,a,I(guard(a),rel(b,guard))];if(op==="E")return [op,a,C(guard(a),rel(b,guard))];if(["&","|",">"].includes(op))return [op,rel(a,guard),rel(b,guard)];return p;}
  const Phi=(y,x,ps,g)=>rel(named(body,[y,x,...ps]),g);
  const local=(r,y,x,ps)=>Phi(y,x,ps,z=>M(z,r));
  const global=(y,x,ps)=>Phi(y,x,ps,L);
  const Ltotal=(a,ps)=>A(x=>I(L(x),I(M(x,a),E(y=>C(L(y),C(global(y,x,ps),A(z=>I(L(z),I(global(z,x,ps),Q(z,y))))))))));
  const Limage=(a,b,ps)=>A(y=>I(L(y),B(M(y,b),E(x=>C(L(x),C(M(x,a),global(y,x,ps)))))));
  const lTrans=A(a=>I(L(a),A(x=>I(M(x,a),L(x)))));
  const bound=A(s=>I(A(x=>I(M(x,s),L(x))),E(c=>E(r=>C(C(Ord(c),W(c,r)),subset(s,r))))));
  const stageTrans=A(c=>A(r=>I(Ord(c),I(W(c,r),trans(r)))));
  const stageMembers=A(c=>A(r=>I(Ord(c),I(W(c,r),A(x=>I(M(x,r),L(x)))))));
  const dc=A(c=>A(r=>A(b=>I(Ord(c),I(W(c,r),I(D(r,b),L(b)))))));
  function paramsAt(r,ps,n,fn){return ps.length===n?fn(ps):A(x=>I(M(x,r),paramsAt(r,[...ps,x],n,fn)));}
  const delta=A(r=>I(trans(r),I(A(x=>I(M(x,r),L(x))),paramsAt(r,[],params+2,vs=>B(local(r,vs[0],vs[1],vs.slice(2)),global(vs[0],vs[1],vs.slice(2)))))));
  function compSpec(r,a,ps){return A(b=>I(A(y=>B(M(y,b),C(M(y,r),E(x=>C(M(x,r),C(M(x,a),local(r,y,x,ps))))))),D(r,b)));}
  const compiler=A(r=>A(a=>I(M(a,r),paramsAt(r,[],params,ps=>compSpec(r,a,ps)))));
  const agreement=r=>paramsAt(r,[],params+2,vs=>B(local(r,vs[0],vs[1],vs.slice(2)),global(vs[0],vs[1],vs.slice(2))));
  const reflection=A(c=>I(Ord(c),E(d=>E(r=>C(C(C(Ord(d),W(d,r)),M(c,d)),agreement(r))))));
  const stageMono=A(c=>A(d=>A(r=>A(s=>I(Ord(c),I(Ord(d),I(W(c,r),I(W(d,s),I(M(c,d),subset(r,s))))))))));
  const deps={L_transitivity:lTrans,constructible_set_stage_bound:bound,ordinal_stage_value_transitive:stageTrans,stage_members_constructible:stageMembers,definable_subset_constructible:dc,...(reflected?{reflection}:{bounded_absoluteness:delta}),image_definability:compiler,...(reflected?{ordinal_stage_value_monotone:stageMono}:{})};
  const names=Object.keys(deps);
  function withDeps(i,ps,fn){return i===names.length?fn(ps):ii(deps[names[i]],p=>withDeps(i+1,[...ps,p],fn));}
  const link=withDeps(0,[],([tr,bd,st,sm,dt,ab,dp,mo])=>{
    function solve(a,la,ps,lps,total){
      // Ambient replacement uses the explicitly class-restricted relation.
      const x0=fresh(),y0=fresh(),spec={name:"replacement",params,body:db(C(L(y0),global(y0,x0,ps)),[y0,x0,...ps])};
      const functional=ui(x=>ii(M(x,a),xa=>{
        const lx=app(ue(app(ue(tr,a),la),x),xa);
        return open(app(ue(total,x),lx,xa),(y,yp)=>{
          const ly=al(yp),phi=al(ar(yp)),uq=ar(ar(yp));
          const u=ui(z=>ii(C(L(z),global(z,x,ps)),zp=>app(ue(uq,z),al(zp),ar(zp))));
          return ei(E(y=>C(C(L(y),global(y,x,ps)),A(z=>I(C(L(z),global(z,x,ps)),Q(z,y))))),y,ai(ai(ly,phi),u));
        });
      }));
      return open(app(us(ax(spec),...ps.slice().reverse(),a),functional),(b,bp)=>{
        const all=ui(y=>ii(M(y,b),yb=>open(from(bp,y,yb),(x,xp)=>al(ar(xp)))));
        // A separate helper for successive adjoining returns the inclusion of
        // the original image into the final bounding set.
        function adjoinAll(i,u,ul,contains,bin,fn){
          if(i===ps.length+1)return fn(u,ul,contains,bin);
          const v=i===0?a:ps[i-1],lv=i===0?la:lps[i-1];
          return withAdjoin(u,v,(w,wp)=>{
            const wl=ui(y=>ii(M(y,w),yw=>oe(from(wp,y,yw),L(y),yu=>app(ue(ul,y),yu),yv=>eqSub(sym(yv),L,lv))));
            const inc=ui(y=>ii(M(y,u),yu=>into(wp,y,ol(yu,Q(y,v)))));
            const old=contains.map((p,j)=>app(ue(inc,j===0?a:ps[j-1]),p));
            old.push(into(wp,v,or(M(v,u),ref(v))));
            const newBin=ui(y=>ii(M(y,b),yb=>app(ue(inc,y),app(ue(bin,y),yb))));
            return adjoinAll(i+1,w,wl,old,newBin,fn);
          });
        }
        const reflex=ui(y=>ii(M(y,b),p=>p));
        return adjoinAll(0,b,all,[],reflex,(u,ul,vals,bin)=>{
          return open(app(ue(bd,u),ul),(c,cp)=>open(cp,(r,rp)=>{
            const oc=al(al(rp)),rw=ar(al(rp)),inc=ar(rp);
            function finish(c,r,oc,rw,inc,reflectedAgreement=null){
            const ar0=app(ue(inc,a),vals[0]),prs=ps.map((p,i)=>app(ue(inc,p),vals[i+1]));
            const ta=app(us(st,c,r),oc,rw),allr=app(us(sm,c,r),oc,rw),abs=reflectedAgreement===null?app(ue(ab,r),ta,allr):reflectedAgreement;
            function eqAt(y,yr,x,xr){let p=app(ue(app(ue(abs,y),yr),x),xr);for(let i=0;i<ps.length;i++)p=app(ue(p,ps[i]),prs[i]);return p;}
            const slice=ui(y=>{
              const ex=E(x=>C(M(x,r),C(M(x,a),local(r,y,x,ps))));
              const fw=ii(M(y,b),yb=>{
                const yr=app(ue(inc,y),app(ue(bin,y),yb));
                return open(from(bp,y,yb),(x,xp)=>{
                  const xa=al(xp),xr=app(ue(app(ue(ta,a),ar0),x),xa);
                  const loc=app(ar(eqAt(y,yr,x,xr)),ar(ar(xp)));
                  return ai(yr,ei(ex,x,ai(xr,ai(xa,loc))));
                });
              });
              const bw=ii(C(M(y,r),ex),yp=>{
                const yr=al(yp),ly=app(ue(allr,y),yr);
                return open(ar(yp),(x,xp)=>{
                  const gl=app(al(eqAt(y,yr,x,al(xp))),ar(ar(xp)));
                  return into(bp,y,ei(ar(ue(bp,y)).goal[1],x,ai(al(ar(xp)),ai(ly,gl))));
                });
              });
              return ai(fw,bw);
            });
            let d=app(us(dp,r,a),ar0);for(let i=0;i<ps.length;i++)d=app(ue(d,ps[i]),prs[i]);
            const db0=app(ue(d,b),slice),lb=app(us(dt,c,r,b),oc,rw,db0);
            const img=ui(y=>ii(L(y),ly=>{
              const ex=E(x=>C(L(x),C(M(x,a),global(y,x,ps))));
              const fw=ii(M(y,b),yb=>open(from(bp,y,yb),(x,xp)=>{
                const lx=app(ue(app(ue(tr,a),la),x),al(xp));
                return ei(ex,x,ai(lx,ai(al(xp),ar(ar(xp)))));
              }));
              const bw=ii(ex,p=>open(p,(x,xp)=>into(bp,y,ei(ar(ue(bp,y)).goal[1],x,ai(al(ar(xp)),ai(ly,ar(ar(xp))))))));
              return ai(fw,bw);
            }));
            return ei(E(b=>C(L(b),Limage(a,b,ps))),b,ai(lb,img));
            }
            if(!reflected)return finish(c,r,oc,rw,inc);
            return open(app(ue(ab,c),oc),(d,dp0)=>open(dp0,(s,sp)=>{
              const od=al(al(al(sp))),sw=ar(al(al(sp))),cd=ar(al(sp)),eq=ar(sp);
              const rs=app(us(mo,c,d,r,s),oc,od,rw,sw,cd);
              const newInc=ui(x=>ii(M(x,u),xu=>app(ue(rs,x),app(ue(inc,x),xu))));
              return finish(d,s,od,sw,newInc,eq);
            }));
          }));
        });
      });
    }
    function buildParams(ps,lps){
      if(ps.length===params)return ui(a=>ii(L(a),la=>ii(Ltotal(a,ps),total=>solve(a,la,ps,lps,total))));
      return ui(p=>ii(L(p),lp=>buildParams([p,...ps],[lp,...lps])));
    }
    return buildParams([],[]);
  });
  const signatures=Object.fromEntries(names.map(n=>[n,db(deps[n],[])]));
  let conclusion=db(link.goal,[]);for(const n of names)conclusion=conclusion[2];
  return {signatures,conclusion,proof:{goal:db(link.goal,[]),proof:link.emit([],[])}};
}

export { buildReplacement };
