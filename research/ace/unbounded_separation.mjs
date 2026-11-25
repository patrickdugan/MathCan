import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildUnboundedSep(defs,body,params){
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




  if(!Number.isInteger(params)||params<0||params>1||!scoped(body,params+1,false))throw Error("separation scope/arity");
  const L=x=>form("L",x);
  const W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  function rel(p,guard){const [op,a,b]=p;if(op==="A")return [op,a,I(guard(a),rel(b,guard))];if(op==="E")return [op,a,C(guard(a),rel(b,guard))];if(["&","|",">"].includes(op))return [op,rel(a,guard),rel(b,guard)];return p;}
  const Phi=(x,ps,guard)=>rel(named(body,[x,...ps]),guard);
  const cmpStage=A(x=>A(y=>I(L(x),I(L(y),E(c=>E(r=>C(C(C(Ord(c),W(c,r)),trans(r)),C(M(x,r),M(y,r)))))))));
  const mono=A(a=>A(b=>A(r=>A(s=>I(Ord(a),I(Ord(b),I(W(a,r),I(W(b,s),I(M(a,b),subset(r,s))))))))));
  const stageTrans=A(b=>A(r=>I(Ord(b),I(W(b,r),trans(r)))));
  const defTransport=A(b=>A(r=>A(x=>I(Ord(b),I(W(b,r),I(D(r,x),L(x)))))));
  function agreement(a,ps=[]){
    if(ps.length===params+1)return B(Phi(ps[0],ps.slice(1),x=>M(x,a)),Phi(ps[0],ps.slice(1),L));
    return A(x=>I(M(x,a),agreement(a,[...ps,x])));
  }
  const reflection=A(c=>I(Ord(c),E(b=>E(a=>C(C(C(Ord(b),W(b,a)),M(c,b)),agreement(a))))));
  function compFor(a,s,ps){
    return A(b=>I(A(x=>B(M(x,b),C(M(x,a),C(M(x,s),Phi(x,ps,z=>M(z,a)))))),D(a,b)));
  }
  const defCompiler=A(a=>A(s=>I(M(s,a),params?A(p=>I(M(p,a),compFor(a,s,[p]))):compFor(a,s,[]))));
  const dependencies={common_constructible_stage:cmpStage,ordinal_stage_value_monotone:mono,ordinal_stage_value_transitive:stageTrans,definable_subset_constructible:defTransport,reflection,subset_definability:defCompiler};
  const names=Object.keys(dependencies);
  function assumeDeps(i,ps,fn){return i===names.length?fn(ps):ii(dependencies[names[i]],p=>assumeDeps(i+1,[...ps,p],fn));}
  const link=assumeDeps(0,[],([cm,mo,st,dc,re,dp])=>{
    function prove(s,ls,ps,lps){
      const p=params?ps[0]:s,lp=params?lps[0]:ls;
      return open(app(us(cm,s,p),ls,lp),(c,cp)=>open(cp,(r,rp)=>{
        const oc=al(al(al(rp))),rw=ar(al(al(rp))),sr=al(ar(rp)),pr=ar(ar(rp));
        return open(app(ue(re,c),oc),(b,bp)=>open(bp,(a,ap)=>{
          const ob=al(al(al(ap))),aw=ar(al(al(ap))),cb=ar(al(ap)),abs=ar(ap);
          const ra=app(us(mo,c,b,r,a),oc,ob,rw,aw,cb),ta=app(us(st,b,a),ob,aw);
          const sa=app(ue(ra,s),sr),pa=app(ue(ra,p),pr);
          const x0=fresh(),spec={name:"separation",params,body:db(Phi(x0,ps,L),[x0,...ps])};
          return open(us(ax(spec),...ps.slice().reverse(),s),(q,qp)=>{
            function equiv(x,xa){let z=app(ue(abs,x),xa);if(params)z=app(ue(z,p),pa);return z;}
            const slice=ui(x=>{
              const local=Phi(x,ps,z=>M(z,a));
              const left=ii(M(x,q),xq=>{
                const v=from(qp,x,xq),xs=al(v),pl=ar(v),xa=app(ue(app(ue(ta,s),sa),x),xs);
                return ai(xa,ai(xs,app(ar(equiv(x,xa)),pl)));
              });
              const right=ii(C(M(x,a),C(M(x,s),local)),h=>into(qp,x,ai(al(ar(h)),app(al(equiv(x,al(h))),ar(ar(h))))));
              return ai(left,right);
            });
            let d=app(us(dp,a,s),sa);
            if(params)d=app(ue(d,p),pa);
            d=app(ue(d,q),slice);
            const lq=app(us(dc,b,a,q),ob,aw,d);
            const goal=E(q=>C(L(q),A(x=>I(L(x),B(M(x,q),C(M(x,s),Phi(x,ps,L)))))));
            return ei(goal,q,ai(lq,ui(x=>ii(L(x),_=>ue(qp,x)))));
          });
        }));
      }));
    }
    return params?ui(p=>ii(L(p),lp=>ui(s=>ii(L(s),ls=>prove(s,ls,[p],[lp]))))):ui(s=>ii(L(s),ls=>prove(s,ls,[],[])));
  });
  const sigs=Object.fromEntries(names.map(n=>[n,db(dependencies[n],[])]));
  let conclusion=db(link.goal,[]);for(const n of names){if(conclusion[0]!==">")throw Error("link shape");conclusion=conclusion[2];}
  return {signatures:sigs,conclusion,proof:{goal:db(link.goal,[]),proof:link.emit([],[])}};
}

export { buildUnboundedSep };
