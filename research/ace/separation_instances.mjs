import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildSep(defs,stages,body,params,defProof,deltaProof){
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
  const cm=imported(stages.common_constructible_stage),dc=imported(stages.definable_subset_constructible),sm=imported(stages.stage_members_constructible),dp=imported(defProof),delta=imported(deltaProof);
  function prove(s,ls,ps,lps){
    const p=params?ps[0]:s,lp=params?lps[0]:ls;
    return open(app(us(cm,s,p),ls,lp),(c,cp)=>open(cp,(a,ap)=>{
      const oc=al(al(al(ap))),aw=ar(al(al(ap))),ta=ar(al(ap)),sa=al(ar(ap)),pa=ar(ar(ap));
      const all=app(us(sm,c,a),oc,aw);
      const abs=app(ue(delta,a),ta,all);
      const x0=fresh(),spec={name:"separation",params,body:db(Phi(x0,ps,L),[x0,...ps])};
      return open(us(ax(spec),...ps.slice().reverse(),s),(b,bp)=>{
        function equiv(x,xa){let q=app(ue(abs,x),xa);if(params)q=app(ue(q,p),pa);return q;}
        const slice=ui(x=>{
          const la=Phi(x,ps,z=>M(z,a));
          const left=ii(M(x,b),xb=>{
            const v=from(bp,x,xb),xs=al(v),pl=ar(v);
            const xa=app(ue(app(ue(ta,s),sa),x),xs);
            return ai(xa,ai(xs,app(ar(equiv(x,xa)),pl)));
          });
          const right=ii(C(M(x,a),C(M(x,s),la)),q=>{
            const xa=al(q),xs=al(ar(q)),truth=ar(ar(q));
            return into(bp,x,ai(xs,app(al(equiv(x,xa)),truth)));
          });
          return ai(left,right);
        });
        let d=app(ue(ue(dp,a),s),sa);
        if(params)d=app(ue(d,p),pa);
        d=app(ue(d,b),slice);
        const lb=app(us(dc,c,a,b),oc,aw,d);
        const target=E(b=>C(L(b),A(x=>I(L(x),B(M(x,b),C(M(x,s),Phi(x,ps,L)))))));
        const local=ui(x=>ii(L(x),_=>ue(bp,x)));
        return ei(target,b,ai(lb,local));
      });
    }));
  }
  const pure=params?ui(p=>ii(L(p),lp=>ui(s=>ii(L(s),ls=>prove(s,ls,[p],[lp]))))):ui(s=>ii(L(s),ls=>prove(s,ls,[],[])));
  return {goal:db(pure.goal,[]),proof:pure.emit([],[])};
}

export { buildSep };
