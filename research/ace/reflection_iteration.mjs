import { definition } from './constructible_definition.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
import { buildL } from './constructible_power.mjs';
import { buildM } from './reflection_bounds.mjs';
function buildN(defs,prior,stages,ranks,clauses,bounds=[]){
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


  if(!Array.isArray(clauses)||clauses.length===0||clauses.length>3||!clauses.every(c=>Number.isInteger(c.arity)&&c.arity>=0&&c.arity<=3&&scoped(c.body,c.arity+1,false)))throw Error("bad clause list");
  const se=imported(stages.successor_exists),su=imported(stages.successor_unique),st=imported(prior.ordinal_successor_transitivity),ov=imported(stages.ordinal_stage_value_exists),mono=imported(stages.ordinal_stage_value_monotone),compare=imported(ranks.ordinal_comparison),uniq=imported(stages.ordinal_stage_value_unique);
  const L=x=>form("L",x),W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  function rel(p){const [op,a,b]=p;if(op==="A")return [op,a,I(L(a),rel(b))];if(op==="E")return [op,a,C(L(a),rel(b))];if(["&","|",">"].includes(op))return [op,rel(a),rel(b)];return p;}
  const Phi=(c,x,ps)=>rel(named(c.body,[x,...ps]));
  const exL=(c,ps)=>E(x=>C(L(x),Phi(c,x,ps))),exIn=(c,s,ps)=>E(x=>C(M(x,s),Phi(c,x,ps)));
  function clause(c,r,s,ps=[]){return ps.length===c.arity?I(exL(c,ps),exIn(c,s,ps)):A(i=>I(M(i,r),clause(c,r,s,[...ps,i])));}
  function conj(xs){return xs.reduce((p,q)=>C(p,q));}
  function conjP(xs){return xs.reduce((p,q)=>ai(p,q));}
  function split(p,n){if(n===1)return [p];return [...split(al(p),n-1),ar(p)];}
  function boundedParams(c,r,ps,ims,fn){return ps.length===c.arity?fn(ps,ims):ui(i=>ii(M(i,r),im=>boundedParams(c,r,[...ps,i],[...ims,im],fn)));}
  function liftClause(c,r,s,t,sb,inc){return boundedParams(c,r,[],[],(ps,ims)=>ii(exL(c,ps),el=>{
    let q=sb;for(let i=0;i<ps.length;i++)q=app(ue(q,ps[i]),ims[i]);
    return open(app(q,el),(x,xp)=>ei(exIn(c,t,ps),x,ai(app(ue(inc,x),al(xp)),ar(xp))));
  }));}
  const extensionGoal=c=>A(a=>A(r=>I(Ord(a),I(W(a,r),E(b=>E(t=>C(C(C(Ord(b),W(b,t)),M(a,b)),C(subset(r,t),clause(c,r,t)))))))));
  const Good=(a,b)=>C(C(Ord(b),M(a,b)),E(r=>C(W(a,r),E(s=>C(W(b,s),conj(clauses.map(c=>clause(c,r,s))))))));
  const Next=(a,b)=>C(Good(a,b),A(i=>I(M(i,b),N(Good(a,i)))));
  function candidates(a,r,oa,rw,exts,fn){
    function loop(j,items){
      if(j===clauses.length)return fn(items);
      return open(app(us(exts[j],a,r),oa,rw),(b,bp)=>open(bp,(s,sp)=>{
        const ob=al(al(al(sp))),sw=ar(al(al(sp))),ab=ar(al(sp)),cl=ar(ar(sp));
        return loop(j+1,[...items,{b,s,ob,sw,ab,cl}]);
      }));
    }
    return loop(0,[]);
  }
  function common(a,r,oa,rw,items,fn){
    function loop(j,b,s,ob,sw,ab,cs){
      if(j===items.length)return fn(b,s,ob,sw,ab,cs);
      const t=items[j],cc=app(ue(app(ue(compare,b),ob),t.b),t.ob);
      const target=E(b=>E(s=>C(C(C(Ord(b),W(b,s)),M(a,b)),conj(clauses.slice(0,j+1).map(c=>clause(c,r,s))))));
      function pack(b,s,ob,sw,ab,cs){return ei(target,b,ei(replace(target[2],target[1],b),s,ai(ai(ai(ob,sw),ab),conjP(cs))));}
      const merged=oe(cc,target,bt=>{
        const inc=app(us(mono,b,t.b,s,t.s),ob,t.ob,sw,t.sw,bt);
        return pack(t.b,t.s,t.ob,t.sw,t.ab,[...cs.map((p,i)=>liftClause(clauses[i],r,s,t.s,p,inc)),t.cl]);
      },rest=>oe(rest,target,eq=>{
        const w=eqSub(sym(eq),i=>W(i,t.s),t.sw);
        const sameValue=app(us(uniq,b,t.s,s),ob,w,sw);
        const cl=eqSub(sameValue,v=>clause(clauses[j],r,v),t.cl);
        return pack(b,s,ob,sw,ab,[...cs,cl]);
      },tb=>{
        const inc=app(us(mono,t.b,b,t.s,s),t.ob,ob,t.sw,sw,tb);
        return pack(b,s,ob,sw,ab,[...cs,liftClause(clauses[j],r,t.s,s,t.cl,inc)]);
      }));
      return open(merged,(c,cp)=>open(cp,(u,up)=>loop(j+1,c,u,al(al(al(up))),ar(al(al(up))),ar(al(up)),split(ar(up),j+1))));
    }
    const t=items[0];return loop(1,t.b,t.s,t.ob,t.sw,t.ab,[t.cl]);
  }
  function assumeExts(j,ps,fn){return j===clauses.length?fn(ps):ii(extensionGoal(clauses[j]),p=>assumeExts(j+1,[...ps,p],fn));}
  const goodExists=assumeExts(0,[],exts=>ui(a=>ii(Ord(a),oa=>open(app(ue(ov,a),oa),(r,rw)=>{
    return candidates(a,r,oa,rw,exts,items=>common(a,r,oa,rw,items,(b,s,ob,sw,ab,cs)=>{
      const g=Good(a,b),rs=g[2],ss=replace(rs[2],rs[1],r)[2];
      return ei(E(b=>Good(a,b)),b,ai(ai(ob,ab),ei(rs,r,ai(rw,ei(ss,s,ai(sw,conjP(cs)))))));
    }));
  }))));
  const minExists=ui(a=>ii(E(b=>Good(a,b)),ge=>open(ge,(b,bp)=>open(ue(se,b),(d,sd)=>{
    const v=fresh(),spec={name:"separation",params:1,body:db(Good(a,v),[v,a])},bd=into(sd,b,or(M(b,b),ref(b))),td=app(us(st,b,d),al(al(al(bp))),sd);
    return open(us(ax(spec),a,d),(c,cp)=>{
      const bc=into(cp,b,ai(bd,bp)),ne=ei(E(x=>M(x,c)),b,bc);
      return open(app(ue(ax({name:"foundation"}),c),ne),(m,mp)=>{
        const mv=from(cp,m,al(mp)),md=al(mv),gm=ar(mv);
        const minimal=ui(i=>ii(M(i,m),im=>ii(Good(a,i),gi=>{
          const id=app(ue(app(ue(td,m),md),i),im);
          return app(app(ue(ar(mp),i),im),into(cp,i,ai(id,gi)));
        })));
        return ei(E(m=>Next(a,m)),m,ai(gm,minimal));
      });
    });
  }))));
  const minUnique=qs(3,(a,b,c)=>ii(Next(a,b),nb=>ii(Next(a,c),nc=>{
    const cc=app(ue(app(ue(compare,b),al(al(al(nb)))),c),al(al(al(nc))));
    return oe(cc,Q(b,c),bc=>fe(app(app(ue(ar(nc),b),bc),al(nb)),Q(b,c)),rest=>oe(rest,Q(b,c),eq=>eq,cb=>fe(app(app(ue(ar(nb),c),cb),al(nc)),Q(b,c))));
  })));
  const minTotal=use(minExists,me=>use(minUnique,mu=>assumeExts(0,[],exts=>{
    const ge=app(goodExists,...exts);
    return ui(a=>ii(Ord(a),oa=>open(app(ue(me,a),app(ue(ge,a),oa)),(b,bp)=>{
      const uq=ui(c=>ii(Next(a,c),cp=>app(us(mu,a,c,b),cp,bp)));
      return ei(E(b=>C(Next(a,b),A(c=>I(Next(a,c),Q(c,b))))),b,ai(bp,uq));
    })));
  })));
  const strict=qs(2,(a,b)=>ii(Next(a,b),p=>ai(al(al(al(p))),ar(al(al(p))))));
  const a0=fresh(),b0=fresh(),nextFormula=db(Next(a0,b0),[b0,a0]);
  const proofs={common_strict_extension_conditional:goodExists,least_extension_exists:minExists,least_extension_unique:minUnique,canonical_extension_total_conditional:minTotal,canonical_extension_strict:strict};
  if(bounds.length){
    if(bounds.length!==clauses.length)throw Error("bound count");
    const total=app(minTotal,...bounds.map(imported));
    proofs.canonical_extension_total=total;
  }
  return {nextFormula,proofs:Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]))};
}
