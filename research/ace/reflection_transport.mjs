import { definition } from './constructible_definition.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildTV(defs,formula,arity){
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


  if(!Number.isInteger(arity)||arity<0||arity>6||!scoped(formula,arity,false))throw Error("transport input scope/arity");
  const L=x=>form("L",x);
  function restrictN(p,guard){
    const [op,a,b]=p;
    if(op==="A")return [op,a,I(guard(a),restrictN(b,guard))];
    if(op==="E")return [op,a,C(guard(a),restrictN(b,guard))];
    if(["&","|",">"].includes(op))return [op,restrictN(a,guard),restrictN(b,guard)];
    return p;
  }
  function truth(p,env,guard){return restrictN(named(p,env),guard);}
  const clauses=[];
  function scan(p,k,path){
    const [op,a,b]=p;
    if(op==="A"||op==="E"){
      clauses.push({path,arity:k,body:op==="A"?[">",a,["F"]]:a,kind:op==="A"?"counterexample":"witness"});
      scan(a,k+1,path+"b");
    }else if(["&","|",">"].includes(op)){scan(a,k,path+"l");scan(b,k,path+"r");}
  }
  scan(formula,arity,"root");
  const byPath=new Map(clauses.map((x,i)=>[x.path,i]));
  function paramFormula(a,n,ps,fn){
    return ps.length===n?fn(ps):A(x=>I(M(x,a),paramFormula(a,n,[...ps,x],fn)));
  }
  function paramProof(a,n,ps,ms,fn){
    return ps.length===n?fn(ps,ms):ui(x=>ii(M(x,a),xa=>paramProof(a,n,[...ps,x],[...ms,xa],fn)));
  }
  const exL=(body,ps)=>E(x=>C(L(x),truth(body,[x,...ps],L)));
  const exA=(body,ps,a)=>E(x=>C(M(x,a),truth(body,[x,...ps],L)));
  const obligation=(a,c)=>paramFormula(a,c.arity,[],ps=>I(exL(c.body,ps),exA(c.body,ps,a)));
  function instantiate(p,ps,ms){
    for(let j=0;j<ps.length;j++)p=app(ue(p,ps[j]),ms[j]);
    return p;
  }
  function equivalence(p,env,mem,a,inc,hs,path){
    const [op,b,c]=p,local=x=>M(x,a);
    const pa=truth(p,env,local),pl=truth(p,env,L);
    const reflex=()=>ai(ii(pa,h=>h),ii(pl,h=>h));
    if(op==="F"||op==="M"||op==="=")return reflex();
    if(["&","|",">"].includes(op)){
      const left=equivalence(b,env,mem,a,inc,hs,path+"l"),right=equivalence(c,env,mem,a,inc,hs,path+"r");
      return use(left,l=>use(right,r=>{
        if(op==="&")return ai(ii(pa,h=>ai(app(al(l),al(h)),app(al(r),ar(h)))),ii(pl,h=>ai(app(ar(l),al(h)),app(ar(r),ar(h)))));
        if(op==="|")return ai(ii(pa,h=>oe(h,pl,x=>ol(app(al(l),x),pl[2]),x=>or(pl[1],app(al(r),x)))),ii(pl,h=>oe(h,pa,x=>ol(app(ar(l),x),pa[2]),x=>or(pa[1],app(ar(r),x)))));
        return ai(ii(pa,h=>ii(pl[1],x=>app(al(r),app(h,app(ar(l),x))))),ii(pl,h=>ii(pa[1],x=>app(ar(r),app(h,app(al(l),x))))));
      }));
    }
    const id=byPath.get(path),cl=clauses[id],w=instantiate(hs[id],env,mem);
    const eqAt=(x,xm)=>equivalence(b,[x,...env],[xm,...mem],a,inc,hs,path+"b");
    if(op==="E"){
      const fw=ii(pa,h=>open(h,(x,xp)=>{
        const xl=app(ue(inc,x),al(xp)),eq=eqAt(x,al(xp));
        return ei(pl,x,ai(xl,app(al(eq),ar(xp))));
      }));
      const bw=ii(pl,h=>open(app(w,h),(x,xp)=>{
        const eq=eqAt(x,al(xp));
        return ei(pa,x,ai(al(xp),app(ar(eq),ar(xp))));
      }));
      return ai(fw,bw);
    }
    if(op==="A"){
      const fw=ii(pa,h=>ui(x=>ii(L(x),xl=>{
        const goal=truth(b,[x,...env],L);
        return dn(ii(N(goal),bad=>{
          const counter=ei(exL(cl.body,env),x,ai(xl,bad));
          return open(app(w,counter),(y,yp)=>{
            const yes=app(ue(h,y),al(yp)),eq=eqAt(y,al(yp));
            return app(ar(yp),app(al(eq),yes));
          });
        }));
      })));
      const bw=ii(pl,h=>ui(x=>ii(M(x,a),xa=>{
        const xl=app(ue(inc,x),xa),eq=eqAt(x,xa);
        return app(ar(eq),app(ue(h,x),xl));
      })));
      return ai(fw,bw);
    }
    throw Error("unsupported formula");
  }
  function assumeClauses(a,hs,fn){
    return hs.length===clauses.length?fn(hs):ii(obligation(a,clauses[hs.length]),p=>assumeClauses(a,[...hs,p],fn));
  }
  const proof=ui(a=>ii(A(x=>I(M(x,a),L(x))),inc=>assumeClauses(a,[],hs=>paramProof(a,arity,[],[],(env,mem)=>equivalence(formula,env,mem,a,inc,hs,"root")))));
  return {goal:db(proof.goal,[]),proof:proof.emit([],[]),clauses};
}
