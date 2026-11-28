import { kernel, same, scoped, rejects } from './zf_interface.mjs';
function buildLink(defs,formula,arity){
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



  if(!scoped(formula,arity,false))throw Error("formula scope");
  const clauses=[];
  function scan(p,k,path){
    const [op,a,b]=p;
    if(op==="A"||op==="E"){clauses.push({path,arity:k,body:op==="A"?[">",a,["F"]]:a,kind:op==="A"?"counterexample":"witness"});scan(a,k+1,path+"b");}
    else if(["&","|",">"].includes(op)){scan(a,k,path+"l");scan(b,k,path+"r");}
  }
  scan(formula,arity,"root");
  if(!clauses.length||clauses.length>3||clauses.some(c=>c.arity>3))throw Error("clause count/arity");
  const L=x=>form("L",x),Omega=w=>form("omega",w);
  const W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  function rel(p,guard){const [op,a,b]=p;if(op==="A")return [op,a,I(guard(a),rel(b,guard))];if(op==="E")return [op,a,C(guard(a),rel(b,guard))];if(["&","|",">"].includes(op))return [op,rel(a,guard),rel(b,guard)];return p;}
  const Phi=(c,x,ps)=>rel(named(c.body,[x,...ps]),L);
  const exL=(c,ps)=>E(x=>C(L(x),Phi(c,x,ps))),exIn=(c,s,ps)=>E(x=>C(M(x,s),Phi(c,x,ps)));
  function clause(c,r,s,ps=[]){return ps.length===c.arity?I(exL(c,ps),exIn(c,s,ps)):A(i=>I(M(i,r),clause(c,r,s,[...ps,i])));}
  function conj(xs){return xs.reduce((p,q)=>C(p,q));}
  function split(p,n){return n===1?[p]:[...split(al(p),n-1),ar(p)];}
  const Good=(a,b)=>C(C(Ord(b),M(a,b)),E(r=>C(W(a,r),E(s=>C(W(b,s),conj(clauses.map(c=>clause(c,r,s))))))));
  const Next=(a,b)=>C(Good(a,b),A(i=>I(M(i,b),N(Good(a,i)))));
  const canonical=A(a=>I(Ord(a),E(b=>C(Next(a,b),A(c=>I(Next(a,c),Q(c,b)))))));
  const strict=A(a=>A(b=>I(Next(a,b),C(Ord(b),M(a,b)))));
  const StepTotal=A(a=>I(Ord(a),E(b=>C(C(Ord(b),Next(a,b)),A(c=>I(Next(a,c),Q(c,b)))))));
  const RangeGood=(a,R)=>C(C(A(v=>I(M(v,R),Ord(v))),M(a,R)),A(v=>I(M(v,R),E(r=>C(M(r,R),Next(v,r))))));
  const range=I(StepTotal,A(a=>A(w=>I(Ord(a),I(Omega(w),I(Ord(w),E(R=>RangeGood(a,R))))))));
  const Ref=(a,l,r)=>C(C(C(Ord(l),W(l,r)),M(a,l)),conj(clauses.map(c=>clause(c,r,r))));
  const reflect=A(a=>A(R=>I(RangeGood(a,R),E(l=>E(r=>Ref(a,l,r))))));
  const omegaExists=E(w=>Omega(w)),omegaOrdinal=A(w=>I(Omega(w),Ord(w)));
  const stageMembers=A(b=>A(r=>I(Ord(b),I(W(b,r),A(x=>I(M(x,r),L(x)))))));
  function agreement(r,ps=[]){
    if(ps.length===arity){const f=named(formula,ps);return B(rel(f,x=>M(x,r)),rel(f,L));}
    return A(x=>I(M(x,r),agreement(r,[...ps,x])));
  }
  const tv=A(r=>{
    let body=agreement(r);
    for(const c of clauses.slice().reverse())body=I(clause(c,r,r),body);
    return I(A(x=>I(M(x,r),L(x))),body);
  });
  const specs={canonical_extension_total:canonical,canonical_extension_strict:strict,omega_range_closed_conditional:range,range_implies_reflecting_stage:reflect,omega_exists:omegaExists,omega_ordinal:omegaOrdinal,stage_members_constructible:stageMembers,conditional_transport:tv};
  const names=Object.keys(specs);
  function withDeps(i,ps,fn){return i===names.length?fn(ps):ii(specs[names[i]],p=>withDeps(i+1,[...ps,p],fn));}
  const proof=withDeps(0,[],([can,st,rng,re,ox,oo,sm,tv0])=>{
    const total=ui(a=>ii(Ord(a),oa=>open(app(ue(can,a),oa),(b,bp)=>{
      const ob=al(app(us(st,a,b),al(bp)));
      return ei(E(b=>C(C(Ord(b),Next(a,b)),A(c=>I(Next(a,c),Q(c,b))))),b,ai(ai(ob,al(bp)),ar(bp)));
    })));
    return use(total,tt=>use(app(rng,tt),rangeEx=>ui(a=>ii(Ord(a),oa=>{
      return open(ox,(w,ow)=>{
        const ordw=app(ue(oo,w),ow);
        return open(app(us(rangeEx,a,w),oa,ow,ordw),(R,rg)=>{
          return open(app(us(re,a,R),rg),(l,lp)=>open(lp,(r,rp)=>{
            const ol0=al(al(al(rp))),rw=ar(al(al(rp))),al0=ar(al(rp)),cs=split(ar(rp),clauses.length);
            const inc=app(us(sm,l,r),ol0,rw),eq=app(app(ue(tv0,r),inc),...cs);
            const goal=E(l=>E(r=>C(C(C(Ord(l),W(l,r)),M(a,l)),agreement(r))));
            return ei(goal,l,ei(replace(goal[2],goal[1],l),r,ai(ai(ai(ol0,rw),al0),eq)));
          }));
        });
      });
    }))));
  });
  const a0=fresh(),b0=fresh();
  const conclusion=A(a=>I(Ord(a),E(l=>E(r=>C(C(C(Ord(l),W(l,r)),M(a,l)),agreement(r))))));
  return {clauses,nextFormula:db(Next(a0,b0),[b0,a0]),signatures:Object.fromEntries(names.map(n=>[n,db(specs[n],[])])),conclusion:db(conclusion,[]),proof:{goal:db(proof.goal,[]),proof:proof.emit([],[])}};
}

export { buildLink };
