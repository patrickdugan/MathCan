import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
function buildI(defs,prior,finite){
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
  const pairInj=imported(finite.pair_injective),pairEx=imported(finite.pair_exists);
  const defEx=imported(prior.def_exists),noCycle=imported(prior.no_two_cycle),coh=imported(prior.stage_graph_coherence),unique=imported(prior.stage_graph_unique),restrict=imported(prior.stage_graph_restriction),succTrans=imported(prior.ordinal_successor_transitivity);
  const withSetPair=(a,b,fn)=>open(us(ax({name:"pairing"}),a,b),fn);
  const withUnion=(a,fn)=>open(ue(ax({name:"union"}),a),fn);
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
  const successorExists=ui(b=>withAdjoin(b,b,(d,su)=>ei(E(d=>Succ(b,d)),d,su)));
  const succUnique=qs(3,(b,d,e)=>ii(Succ(b,d),sd=>ii(Succ(b,e),se=>extEq(d,e,x=>ai(ii(M(x,d),xd=>into(se,x,from(sd,x,xd))),ii(M(x,e),xe=>into(sd,x,from(se,x,xe))))))));
  const domainLemma=use(pairInj,inj=>qs(4,(f,d,i,r)=>ii(Graph(f,d),g=>ii(Val(f,i,r),v=>open(v,(p,pv)=>{
    return open(app(ue(al(g),p),al(pv)),(j,jp)=>open(ar(jp),(y,py)=>{
      const eq=al(app(us(inj,p,i,r,j,y),ar(pv),py));
      return eqSub(sym(eq),t=>M(t,d),al(jp));
    }));
  })))));
  const reflSub=ui(a=>ui(x=>ii(M(x,a),p=>p)));
  function earlier(td,b,bd,i,ib){return app(ue(app(ue(td,b),bd),i),ib);}
  const eqvVals=(f,g,b)=>A(i=>I(M(i,b),A(r=>B(Val(f,i,r),Val(g,i,r)))));
  function transfer(f,g,b,r,eqv,st){
    const target=Stage(g,b,r);
    return oe(st,target,ss=>open(ss,(i,ip)=>open(ar(ar(ip)),(s,sp)=>{
      const v=app(al(ue(app(ue(eqv,i),al(ip)),s)),al(sp));
      const inn=replace(target[1][2],target[1][1],i)[2][2];
      return ol(ei(target[1],i,ai(al(ip),ai(al(ar(ip)),ei(inn,s,ai(v,ar(sp)))))),target[2]);
    })),ls=>{
      const old=ar(ls),newU=target[2][2];
      const union=ui(x=>{
        function move(p,goal,reverse){
          return open(p,(i,ip)=>open(ar(ip),(s,sp)=>{
            const eq=ue(app(ue(eqv,i),al(ip)),s),v=app(reverse?ar(eq):al(eq),al(sp));
            const inn=replace(goal[2],goal[1],i)[2];
            return ei(goal,i,ai(al(ip),ei(inn,s,ai(v,ar(sp)))));
          }));
        }
        const ex=replace(newU[2],newU[1],x)[2][1];
        return ai(ii(M(x,r),xr=>move(from(old,x,xr),ex,false)),ii(ex,p=>into(old,x,move(p,ar(ue(old,x)).goal[1],true))));
      });
      return or(target[1],ai(al(ls),union));
    });
  }
  const stageTransfer=qs(4,(f,g,b,r)=>ii(eqvVals(f,g,b),eq=>ii(Stage(f,b,r),st=>transfer(f,g,b,r,eq,st))));
  function withLimitValue(f,b,g,fn){
    const i=fresh(),v=fresh(),spec={name:"replacement",params:1,body:db(Val(f,i,v),[v,i,f])};
    const img=app(us(ax(spec),f,b),ar(g));
    return open(img,(s,sp)=>withUnion(s,(r,rp)=>{
      const lim=Stage(f,b,r)[2][2];
      const proof=ui(x=>{
        const ex=replace(lim[2],lim[1],x)[2][1];
        const left=ii(M(x,r),xr=>open(from(rp,x,xr),(y,yp)=>open(from(sp,y,al(yp)),(j,jp)=>{
          const inn=replace(ex[2],ex[1],j)[2];
          return ei(ex,j,ai(al(jp),ei(inn,y,ai(ar(jp),ar(yp)))));
        })));
        const right=ii(ex,p=>open(p,(i,ip)=>open(ar(ip),(y,yp)=>{
          const sy=into(sp,y,ei(ar(ue(sp,y)).goal[1],i,ai(al(ip),al(yp))));
          return into(rp,x,ei(ar(ue(rp,x)).goal[1],y,ai(sy,ar(yp))));
        })));
        return ai(left,right);
      });
      return use(proof,p=>fn(r,p));
    }));
  }
  const limitValue=qs(2,(f,b)=>ii(Graph(f,b),g=>withLimitValue(f,b,g,(r,p)=>ei(E(r=>Stage(f,b,r)[2][2]),r,p))));
  function withStageValue(f,b,g,fn){
    const pred=E(i=>C(M(i,b),Succ(i,b)));
    const goal=E(r=>Stage(f,b,r));
    const existence=oe(em(pred),goal,sp=>{
      return open(sp,(i,ip)=>open(app(ue(ar(g),i),al(ip)),(a,ap)=>open(ue(defEx,a),(r,dr)=>{
        const st=Stage(f,b,r),inn=replace(st[1][2],st[1][1],i)[2][2];
        const sr=ol(ei(st[1],i,ai(al(ip),ai(ar(ip),ei(inn,a,ai(al(ap),dr))))),st[2]);
        return ei(goal,r,sr);
      })));
    },lp=>withLimitValue(f,b,g,(r,p)=>ei(goal,r,or(Stage(f,b,r)[1],ai(lp,p)))));
    return open(existence,fn);
  }
  const stageTotal=qs(2,(f,b)=>ii(Graph(f,b),g=>withStageValue(f,b,g,(r,p)=>ei(E(r=>Stage(f,b,r)),r,p))));
  const proofs={successor_exists:successorExists,successor_unique:succUnique,value_in_domain:domainLemma,subset_reflexive:reflSub,stage_value_transport:stageTransfer,limit_value_exists:limitValue,stage_value_exists:stageTotal};
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
