// ACE-03X. Closed two-parameter prefix-range recursion instance.
import { kernel } from './zf_interface.mjs';
import { buildUniformHistoryRecursion } from './uniform_history_recursion.mjs';

function buildUniformHistoryExample(defs){
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
  const Val=(f,i,r)=>form("val",f,i,r),Graph=(f,d)=>form("graph",f,d);
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
  const Range=(f,i,z)=>E(j=>C(M(j,i),Val(f,j,z)));
  const Seed=(f,i,r,a,b)=>A(z=>B(M(z,r),['|',['|',Q(z,a),Q(z,b)],Range(f,i,z)]));
  const sf=fresh(),si=fresh(),sr=fresh(),sa=fresh(),sb=fresh();
  const step=db(Seed(sf,si,sr,sa,sb),[sf,si,sr,sa,sb]);
  const schema=buildUniformHistoryRecursion(defs,step,2);
  const Hist=(f,i,a,b)=>named(schema.formulas.history,[f,i,a,b]);
  const Eq=(f,g,i)=>named(schema.formulas.value_agreement,[f,g,i]);
  const graphTotal=qs(4,(a,b,f,i)=>ii(Graph(f,i),g=>{
    const j=fresh(),v=fresh(),spec={name:'replacement',params:1,body:db(Val(f,j,v),[v,j,f])};
    return open(app(us(ax(spec),f,i),ar(g)),(values,vp)=>{
      return open(us(ax({name:'pairing'}),a,b),(seeds,sp)=>open(us(ax({name:'pairing'}),seeds,values),(both,bp)=>open(ue(ax({name:'union'}),both),(r,rp)=>{
        const seedsIn=into(bp,seeds,ol(ref(seeds),Q(seeds,values)));
        const valuesIn=into(bp,values,or(Q(values,seeds),ref(values)));
        const exact=ui(z=>{
          const seedAlt=['|',Q(z,a),Q(z,b)],range=Range(f,i,z),rhs=['|',seedAlt,range];
          const left=ii(M(z,r),zr=>open(from(rp,z,zr),(w,wp)=>oe(from(bp,w,al(wp)),rhs,
            eq=>ol(from(sp,z,eqSub(eq,x=>M(z,x),ar(wp))),range),
            eq=>or(seedAlt,from(vp,z,eqSub(eq,x=>M(z,x),ar(wp)))))));
          const right=ii(rhs,p=>oe(p,M(z,r),seed=>
            into(rp,z,ei(ar(ue(rp,z)).goal[1],seeds,ai(seedsIn,into(sp,z,seed)))),value=>
            into(rp,z,ei(ar(ue(rp,z)).goal[1],values,ai(valuesIn,into(vp,z,value))))));
          return ai(left,right);
        });
        return ei(E(r=>Seed(f,i,r,a,b)),r,exact);
      })));
    });
  }));
  const functional=qs(6,(a,b,f,i,r,s)=>ii(Hist(f,i,a,b),history=>ii(Seed(f,i,r,a,b),rp=>ii(Seed(f,i,s,a,b),sp=>
    extEq(r,s,x=>ai(ii(M(x,r),xr=>into(sp,x,from(rp,x,xr))),ii(M(x,s),xs=>into(rp,x,from(sp,x,xs)))))))));
  const local=qs(6,(a,b,f,g,i,r)=>ii(Eq(f,g,i),eq=>ii(Seed(f,i,r,a,b),old=>ui(z=>{
    const seedAlt=['|',Q(z,a),Q(z,b)],rf=Range(f,i,z),rg=Range(g,i,z);
    function move(p,range,reverse){
      return oe(p,['|',seedAlt,range],seed=>ol(seed,range),rv=>open(rv,(j,jp)=>{
        const at=ue(app(ue(eq,j),al(jp)),z),value=app(reverse?ar(at):al(at),ar(jp));
        return or(seedAlt,ei(range,j,ai(al(jp),value)));
      }));
    }
    return ai(ii(M(z,r),zr=>move(from(old,z,zr),rg,false)),ii(['|',seedAlt,rg],p=>into(old,z,move(p,rf,true))));
  }))));
  const historyTotal=use(imported(schema.proofs.graph_total_implies_history_total),bridge=>use(graphTotal,gt=>
    qs(2,(a,b)=>app(us(bridge,a,b),us(gt,a,b)))));
  function discharge(name){
    return use(imported(schema.proofs[name]),theorem=>use(historyTotal,total=>use(functional,fun=>use(local,loc=>
      qs(2,(a,b)=>app(us(theorem,a,b),us(total,a,b),us(fun,a,b),us(loc,a,b)))))));
  }
  const proofs={seeded_graph_total:graphTotal,seeded_history_total:historyTotal,seeded_functional:functional,
    seeded_prefix_local:local,seeded_ordinal_history_exists_unique:discharge('ordinal_history_exists_unique'),
    seeded_ordinal_value_exists:discharge('ordinal_value_exists')};
  return {step,formulas:schema.formulas,proofs:Object.fromEntries(Object.entries(proofs).map(([name,p])=>
    [name,{goal:db(p.goal,[]),proof:p.emit([],[])}]))};
}

export { buildUniformHistoryExample };
