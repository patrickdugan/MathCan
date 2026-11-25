import { definition } from './constructible_definition.mjs';
import { kernel, same } from './zf_interface.mjs';
function buildE(defs){
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
  const definableProof=(a,x,d)=>ui(y=>ii(M(y,x),mem=>{
    const goal=M(y,a);
    function follow(p,path){
      if(!path.length)return al(ie(al(ue(p,y)),mem));
      const [step,...tail]=path;
      if(step==="l")return follow(al(p),tail);
      if(step==="r")return follow(ar(p),tail);
      return ee(p,goal,(_,q)=>follow(q,tail));
    }
    return oe(d,goal,p=>fe(ie(ue(p,y),mem),goal),
      p=>follow(p,["e","r","e","r","e","r","r","e","r","e","r","r","e","r","e","r","r","e","r"]));
  }));
  const subsetD=ui(a=>ui(x=>ii(D(a,x),d=>definableProof(a,x,d))));
  const emptyD=ui(a=>ui(x=>ii(Empty(x),p=>ol(p,D(a,x)[2]))));
  const defMembers=ui(a=>ui(b=>ii(Def(a,b),d=>{
    return ui(x=>ii(M(x,b),mem=>definableProof(a,x,ie(al(ue(d,x)),mem))));
  })));
  const defEmpty=ui(a=>ui(b=>ii(Def(a,b),d=>{
    return ui(x=>ii(Empty(x),p=>ie(ar(ue(d,x)),ol(p,D(a,x)[2]))));
  })));
  const defTrans=ui(a=>ui(b=>ii(Def(a,b),d=>ii(subset(a,b),inc=>{
    return ui(x=>ii(M(x,b),mx=>ui(y=>ii(M(y,x),my=>{
      const s=definableProof(a,x,ie(al(ue(d,x)),mx));
      return ie(ue(inc,y),ie(ue(s,y),my));
    }))));
  }))));
  const unionSpec=(a,b)=>A(x=>{const r=E(y=>C(M(y,a),M(x,y)));return C(I(M(x,b),r),I(r,M(x,b)));});
  const unionTrans=ui(a=>ui(b=>ii(unionSpec(a,b),u=>ii(A(x=>I(M(x,a),trans(x))),family=>{
    return ui(x=>ii(M(x,b),mx=>ui(y=>ii(M(y,x),my=>{
      return ee(ie(al(ue(u,x)),mx),M(y,b),(z,w)=>{
        const yz=ie(ue(ie(ue(ie(ue(family,z),al(w)),x),ar(w)),y),my);
        const ex=ar(ue(u,y)).goal[1];return ie(ar(ue(u,y)),ei(ex,z,ai(al(w),yz)));
      });
    }))));
  }))));
  const proofs={definable_subset:subsetD,empty_definable:emptyD,def_members_subset:defMembers,empty_in_def:defEmpty,successor_transitivity:defTrans,union_transitivity:unionTrans};
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
