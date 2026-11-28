// ACE-03Y-02: bounded selector and transitive-class order transport.
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { kernel, same, scoped, compile, expandClass, rejects } from "./zf_interface.mjs";
import { definition } from "./constructible_definition.mjs";
import { buildWellOrder } from "./constructible_well_order.mjs";
function runBoundedChoice({kernel,same,scoped,compile,expandClass,rejects,definition,buildWellOrder,pinned,prior}, emitProofs=false) {
  const defs=definition("v",true),w=buildWellOrder(defs);
  const req=(p,m)=>{if(!p)throw Error(m);};
  req(same(defs.L,pinned),"pinned L mismatch");
  let serial=0;
  const fresh=()=>`b${serial++}`,F=["F"],G=x=>["G",x],M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b];
  const I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],O=(p,q)=>["|",p,q],N=p=>I(p,F),B=(p,q)=>C(I(p,q),I(q,p));
  const A=f=>{const x=fresh();return ["A",x,f(x)];},E=f=>{const x=fresh();return ["E",x,f(x)];};
  const all=(s,f)=>A(x=>I(M(x,s),f(x))),some=(s,f)=>E(x=>C(M(x,s),f(x)));
  function named(p,e){const [o,a,b]=p;if(o==="F")return F;if(o==="G")return G(e[a]);if(o==="M"||o==="=")return [o,e[a],e[b]];if(o==="A"||o==="E"){const x=fresh();return [o,x,named(a,[x,...e])];}return [o,named(a,e),named(b,e)];}
  function db(p,e=[]){const [o,a,b]=p;if(o==="F")return F;if(o==="G"){req(e.includes(a),"unbound guard");return G(e.indexOf(a));}if(o==="M"||o==="="){req(e.includes(a)&&e.includes(b),"unbound variable");return [o,e.indexOf(a),e.indexOf(b)];}if(o==="A"||o==="E")return [o,db(b,[a,...e])];return [o,db(a,e),db(b,e)];}
  function replace(p,x,y){const [o,a,b]=p;if(o==="F")return F;if(o==="G")return G(a===x?y:a);if(o==="M"||o==="=")return [o,a===x?y:a,b===x?y:b];if(o==="A"||o==="E"){if(a===x)return p;if(a===y){const z=fresh();return [o,z,replace(replace(b,a,z),x,y)];}return [o,a,replace(b,x,y)];}return [o,replace(a,x,y),replace(b,x,y)];}
  function guard(p){const [o,a,b]=p;if(o==="A")return [o,a,I(G(a),guard(b))];if(o==="E")return [o,a,C(G(a),guard(b))];if(["&","|",">"].includes(o))return [o,guard(a),guard(b)];return p;}
  const P=(goal,emit)=>({goal,emit});
  function assume(goal){const id=fresh();return {id,p:P(goal,(_,h)=>{const j=h.indexOf(id);req(j>=0,"unbound hypothesis");return ["h",j];})};}
  function ii(g,f){const a=assume(g),p=f(a.p);return P(I(g,p.goal),(e,h)=>["iI",db(g,e),p.emit(e,[...h,a.id])]);}
  function ui(f){const x=fresh(),p=f(x);return P(["A",x,p.goal],(e,h)=>["uI",p.emit([x,...e],h)]);}
  const al=p=>P(p.goal[1],(e,h)=>["aL",p.emit(e,h)]),ar=p=>P(p.goal[2],(e,h)=>["aR",p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>["aI",p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>["iE",p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>["uE",p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p),app=(p,...qs)=>qs.reduce(ie,p);
  const ref=x=>P(Q(x,x),(e,h)=>["refl",e.indexOf(x)]);
  function ei(g,x,p){return P(g,(e,h)=>["eI",db(g[2],[g[1],...e]),e.indexOf(x),p.emit(e,h)]);}
  function open(p,f){req(p.goal[0]==="E","expected existential");const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=f(x,a.p);return P(q.goal,(e,h)=>["eE",p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);}
  function oe(p,g,l,r){const a=assume(p.goal[1]),b=assume(p.goal[2]),x=l(a.p),y=r(b.p);return P(g,(e,h)=>["oE",p.emit(e,h),x.emit(e,[...h,a.id]),y.emit(e,[...h,b.id])]);}
  const ol=(p,g)=>P(O(p.goal,g),(e,h)=>["oL",p.emit(e,h),db(g,e)]),or=(g,p)=>P(O(g,p.goal),(e,h)=>["oR",db(g,e),p.emit(e,h)]);
  function eqSub(eq,f,p){const v=fresh(),g=f(v);return P(replace(g,v,eq.goal[2]),(e,h)=>["eqS",db(g,[v,...e]),eq.emit(e,h),p.emit(e,h)]);}
  const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
  const use=(p,f)=>app(ii(p.goal,f),p);
  const qs=(n,f,v=[])=>v.length===n?f(...v):ui(x=>qs(n,f,[...v,x]));
  const childRules={h:[],refl:[],dne:[1],eqS:[2,3],axiom:[],iI:[2],iE:[1,2],aI:[1,2],aL:[1],aR:[1],oL:[1],oR:[2],oE:[1,2,3],fE:[1],uI:[1],uE:[1],eI:[3],eE:[1,3]};
  function shift(n,k){req(Object.hasOwn(childRules,n[0]),"unknown proof child");if(n[0]==="h")return ["h",n[1]+k];const v=n.slice();for(const j of childRules[n[0]])v[j]=shift(n[j],k);return v;}
  const imported=p=>P(named(p.goal,[]),(_,h)=>shift(p.proof,h.length));
  const checks={};
  function check(n,p,expected,g=false){const proof=p.emit([],[]),out=kernel(0,[],proof,g,"logic");req(same(out.goal,expected)&&same(out.goal,db(p.goal)),n+" goal mismatch");checks[n]=out.visits;return {goal:out.goal,proof};}
  const eqs=(x,a,b)=>b===undefined?Q(x,a):O(Q(x,a),Q(x,b));
  const listed=(p,a,b)=>A(x=>B(M(x,p),eqs(x,a,b)));
  const listedB=(p,a,b)=>C(b===undefined?M(a,p):C(M(a,p),M(b,p)),all(p,x=>eqs(x,a,b)));
  function listEquiv(p,a,b){
    const raw=listed(p,a,b),bd=listedB(p,a,b);
    const fw=ii(raw,h=>{
      const am=app(ar(ue(h,a)),b===undefined?ref(a):ol(ref(a),Q(a,b)));
      const ms=b===undefined?am:ai(am,app(ar(ue(h,b)),or(Q(b,a),ref(b))));
      return ai(ms,ui(x=>ii(M(x,p),xm=>app(al(ue(h,x)),xm))));
    });
    const bw=ii(bd,h=>ui(x=>{
      const to=ii(M(x,p),xm=>app(ue(ar(h),x),xm));
      const from=ii(eqs(x,a,b),e=>{
        if(b===undefined)return eqSub(sym(e),z=>M(z,p),al(h));
        return oe(e,M(x,p),u=>eqSub(sym(u),z=>M(z,p),al(al(h))),v=>eqSub(sym(v),z=>M(z,p),ar(al(h))));
      });
      return ai(to,from);
    }));
    return ai(fw,bw);
  }
  const Pair=(p,a,b)=>E(u=>E(v=>C(C(listed(u,a),listed(v,a,b)),listed(p,u,v))));
  const PairB=(p,a,b)=>some(p,u=>some(p,v=>C(C(listedB(u,a),listedB(v,a,b)),listedB(p,u,v))));
  const Val=(r,a,b)=>some(r,p=>Pair(p,a,b));
  const ValB=(r,a,b)=>some(r,p=>PairB(p,a,b));
  req(same(db(Val("r","a","b"),["r","a","b"]),defs.val),"independent pinned Val mismatch");
  function pairEquiv(p,a,b){
    const raw=Pair(p,a,b),bd=PairB(p,a,b);
    const fw=ii(raw,h=>open(h,(u,up)=>open(up,(v,vp)=>{
      const e=app(al(listEquiv(p,u,v)),ar(vp)),ub=al(al(e)),vb=ar(al(e));
      const fields=ai(ai(app(al(listEquiv(u,a)),al(al(vp))),app(al(listEquiv(v,a,b)),ar(al(vp)))),e);
      const middle=replace(bd[2][2],bd[1],u);
      return ei(bd,u,ai(ub,ei(middle,v,ai(vb,fields))));
    })));
    const bw=ii(bd,h=>open(h,(u,up)=>open(ar(up),(v,vp)=>{
      const fields=ar(vp),rr=ai(ai(app(ar(listEquiv(u,a)),al(al(fields))),app(ar(listEquiv(v,a,b)),ar(al(fields)))),app(ar(listEquiv(p,u,v)),ar(fields)));
      return ei(raw,u,ei(replace(raw[2],raw[1],u),v,rr));
    })));
    return ai(fw,bw);
  }
  function valEquiv(r,a,b){
    const raw=Val(r,a,b),bd=ValB(r,a,b);
    return ai(ii(raw,h=>open(h,(p,pp)=>ei(bd,p,ai(al(pp),app(al(pairEquiv(p,a,b)),ar(pp)))))),ii(bd,h=>open(h,(p,pp)=>ei(raw,p,ai(al(pp),app(ar(pairEquiv(p,a,b)),ar(pp)))))));
  }
  const valProof=check("ambient_val_bounded_equivalence",qs(3,(r,a,b)=>valEquiv(r,a,b)),db(A(r=>A(a=>A(b=>B(Val(r,a,b),ValB(r,a,b)))))));
  const sel=(y,a,r,v)=>some(a,x=>C(M(y,x),all(x,z=>N(v(r,z,y)))));
  const rawSpec={name:"separation",params:2,body:db(sel("y","a","r",Val),["y","a","r"])};
  const boundedSpec={name:"separation",params:2,body:db(sel("y","a","r",ValB),["y","a","r"])};
  req(same(rawSpec,prior.selector_schema),"exact prior selector schema changed");
  function bounded(p){const [o,a,b]=p;if(o==="A"||o==="E")return a[0]===(o==="A"?">":"&")&&a[1][0]==="M"&&a[1][1]===0&&a[1][2]>0&&bounded(a[2]);return ["&","|",">"].includes(o)?bounded(a)&&bounded(b):["M","=","F"].includes(o);}
  req(bounded(boundedSpec.body)&&!bounded(rawSpec.body),"bounded selector shape");
  function selEquiv(y,a,r){
    const raw=sel(y,a,r,Val),bd=sel(y,a,r,ValB);
    const dir=(f,g,side)=>ii(f,h=>open(h,(x,xp)=>{
      const member=al(ar(xp)),n=ar(ar(xp));
      const min=ui(z=>ii(M(z,x),zx=>ii((side===0?ValB:Val)(r,z,y),lt=>{
        const eq=us(imported(valProof),r,z,y);
        return app(app(ue(n,z),zx),app(side===0?ar(eq):al(eq),lt));
      })));
      return ei(g,x,ai(al(xp),ai(member,min)));
    }));
    return ai(dir(raw,bd,0),dir(bd,raw,1));
  }
  const selProof=check("ambient_selector_bounded_equivalence",qs(3,(y,a,r)=>selEquiv(y,a,r)),db(A(y=>A(a=>A(r=>B(sel(y,a,r,Val),sel(y,a,r,ValB)))))));
  function translated(n,p,expected){const t=compile(0,[],p.proof,{sourceTheory:"logic",targetTheory:"logic",certificates:[]});req(t.targetCtx.length===0&&same(t.target.goal,expected),n+" target mismatch");checks[n]=t.target.visits;return {goal:t.target.goal,proof:t.proof};}
  const gv=translated("relativized_val_equivalence",valProof,db(guard(named(valProof.goal,[]))));
  const gs=translated("relativized_selector_equivalence",selProof,db(guard(named(selProof.goal,[]))));
  const T=A(x=>A(y=>I(C(G(x),M(y,x)),G(y))));
  // Generic bounded absoluteness for a transitive class, proved by recursion
  // on the accepted bounded syntax. Each quantifier derives its class guard
  // from membership in an already guarded bounding object.
  function abs(p,guards,tr){
    const [o,a,b]=p,q=guard(p);
    if(["F","M","="].includes(o))return ai(ii(p,h=>h),ii(q,h=>h));
    if(["&","|",">"].includes(o))return use(abs(a,guards,tr),l=>use(abs(b,guards,tr),r=>{
      if(o==="&")return ai(ii(p,h=>ai(app(al(l),al(h)),app(al(r),ar(h)))),ii(q,h=>ai(app(ar(l),al(h)),app(ar(r),ar(h)))));
      if(o==="|")return ai(ii(p,h=>oe(h,q,x=>ol(app(al(l),x),q[2]),x=>or(q[1],app(al(r),x)))),ii(q,h=>oe(h,p,x=>ol(app(ar(l),x),p[2]),x=>or(p[1],app(ar(r),x)))));
      return ai(ii(p,h=>ii(q[1],x=>app(al(r),app(h,app(ar(l),x))))),ii(q,h=>ii(p[1],x=>app(ar(r),app(h,app(al(l),x))))));
    }));
    req((o==="A"||o==="E")&&b[0]===(o==="A"?">":"&")&&b[1][0]==="M"&&b[1][1]===a&&guards.has(b[1][2]),"not a bounded quantified formula");
    const bound=b[1][2],body=b[2];
    const inc=(x,xb)=>app(us(tr,bound,x),ai(guards.get(bound),xb));
    const sub=(x,gx)=>abs(replace(body,a,x),new Map([...guards,[x,gx]]),tr);
    if(o==="E")return ai(ii(p,h=>open(h,(x,xp)=>{
      const gx=inc(x,al(xp));return ei(q,x,ai(gx,ai(al(xp),app(al(sub(x,gx)),ar(xp)))));
    })),ii(q,h=>open(h,(x,xp)=>ei(p,x,ai(al(ar(xp)),app(ar(sub(x,al(xp))),ar(ar(xp))))))));
    const fw=ii(p,h=>ui(x=>ii(G(x),gx=>ii(M(x,bound),xb=>app(al(sub(x,gx)),app(ue(h,x),xb))))));
    const bw=ii(q,h=>ui(x=>ii(M(x,bound),xb=>{const gx=inc(x,xb);return app(ar(sub(x,gx)),app(ue(h,x),gx,xb));})));
    return ai(fw,bw);
  }
  const forallG=(n,f,vs=[],ps=[])=>vs.length===n?f(vs,ps):ui(x=>ii(G(x),gx=>forallG(n,f,[...vs,x],[...ps,gx])));
  const guardedExpected=(n,f,vs=[])=>vs.length===n?f(vs):A(x=>I(G(x),guardedExpected(n,f,[...vs,x])));
  const va=check("bounded_val_absoluteness",ii(T,tr=>forallG(3,([r,a,b],ps)=>abs(ValB(r,a,b),new Map([[r,ps[0]],[a,ps[1]],[b,ps[2]]]),tr))),db(I(T,guardedExpected(3,([r,a,b])=>B(ValB(r,a,b),guard(ValB(r,a,b)))))),true);
  const sa=check("bounded_selector_absoluteness",ii(T,tr=>forallG(3,([y,a,r],ps)=>abs(sel(y,a,r,ValB),new Map([[y,ps[0]],[a,ps[1]],[r,ps[2]]]),tr))),db(I(T,guardedExpected(3,([y,a,r])=>B(sel(y,a,r,ValB),guard(sel(y,a,r,ValB)))))),true);
  function applyG(p,vs,ps){return vs.reduce((v,x,i)=>app(ue(v,x),ps[i]),p);}
  // Combine source equivalence, its relativization and bounded absoluteness.
  const valAbs=check("exact_val_absoluteness",ii(T,tr=>forallG(3,([r,a,b],ps)=>{
    const l=us(imported(valProof),r,a,b),m=applyG(app(imported(va),tr),[r,a,b],ps),n=applyG(imported(gv),[r,a,b],ps);
    return ai(ii(Val(r,a,b),v=>app(ar(n),app(al(m),app(al(l),v)))),ii(guard(Val(r,a,b)),v=>app(ar(l),app(ar(m),app(al(n),v)))));
  })),db(I(T,guardedExpected(3,([r,a,b])=>B(Val(r,a,b),guard(Val(r,a,b)))))),true);
  const sepRaw=kernel(0,[],["axiom",rawSpec],false,"ZF").goal,sepBound=kernel(0,[],["axiom",boundedSpec],false,"ZF").goal;
  const sb=guard(named(sepBound,[])),sr=guard(named(sepRaw,[]));
  const sepTransfer=ii(sb,h=>forallG(3,([r,a,u],ps)=>{
    const [gr,ga,gu]=ps;
    return open(applyG(h,[r,a,u],ps),(c,cp)=>{
      const target=E(c=>C(G(c),A(y=>I(G(y),B(M(y,c),C(M(y,u),guard(sel(y,a,r,Val))))))));
      const bic=ui(y=>ii(G(y),gy=>{
        const orig=app(ue(ar(cp),y),gy),eq=applyG(imported(gs),[y,a,r],[gy,ga,gr]);
        return ai(ii(M(y,c),yc=>{const x=app(al(orig),yc);return ai(al(x),app(ar(eq),ar(x)));}),
          ii(C(M(y,u),guard(sel(y,a,r,Val))),v=>app(ar(orig),ai(al(v),app(al(eq),ar(v))))));
      }));
      return ei(target,c,ai(al(cp),bic));
    });
  }));
  const sepLink=check("bounded_separation_to_exact_selector_schema",sepTransfer,db(I(sb,sr)),true);
  // WO is checked against the exact old well-order formula. Its least-element
  // quantifier ranges over all sets externally, only class sets internally.
  const sub=(s,a)=>all(s,x=>M(x,a)),ne=s=>E(x=>M(x,s)),min=(s,r,x)=>C(M(x,s),all(s,y=>N(Val(r,y,x))));
  const irr=(a,r)=>all(a,x=>N(Val(r,x,x)));
  const trans=(a,r)=>A(x=>A(y=>A(z=>I(M(x,a),I(M(y,a),I(M(z,a),I(Val(r,x,y),I(Val(r,y,z),Val(r,x,z)))))))));
  const total=(a,r)=>A(x=>A(y=>I(M(x,a),I(M(y,a),O(Q(x,y),O(Val(r,x,y),Val(r,y,x)))))));
  const mins=(a,r)=>A(s=>I(sub(s,a),I(ne(s),E(x=>min(s,r,x)))));
  const WO=(a,r)=>C(C(C(irr(a,r),trans(a,r)),total(a,r)),mins(a,r));
  req(same(db(WO("a","r"),["a","r"]),w.formulas.well_order),"old WO interface changed");
  const woProof=ii(T,tr=>forallG(2,([a,r],[ga,gr])=>ii(WO(a,r),wo=>{
    const vl=(x,y,gx,gy)=>applyG(app(imported(valAbs),tr),[r,x,y],[gr,gx,gy]);
    const to=(x,y,gx,gy,p)=>app(al(vl(x,y,gx,gy)),p),from=(x,y,gx,gy,p)=>app(ar(vl(x,y,gx,gy)),p);
    const ir=ui(x=>ii(G(x),gx=>ii(M(x,a),xa=>ii(guard(Val(r,x,x)),p=>app(app(ue(al(al(al(wo))),x),xa),from(x,x,gx,gx,p))))));
    const tf=forallG(3,([x,y,z],[gx,gy,gz])=>ii(M(x,a),xa=>ii(M(y,a),ya=>ii(M(z,a),za=>ii(guard(Val(r,x,y)),xy=>ii(guard(Val(r,y,z)),yz=>to(x,z,gx,gz,app(us(ar(al(al(wo))),x,y,z),xa,ya,za,from(x,y,gx,gy,xy),from(y,z,gy,gz,yz)))))))));
    // Quantifiers in the raw transitivity/totality formulas precede their
    // membership antecedents, matching forallG's nested guarded binders.
    const tt=forallG(2,([x,y],[gx,gy])=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
      const raw=app(us(ar(al(wo)),x,y),xa,ya),goal=O(Q(x,y),O(guard(Val(r,x,y)),guard(Val(r,y,x))));
      return oe(raw,goal,p=>ol(p,goal[2]),p=>or(goal[1],oe(p,goal[2],xy=>ol(to(x,y,gx,gy,xy),goal[2][2]),yx=>or(goal[2][1],to(y,x,gy,gx,yx)))));
    })));
    const mm=ui(s=>ii(G(s),gS=>ii(guard(sub(s,a)),subG=>ii(guard(ne(s)),neG=>{
      const inG=(x,xs)=>app(us(tr,s,x),ai(gS,xs));
      const subA=ui(x=>ii(M(x,s),xs=>app(ue(subG,x),inG(x,xs),xs)));
      const neA=open(neG,(x,xp)=>ei(ne(s),x,ar(xp)));
      return open(app(ue(ar(wo),s),subA,neA),(x,xp)=>{
        const gx=inG(x,al(xp)),least=ui(y=>ii(G(y),gy=>ii(M(y,s),ys=>ii(guard(Val(r,y,x)),v=>app(app(ue(ar(xp),y),ys),from(y,x,gy,gx,v))))));
        return ei(guard(E(x=>min(s,r,x))),x,ai(gx,ai(al(xp),least)));
      });
    }))));
    return ai(ai(ai(ir,tf),tt),mm);
  })));
  const woLink=check("ambient_to_internal_well_order",woProof,db(I(T,guardedExpected(2,([a,r])=>I(WO(a,r),guard(WO(a,r)))))),true);
  const internal=guard(A(a=>E(r=>WO(a,r))));
  const external=A(a=>I(G(a),E(r=>C(G(r),WO(a,r)))));
  const allLink=ii(T,tr=>ii(external,h=>ui(a=>ii(G(a),ga=>open(app(ue(h,a),ga),(r,rp)=>{
    const ow=app(applyG(app(imported(woLink),tr),[a,r],[ga,al(rp)]),ar(rp));
    return ei(guard(E(r=>WO(a,r))),r,ai(al(rp),ow));
  })))));
  const allProof=check("constructible_ambient_orders_to_internal_well_orderability",allLink,db(I(T,I(external,internal))),true);
  // Check both key implications with the actual pinned L expansion.
  for(const [name,p] of [["selector_schema",sepLink],["internal_well_orderability",allProof]]){
    const expanded=expandClass(p.goal,defs.L),got=kernel(0,[p.goal],["conv",expanded,["h",0]],true,"logic",defs.L);
    req(same(got.goal,expanded),name+" pinned conversion");checks[name+"_pinned_conversion"]=got.visits;
  }
  const controls=[
    ()=>kernel(0,[],["axiom",rawSpec],false,"logic"),
    ()=>kernel(0,[],["axiom",boundedSpec],false,"logic"),
    ()=>kernel(0,[],["h",0],true,"logic"),
    ()=>kernel(0,[sepLink.goal,sr],["iE",["h",0],["h",1]],true,"logic"),
    ()=>kernel(0,[allProof.goal,db(external)],["iE",["h",0],["h",1]],true,"logic"),
    ()=>kernel(0,[sepLink.goal],["conv",expandClass(sepLink.goal,defs.L),["h",0]],true,"logic",["=",0,0])
  ];
  for(const f of controls)req(rejects(f),"negative control accepted");
  const receipt={experiment:"ACE-03Y-02",scope:"bounded selector equivalence and transitive-class ambient-to-internal well-order transport; conditional closure only",pinned_L_unchanged:true,raw_selector_schema:rawSpec,bounded_selector_schema:boundedSpec,checks,negative_controls:controls.length,choice_imports:0,proof_theory:"logic"};  return emitProofs ? {receipt, sepLink, allProof} : receipt;
}

export { runBoundedChoice };
const read=n=>JSON.parse(readFileSync(new URL(n,import.meta.url),"utf8"));
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(runBoundedChoice({kernel,same,scoped,compile,expandClass,rejects,definition,buildWellOrder,pinned:read("./L_formula.json"),prior:read("./internal_choice_bridge_receipt.json")}),null,2));
