import { definition } from './constructible_definition.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
function buildOmega(defs,prior,stages,finite,stepFormula,only=null){
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



  if(!scoped(stepFormula,2,false))throw Error("bad step scope");
  const se=imported(stages.successor_exists),su=imported(stages.successor_unique),st=imported(prior.ordinal_successor_transitivity);
  const pu=imported(prior.successor_predecessor_unique),ap=imported(finite.graph_append_exists),dom=imported(stages.value_in_domain);
  const Next=(a,b)=>named(stepFormula,[b,a]),Omega=w=>form("omega",w);
  const StepTotal=A(a=>I(Ord(a),E(b=>C(C(Ord(b),Next(a,b)),A(c=>I(Next(a,c),Q(c,b)))))));
  // Rules are only imposed at zero and successor indices. Existence on
  // finite domains is enough; no claim of uniqueness at other limits.
  const rule=(a,f,i,v)=>C(C(Ord(v),I(Empty(i),Q(v,a))),A(j=>I(M(j,i),I(Succ(j,i),A(u=>I(Val(f,j,u),Next(u,v)))))));
  const Rec=(a,d,f)=>C(Graph(f,d),A(i=>I(M(i,d),A(v=>I(Val(f,i,v),rule(a,f,i,v))))));
  const Tight=(a,n,v)=>E(d=>C(Succ(n,d),E(f=>C(Rec(a,d,f),Val(f,n,v)))));
  const End=(a,n,v)=>E(d=>C(C(trans(d),M(n,d)),E(f=>C(Rec(a,d,f),Val(f,n,v)))));
  const Good=(a,n)=>E(v=>C(Tight(a,n,v),A(u=>I(End(a,n,u),Q(u,v)))));
  const goalEnd=(a,n)=>E(v=>C(End(a,n,v),A(u=>I(End(a,n,u),Q(u,v)))));
  const emptyOrd=(z,ez)=>ai(ui(x=>ii(M(x,z),p=>fe(app(ue(ez,x),p),subset(x,z)))),ui(x=>ii(M(x,z),p=>fe(app(ue(ez,x),p),trans(x)))));
  function earlier(td,i,id,j,ji){return app(ue(app(ue(td,i),id),j),ji);}
  function valueRule(a,d,f,i,v,rec,id,vp){return app(ue(app(ue(ar(rec),i),id),v),vp);}
  function valEq(g,i,id,v,u,vp,up){
    return open(app(ue(ar(g),i),id),(x,xp)=>chain(app(ue(ar(xp),v),vp),sym(app(ue(ar(xp),u),up))));
  }
  function tightOpen(p,fn){return open(p,(d,dp)=>open(ar(dp),(f,fp)=>fn(d,f,al(dp),al(fp),ar(fp))));}
  function endOpen(p,fn){return open(p,(d,dp)=>open(ar(dp),(f,fp)=>fn(d,f,al(al(dp)),ar(al(dp)),al(fp),ar(fp))));}
  function makeTight(a,n,v,d,sd,f,rf,vp){
    const g=Tight(a,n,v),body=replace(g[2],g[1],d)[2];
    return ei(g,d,ai(sd,ei(body,f,ai(rf,vp))));
  }
  function makeEnd(a,n,v,d,td,nin,f,rf,vp){
    const g=End(a,n,v),body=replace(g[2],g[1],d)[2];
    return ei(g,d,ai(ai(td,nin),ei(body,f,ai(rf,vp))));
  }
  const tightEnd=qs(3,(a,n,v)=>ii(trans(n),tn=>ii(Tight(a,n,v),tp=>tightOpen(tp,(d,f,sd,rf,vp)=>{
    const td=app(us(st,n,d),tn,sd),nin=into(sd,n,or(M(n,n),ref(n)));
    return makeEnd(a,n,v,d,td,nin,f,rf,vp);
  }))));
  function extendRec(a,b,d,f,r,tb,sd,rf,newOrd,baseRule,nextRule,fn){
    return open(app(us(ap,f,b,d,r),al(rf),sd),(g,gp)=>{
      const gg=al(al(gp)),eqv=ar(al(gp)),gv=ar(gp);
      const rules=ui(i=>ii(M(i,d),id=>ui(v=>ii(Val(g,i,v),vv=>{
        const want=rule(a,g,i,v);
        return oe(from(sd,i,id),want,ib=>{
          const old=app(ar(ue(app(ue(eqv,i),ib),v)),vv);
          const rr=valueRule(a,b,f,i,v,rf,ib,old);
          const step=ui(j=>ii(M(j,i),ji=>ii(Succ(j,i),sji=>ui(u=>ii(Val(g,j,u),uv=>{
            const jb=earlier(tb,i,ib,j,ji);
            const fu=app(ar(ue(app(ue(eqv,j),jb),u)),uv);
            return app(ue(app(ue(ar(rr),j),ji,sji),u),fu);
          })))));
          return ai(al(rr),step);
        },eq=>{
          const bd=into(sd,b,or(M(b,b),ref(b)));
          const bv=eqSub(eq,t=>Val(g,t,v),vv);
          const vr=valEq(gg,b,bd,v,r,bv,gv);
          const step=ui(j=>ii(M(j,b),jb=>ii(Succ(j,b),sjb=>ui(u=>ii(Val(g,j,u),uv=>{
            const fu=app(ar(ue(app(ue(eqv,j),jb),u)),uv);
            return nextRule(j,jb,sjb,u,fu);
          })))));
          const rr=ai(ai(newOrd,baseRule),step);
          const atV=eqSub(sym(vr),z=>rule(a,g,b,z),rr);
          return eqSub(sym(eq),z=>rule(a,g,z,v),atV);
        });
      }))));
      return fn(g,ai(gg,rules),gv);
    });
  }
  function base(a,oa,z,ez){
    const tz=al(emptyOrd(z,ez));
    const graph=ai(ui(p=>ii(M(p,z),pz=>fe(app(ue(ez,p),pz),E(i=>C(M(i,z),E(y=>form("pair",p,i,y))))))),
      ui(i=>ii(M(i,z),iz=>fe(app(ue(ez,i),iz),E(v=>C(Val(z,i,v),A(u=>I(Val(z,i,u),Q(u,v)))))))));
    const rf=ai(graph,ui(i=>ii(M(i,z),iz=>fe(app(ue(ez,i),iz),A(v=>I(Val(z,i,v),rule(a,z,i,v)))))));
    return open(ue(se,z),(d,sd)=>{
      const baseRule=ii(Empty(z),_=>ref(a));
      return extendRec(a,z,d,z,a,tz,sd,rf,oa,baseRule,(j,jz,sj,u,fu)=>fe(app(ue(ez,j),jz),Next(u,a)),(f,rec,vp)=>{
        const tp=makeTight(a,z,a,d,sd,f,rec,vp);
        const unique=ui(u=>ii(End(a,z,u),ep=>endOpen(ep,(e,h,te,zin,rh,uv)=>{
          const rr=valueRule(a,e,h,z,u,rh,zin,uv);
          return app(ar(al(rr)),ez);
        })));
        return ei(Good(a,z),a,ai(tp,unique));
      });
    });
  }
  function succCase(a,n,j,tn,nj,prior,total){
    return open(prior,(v,vp)=>tightOpen(al(vp),(d,f,sd,rf,fv)=>{
      const dj=app(us(su,n,d,j),sd,nj);
      const rf0=eqSub(dj,t=>Rec(a,t,f),rf),nin=into(nj,n,or(M(n,n),ref(n)));
      const vo=al(al(valueRule(a,j,f,n,v,rf0,nin,fv)));
      const tj=app(us(st,n,j),tn,nj);
      return open(app(ue(total,v),vo),(r,rp)=>{
        const ro=al(al(rp)),nr=ar(al(rp)),ru=ar(rp);
        return open(ue(se,j),(e,je)=>{
          const baseRule=ii(Empty(j),ej=>fe(app(ue(ej,n),nin),Q(r,a)));
          return extendRec(a,j,e,f,r,tj,je,rf0,ro,baseRule,(k,kj,sk,u,fu)=>{
            const kn=app(us(pu,k,n,j),sk,nj);
            const nu=eqSub(kn,t=>Val(f,t,u),fu);
            const uv=valEq(al(rf0),n,nin,u,v,nu,fv);
            return eqSub(sym(uv),x=>Next(x,r),nr);
          },(g,rg,gr)=>{
            const tp=makeTight(a,j,r,e,je,g,rg,gr);
            const unique=ui(u=>ii(End(a,j,u),ep=>endOpen(ep,(z,h,tz,jin,rh,hu)=>{
              const nh=earlier(tz,j,jin,n,nin);
              return open(app(ue(ar(al(rh)),n),nh),(w,wp)=>{
                const end=makeEnd(a,n,w,z,tz,nh,h,rh,al(wp));
                const wv=app(ue(ar(vp),w),end);
                const rr=valueRule(a,z,h,j,u,rh,jin,hu);
                const step=app(ue(app(ue(ar(rr),n),nin,nj),w),al(wp));
                return app(ue(ru,u),eqSub(wv,t=>Next(t,u),step));
              });
            })));
            return ei(Good(a,j),r,ai(tp,unique));
          });
        });
      });
    }));
  }
  const iteration=ii(StepTotal,total=>qs(2,(a,w)=>ii(Ord(a),oa=>ii(Omega(w),ow=>{
    // Separate n in omega satisfying Good; prove inductive, then leastness.
    const v=fresh(),spec={name:"separation",params:1,body:db(Good(a,v),[v,a])};
    return open(us(ax(spec),a,w),(c,cp)=>{
      // The least inductive set is transitive. Prove just this needed
      // property by separating those elements which are subsets of w.
      // Prove the stronger fact every member of omega is transitive.
      const q2=fresh(),spec2={name:"separation",params:0,body:db(trans(q2),[q2])};
      const each=open(ue(ax(spec2),w),(t,tp)=>{
        const base0=open(al(al(ow)),(z,zp)=>ei(E(z=>C(M(z,t),Empty(z))),z,ai(into(tp,z,ai(al(zp),al(emptyOrd(z,ar(zp))))),ar(zp))));
        const step0=ui(i=>ii(M(i,t),it=>{
          const iw=al(from(tp,i,it)),ti=ar(from(tp,i,it));
          return open(app(ue(ar(al(ow)),i),iw),(j,jp)=>{
            const tj=app(us(st,i,j),ti,ar(jp));
            return ei(E(j=>C(M(j,t),Succ(i,j))),j,ai(into(tp,j,ai(al(jp),tj)),ar(jp)));
          });
        }));
        const wt=app(ue(ar(ow),t),ai(base0,step0));
        return ui(i=>ii(M(i,w),iw=>ar(from(tp,i,app(ue(wt,i),iw)))));
      });
      return use(each,transMembers=>{
        const b=open(al(al(ow)),(z,zp)=>{
          const gd=base(a,oa,z,ar(zp));
          return ei(E(z=>C(M(z,c),Empty(z))),z,ai(into(cp,z,ai(al(zp),gd)),ar(zp)));
        });
        const step=ui(i=>ii(M(i,c),ic=>{
          const iw=al(from(cp,i,ic)),gd=ar(from(cp,i,ic)),ti=app(ue(transMembers,i),iw);
          return open(app(ue(ar(al(ow)),i),iw),(j,jp)=>{
            const good=succCase(a,i,j,ti,ar(jp),gd,total);
            return ei(E(j=>C(M(j,c),Succ(i,j))),j,ai(into(cp,j,ai(al(jp),good)),ar(jp)));
          });
        }));
        const wc=app(ue(ar(ow),c),ai(b,step));
        return ui(n=>ii(M(n,w),nw=>ar(from(cp,n,app(ue(wc,n),nw)))));
      });
    });
  }))));
  // A graph-free endpoint relation is functional on omega; collect
  // endpoint values by Replacement to obtain the set of iterates.
  const endpointTotal=ii(StepTotal,total=>qs(2,(a,w)=>ii(Ord(a),oa=>ii(Omega(w),ow=>{
    const g=app(us(app(iteration,total),a,w),oa,ow);
    const q=fresh(),spec={name:"separation",params:0,body:db(trans(q),[q])};
    return open(ue(ax(spec),w),(t,tp)=>{
      const base0=open(al(al(ow)),(z,zp)=>ei(E(z=>C(M(z,t),Empty(z))),z,ai(into(tp,z,ai(al(zp),al(emptyOrd(z,ar(zp))))),ar(zp))));
      const step0=ui(i=>ii(M(i,t),it=>open(app(ue(ar(al(ow)),i),al(from(tp,i,it))),(j,jp)=>{
        const tj=app(us(st,i,j),ar(from(tp,i,it)),ar(jp));
        return ei(E(j=>C(M(j,t),Succ(i,j))),j,ai(into(tp,j,ai(al(jp),tj)),ar(jp)));
      })));
      const wt=app(ue(ar(ow),t),ai(base0,step0));
      const each=ui(i=>ii(M(i,w),iw=>ar(from(tp,i,app(ue(wt,i),iw)))));
      return ui(n=>ii(M(n,w),nw=>open(app(ue(g,n),nw),(v,vp)=>{
        const ep=app(us(tightEnd,a,n,v),app(ue(each,n),nw),al(vp));
        return ei(goalEnd(a,n),v,ai(ep,ar(vp)));
      })));
    });
  }))));
  const rangeSpec=(a,w,R)=>A(v=>B(M(v,R),E(n=>C(M(n,w),End(a,n,v)))));
  const rangeExists=ii(StepTotal,total=>qs(2,(a,w)=>ii(Ord(a),oa=>ii(Omega(w),ow=>{
    const n=fresh(),v=fresh(),spec={name:"replacement",params:1,body:db(End(a,n,v),[v,n,a])};
    const fun=app(us(app(endpointTotal,total),a,w),oa,ow);
    return app(us(ax(spec),a,w),fun);
  }))));

  const strictFormula=A(a=>A(b=>I(Next(a,b),C(Ord(b),M(a,b)))));
  const rangeGood=(a,w,R)=>C(C(A(v=>I(M(v,R),Ord(v))),M(a,R)),A(v=>I(M(v,R),E(r=>C(M(r,R),Next(v,r))))));
  // The conditional theorem uses the exact omega ordinal property.
  // It avoids any repeated construction of the ambient omega proof.
  function rangeProperties(a,w,R,oa,ow,ordw,it,rp){
    const allOrd=ui(v=>ii(M(v,R),vr=>open(from(rp,v,vr),(n,np)=>endOpen(ar(np),(d,f,td,nin,rf,vp)=>al(al(valueRule(a,d,f,n,v,rf,nin,vp)))))));
    const base=open(al(al(ow)),(z,zp)=>{
      const zw=al(zp),ez=ar(zp),tz=app(ue(ar(ordw),z),zw);
      return open(app(ue(it,z),zw),(v,vp)=>{
        const ep=app(us(tightEnd,a,z,v),tz,al(vp));
        return endOpen(ep,(d,f,td,zin,rf,vr)=>{
          const va=app(ar(al(valueRule(a,d,f,z,v,rf,zin,vr))),ez);
          const ea=eqSub(va,t=>End(a,z,t),ep);
          return into(rp,a,ei(ar(ue(rp,a)).goal[1],z,ai(zw,ea)));
        });
      });
    });
    const closed=ui(v=>ii(M(v,R),vr=>open(from(rp,v,vr),(n,np)=>{
      const nw=al(np),ev=ar(np);
      return open(app(ue(ar(al(ow)),n),nw),(j,jp)=>{
        const jw=al(jp),nj=ar(jp),nin=into(nj,n,or(M(n,n),ref(n))),tj=app(ue(ar(ordw),j),jw);
        return open(app(ue(it,j),jw),(r,rp0)=>tightOpen(al(rp0),(d,f,sd,rf,rv)=>{
          const td=app(us(st,j,d),tj,sd),jin=into(sd,j,or(M(j,j),ref(j))),nd=into(sd,n,ol(nin,Q(n,j)));
          return open(app(ue(ar(al(rf)),n),nd),(u,up)=>{
            const ue0=makeEnd(a,n,u,d,td,nd,f,rf,al(up));
            const rr=valueRule(a,d,f,j,r,rf,jin,rv);
            const step=app(ue(app(ue(ar(rr),n),nin,nj),u),al(up));
            return open(app(ue(it,n),nw),(b,bp)=>{
              const ub=app(ue(ar(bp),u),ue0),vb=app(ue(ar(bp),v),ev);
              const uv=chain(ub,sym(vb));
              const next=eqSub(uv,t=>Next(t,r),step);
              const endr=makeEnd(a,j,r,d,td,jin,f,rf,rv);
              const rR=into(rp,r,ei(ar(ue(rp,r)).goal[1],j,ai(jw,endr)));
              return ei(E(r=>C(M(r,R),Next(v,r))),r,ai(rR,next));
            });
          });
        }));
      });
    })));
    return ai(ai(allOrd,base),closed);
  }
  const rangeClosed=ii(StepTotal,total=>qs(2,(a,w)=>ii(Ord(a),oa=>ii(Omega(w),ow=>ii(Ord(w),ordw=>{
    const it=app(us(app(iteration,total),a,w),oa,ow);
    return open(app(us(app(rangeExists,total),a,w),oa,ow),(R,rp)=>{
      const prop=rangeProperties(a,w,R,oa,ow,ordw,it,rp);
      return ei(E(R=>rangeGood(a,w,R)),R,prop);
    });
  })))));
  const proofs={tight_endpoint_is_endpoint:tightEnd,finite_iteration_conditional:iteration,omega_endpoint_total_conditional:endpointTotal,omega_range_exists_conditional:rangeExists,omega_range_closed_conditional:rangeClosed};
  return {stepTotal:db(StepTotal,[]),endpointFormula:(()=>{const a=fresh(),n=fresh(),v=fresh();return db(End(a,n,v),[v,n,a]);})(),proofs:Object.fromEntries(Object.entries(proofs).filter(([n])=>only===null||only.includes(n)).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]))};
}
