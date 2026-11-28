// ACE-03X. Uniform recursion for a supplied pure set-language local step.
// The exported conditional theorems retain every step contract explicitly.
import { kernel, scoped } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';

function buildUniformHistoryRecursion(defs, step, parameterCount=0, options={}) {
  if(!Number.isSafeInteger(parameterCount)||parameterCount<0||!scoped(step,3+parameterCount,false))
    throw Error('uniform recursion requires a pure step with free layout [history,index,value,...params]');
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
  const parameters=Array.from({length:parameterCount},fresh);
  const Val=(f,i,r)=>form("val",f,i,r),Graph=(f,d)=>form("graph",f,d),Succ=(a,b)=>form("successor",a,b),Ord=a=>form("ordinal",a);
  const Stage=(f,b,r)=>named(step,[f,b,r,...parameters]);
  const SG=(f,d)=>C(Graph(f,d),A(i=>I(M(i,d),E(r=>C(Val(f,i,r),Stage(f,i,r))))));
  function eqSub(eq,prop,proof){
    const v=fresh(),g=prop(v);
    return P(replace(g,v,eq.goal[2]),(e,h)=>["eqS",db(g,[v,...e]),eq.emit(e,h),proof.emit(e,h)]);
  }
  const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  function use(p,fn){return ie(ii(p.goal,fn),p);}
  function using(ps,fn){
    const joined=ps.reduce(ai),project=(p,i,n)=>n===1?p:i===n-1?ar(p):project(al(p),i,n-1);
    return use(joined,p=>fn(ps.map((_,i)=>project(p,i,ps.length))));
  }
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
  function imported(p){return P(named(p.goal,[]),(_,h)=>h.length?shiftHyps(p.proof,h.length):p.proof);}
  const {pair_injective,pair_exists}=buildF(defs);
  const {no_two_cycle,ordinal_successor_transitivity,graph_extensionality}=buildE(defs,true);
  const pairInj=imported(pair_injective),pairEx=imported(pair_exists);
  const noCycle=imported(no_two_cycle),succTrans=imported(ordinal_successor_transitivity);
  const graphExt=imported(graph_extensionality);
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
  const Total= A(f=>A(b=>I(Ord(b),I(SG(f,b),E(r=>Stage(f,b,r))))));
  const GraphTotal=A(f=>A(b=>I(Graph(f,b),E(r=>Stage(f,b,r)))));
  const Functional=A(f=>A(b=>A(r=>A(t=>I(SG(f,b),I(Stage(f,b,r),I(Stage(f,b,t),Q(r,t))))))));
  const Local=A(f=>A(g=>A(b=>A(r=>I(eqvVals(f,g,b),I(Stage(f,b,r),Stage(g,b,r)))))));
  function boundedInduction(property,paramCount){
    function quantify(ps){
      if(ps.length<paramCount)return ui(p=>quantify([...ps,p]));
      const PAt=x=>named(property,[x,...ps]);
      const step=a=>A(y=>I(M(y,a),I(A(z=>I(M(z,y),PAt(z))),PAt(y))));
      return ui(a=>ii(trans(a),ta=>ii(step(a),st=>ui(x=>ii(M(x,a),xa=>{
        const v=fresh(),spec={name:"separation",params:paramCount,body:db(N(PAt(v)),[v,...ps])};
        let sep=ax(spec);
        for(const p of ps.slice().reverse())sep=ue(sep,p);
        sep=ue(sep,a);
        const nn=ii(N(PAt(x)),nx=>{
          return ee(sep,F,(bad,sb)=>{
            const xb=ie(ar(ue(sb,x)),ai(xa,nx));
            const nz=E(y=>M(y,bad));
            const found=ie(ue(ax({name:"foundation"}),bad),ei(nz,x,xb));
            return ee(found,F,(y,fy)=>{
              const by=ie(al(ue(sb,y)),al(fy)),ya=al(by),ny=ar(by);
              const pred=ui(z=>ii(M(z,y),zy=>{
                const za=ie(ue(ie(ue(ta,y),ya),z),zy);
                return dn(ii(N(PAt(z)),nz=>{
                  const zb=ie(ar(ue(sb,z)),ai(za,nz));
                  return ie(ie(ue(ar(fy),z),zy),zb);
                }));
              }));
              return ie(ny,ie(ie(ue(st,y),ya),pred));
            });
          });
        });
        return dn(nn);
      })))));
    }
    return quantify([]);
  }

  const exactRestriction=(h,f,e)=>A(p=>B(M(p,h),C(M(p,f),E(i=>C(M(i,e),E(y=>form('pair',p,i,y)))))));
  function restriction(f,d,e,te,inc,sf,local){
    const qualify=p=>E(i=>C(M(i,e),E(y=>form('pair',p,i,y))));
    const v=fresh(),spec={name:'separation',params:1,body:db(qualify(v),[v,e])};
    return open(us(ax(spec),e,f),(h,hp)=>{
      function toF(i,r,p){
        return open(p,(w,wp)=>ei(Val(f,i,r),w,ai(al(from(hp,w,al(wp))),ar(wp))));
      }
      function toH(i,r,im,p){
        return open(p,(w,wp)=>{
          const qual=qualify(w),inner=replace(qual[2],qual[1],i)[2];
          const wh=into(hp,w,ai(al(wp),ei(qual,i,ai(im,ei(inner,r,ar(wp))))));
          return ei(Val(h,i,r),w,ai(wh,ar(wp)));
        });
      }
      const eqv=ui(i=>ii(M(i,e),im=>ui(r=>ai(ii(Val(h,i,r),p=>toF(i,r,p)),ii(Val(f,i,r),p=>toH(i,r,im,p))))));
      return use(eqv,ev=>{
        const graph=ai(ui(p=>ii(M(p,h),ph=>ar(from(hp,p,ph)))),ui(i=>ii(M(i,e),im=>{
          const id=app(ue(inc,i),im);
          return open(app(ue(ar(al(sf)),i),id),(r,rv)=>{
            const value=app(ar(ue(app(ue(ev,i),im),r)),al(rv));
            const unique=ui(s=>ii(Val(h,i,s),vs=>app(ue(ar(rv),s),app(al(ue(app(ue(ev,i),im),s)),vs))));
            return ei(E(y=>C(Val(h,i,y),A(z=>I(Val(h,i,z),Q(z,y))))),r,ai(value,unique));
          });
        })));
        const steps=ui(b=>ii(M(b,e),be=>{
          const bd=app(ue(inc,b),be);
          return open(app(ue(ar(sf),b),bd),(r,rv)=>{
            const hv=app(ar(ue(app(ue(ev,b),be),r)),al(rv));
            const eq=ui(i=>ii(M(i,b),ib=>{
              const ie0=earlier(te,b,be,i,ib);
              return ui(y=>{
                const at=ue(app(ue(ev,i),ie0),y);
                return ai(ar(at),al(at));
              });
            }));
            const st=app(us(local,f,h,b,r),eq,ar(rv));
            return ei(E(r=>C(Val(h,b,r),Stage(h,b,r))),r,ai(hv,st));
          });
        }));
        return ei(E(h=>C(SG(h,e),C(eqvVals(h,f,e),exactRestriction(h,f,e)))),h,ai(ai(graph,steps),ai(ev,hp)));
      });
    });
  }
  const restrict=ii(Local,local=>qs(3,(f,d,e)=>ii(trans(e),te=>ii(subset(e,d),inc=>ii(SG(f,d),sf=>restriction(f,d,e,te,inc,sf,local))))));

  function ordinalMember(b,i,ob,ib){
    const ti=app(ue(ar(ob),i),ib);
    const members=ui(j=>ii(M(j,i),ji=>app(ue(ar(ob),j),earlier(al(ob),i,ib,j,ji))));
    return ai(ti,members);
  }
  const ordinalMemberProof=qs(2,(b,i)=>ii(Ord(b),ob=>ii(M(i,b),ib=>ordinalMember(b,i,ob,ib))));
  const ordinalSucc=use(succTrans,st=>qs(2,(b,d)=>ii(Ord(b),ob=>ii(Succ(b,d),sd=>{
    const td=app(us(st,b,d),al(ob),sd);
    const members=ui(x=>ii(M(x,d),xd=>oe(from(sd,x,xd),trans(x),
      xb=>app(ue(ar(ob),x),xb),eq=>eqSub(sym(eq),trans,al(ob)))));
    return ai(td,members);
  }))));
  function valUnique(sg,i,im,x,y,vx,vy){
    return open(app(ue(ar(al(sg)),i),im),(v,uv)=>chain(app(ue(ar(uv),x),vx),sym(app(ue(ar(uv),y),vy))));
  }
  const agreeAt=(f,g,e,b)=>I(M(b,e),A(r=>I(Val(f,b,r),A(s=>I(Val(g,b,s),Q(r,s))))));
  const af=fresh(),ag=fresh(),ae=fresh(),ab=fresh();
  const agreeInd=boundedInduction(db(agreeAt(af,ag,ae,ab),[ab,af,ag,ae]),3);
  function agreeGraphs(f,g,d,e,od,oe0,sf,sg,functional,local,re,ind){
    const td=al(od),te=al(oe0);
    const stepProof=ui(b=>ii(M(b,d),bd=>ii(A(i=>I(M(i,b),agreeAt(f,g,e,i))),ih=>ii(M(b,e),be=>{
      const inD=(i,ib)=>earlier(td,b,bd,i,ib),inE=(i,ib)=>earlier(te,b,be,i,ib);
      function equalPrev(i,ib,r,s,vr,vs){
        return app(ue(app(ue(app(ue(ih,i),ib,inE(i,ib)),r),vr),s),vs);
      }
      const eqv=ui(i=>ii(M(i,b),ib=>ui(r=>ai(
        ii(Val(f,i,r),vr=>open(app(ue(ar(al(sg)),i),inE(i,ib)),(s,vs)=>{
          const rs=equalPrev(i,ib,r,s,vr,al(vs));
          return eqSub(sym(rs),x=>Val(g,i,x),al(vs));
        })),
        ii(Val(g,i,r),vr=>open(app(ue(ar(al(sf)),i),inD(i,ib)),(s,vs)=>{
          const sr=equalPrev(i,ib,s,r,al(vs),vr);
          return eqSub(sr,x=>Val(f,i,x),al(vs));
        }))
      ))));
      return use(eqv,fg=>{
        const tb=al(ordinalMember(d,b,od,bd)),inc=ui(i=>ii(M(i,b),ib=>inD(i,ib)));
        return open(app(us(re,f,d,b),tb,inc,sf),(h,hp)=>{
          const hf=al(ar(hp));
          const fh=ui(i=>ii(M(i,b),ib=>ui(r=>{
            const at=ue(app(ue(hf,i),ib),r);return ai(ar(at),al(at));
          })));
          const gh=ui(i=>ii(M(i,b),ib=>ui(r=>{
            const left=ue(app(ue(fg,i),ib),r),right=ue(app(ue(hf,i),ib),r);
            return ai(ii(Val(g,i,r),v=>app(ar(right),app(ar(left),v))),ii(Val(h,i,r),v=>app(al(left),app(al(right),v))));
          })));
          return ui(r=>ii(Val(f,b,r),vr=>ui(s=>ii(Val(g,b,s),vs=>{
            return open(app(ue(ar(sf),b),bd),(a,pa)=>open(app(ue(ar(sg),b),be),(c,pc)=>{
              const ha=app(us(local,f,h,b,a),fh,ar(pa));
              const hc=app(us(local,g,h,b,c),gh,ar(pc));
              const ac=app(us(functional,h,b,a,c),al(hp),ha,hc);
              const ra=valUnique(sf,b,bd,r,a,vr,al(pa));
              const cs=valUnique(sg,b,be,c,s,al(pc),vs);
              return chain(chain(ra,ac),cs);
            }));
          }))));
        });
      });
    }))));
    return app(us(ind,f,g,e,d),td,stepProof);
  }
  const coh=using([restrict,agreeInd],([re0,ind])=>ii(Functional,fun=>ii(Local,local=>qs(4,(f,g,d,e)=>
    ii(Ord(d),od=>ii(Ord(e),oe0=>ii(SG(f,d),sf=>ii(SG(g,e),sg=>agreeGraphs(f,g,d,e,od,oe0,sf,sg,fun,local,app(re0,local),ind)))))))));
  const unique=using([coh,graphExt],([co0,ge])=>ii(Functional,fun=>ii(Local,local=>qs(3,(f,g,d)=>
    ii(Ord(d),od=>ii(SG(f,d),sf=>ii(SG(g,d),sg=>{
      const agree=app(us(app(co0,fun,local),f,g,d,d),od,od,sf,sg);
      const equiv=ui(i=>ii(M(i,d),id=>ui(r=>{
        function convert(tgt,other,p,reverse){
          return open(app(ue(ar(other),i),id),(a,av)=>{
            const common=app(ue(agree,i),id,id);
            const eq=reverse?app(ue(app(ue(common,a),al(av)),r),p):app(ue(app(ue(common,r),p),a),al(av));
            return eqSub(reverse?eq:sym(eq),z=>Val(tgt,i,z),al(av));
          });
        }
        return ai(ii(Val(f,i,r),p=>convert(g,sg,p,false)),ii(Val(g,i,r),p=>convert(f,sf,p,true)));
      })));
      return app(us(ge,f,g,d),al(sf),al(sg),equiv);
    })))))));
  function extendHistory(f,b,d,ob,sd,sf,inj,dom,nc,tot,tr,pairExists){
    const tb=al(ob),g0=al(sf),noSelf=ii(M(b,b),bb=>app(us(nc,b,b),bb,bb));
    return use(noSelf,nb=>open(app(us(tot,f,b),ob,sf),(r,rs)=>{
      return open(us(pairExists,b,r),(p,pp)=>{
        return withAdjoin(f,p,(g,gp)=>{
          const valCases=(i,y,v)=>open(v,(w,wp)=>{
            const goal=["|",Val(f,i,y),C(Q(i,b),Q(y,r))];
            return oe(from(gp,w,al(wp)),goal,
              wf=>ol(ei(Val(f,i,y),w,ai(wf,ar(wp))),goal[2]),
              eq=>or(goal[1],app(us(inj,p,i,y,b,r),eqSub(eq,t=>form("pair",t,i,y),ar(wp)),pp)));
          });
          const oldToNew=(i,y,v)=>open(v,(w,wp)=>{
            const wg=into(gp,w,ol(al(wp),Q(w,p)));
            return ei(Val(g,i,y),w,ai(wg,ar(wp)));
          });
          const newValue=ei(Val(g,b,r),p,ai(into(gp,p,or(M(p,f),ref(p))),pp));
          const oldEquiv=ui(i=>ii(M(i,b),ib=>ui(y=>ai(
            ii(Val(f,i,y),v=>oldToNew(i,y,v)),
            ii(Val(g,i,y),v=>oe(valCases(i,y,v),Val(f,i,y),q=>q,eq=>fe(app(nb,eqSub(al(eq),t=>M(t,b),ib)),Val(f,i,y))))))));
          return use(oldEquiv,eqv=>{
            const entries=ui(w=>ii(M(w,g),wg=>{
              const goal=E(i=>C(M(i,d),E(y=>form("pair",w,i,y))));
              return oe(from(gp,w,wg),goal,
                wf=>open(app(ue(al(g0),w),wf),(i,ip)=>{
                  const id=into(sd,i,ol(al(ip),Q(i,b)));
                  return ei(goal,i,ai(id,ar(ip)));
                }),
                eq=>{
                  const bd=into(sd,b,or(M(b,b),ref(b)));
                  const sub=replace(goal[2],goal[1],b)[2];
                  return ei(goal,b,ai(bd,ei(sub,r,eqSub(sym(eq),t=>form("pair",t,b,r),pp))));
                });
            }));
            const total=ui(i=>ii(M(i,d),id=>{
              const goal=E(y=>C(Val(g,i,y),A(z=>I(Val(g,i,z),Q(z,y)))));
              return oe(from(sd,i,id),goal,
                ib=>open(app(ue(ar(g0),i),ib),(y,yp)=>{
                  const v=app(al(ue(app(ue(eqv,i),ib),y)),al(yp));
                  const u=ui(z=>ii(Val(g,i,z),vz=>app(ue(ar(yp),z),app(ar(ue(app(ue(eqv,i),ib),z)),vz))));
                  return ei(goal,y,ai(v,u));
                }),
                eq=>{
                  const iv=eqSub(sym(eq),t=>Val(g,t,r),newValue);
                  const un=ui(y=>ii(Val(g,i,y),vy=>{
                    const vb=eqSub(eq,t=>Val(g,t,y),vy);
                    return oe(valCases(b,y,vb),Q(y,r),old=>fe(app(nb,app(us(dom,f,b,b,y),g0,old)),Q(y,r)),both=>ar(both));
                  }));
                  return ei(goal,r,ai(iv,un));
                });
            }));
            const steps=ui(i=>ii(M(i,d),id=>{
              const goal=E(y=>C(Val(g,i,y),Stage(g,i,y)));
              return oe(from(sd,i,id),goal,
                ib=>open(app(ue(ar(sf),i),ib),(y,yp)=>{
                  const v=app(al(ue(app(ue(eqv,i),ib),y)),al(yp));
                  const local=ui(j=>ii(M(j,i),ji=>app(ue(eqv,j),earlier(tb,i,ib,j,ji))));
                  const st=app(us(tr,f,g,i,y),local,ar(yp));
                  return ei(goal,y,ai(v,st));
                }),
                eq=>{
                  const st=app(us(tr,f,g,b,r),eqv,rs);
                  const v=eqSub(sym(eq),t=>C(Val(g,t,r),Stage(g,t,r)),ai(newValue,st));
                  return ei(goal,r,v);
                });
            }));
            return ei(E(z=>SG(z,d)),g,ai(ai(entries,total),steps));
          });
        });
      });
    }));
  }
  const extend=using([pairInj,domainLemma,noCycle,pairEx],([inj,dom,nc,pairExists])=>ii(Total,tot=>ii(Local,tr=>{
    return qs(3,(f,b,d)=>ii(Ord(b),ob=>ii(Succ(b,d),sd=>ii(SG(f,b),sf=>extendHistory(f,b,d,ob,sd,sf,inj,dom,nc,tot,tr,pairExists)))));
  })));
  const emptyGraph=ui(d=>ii(Empty(d),ed=>open(ax({name:"empty"}),(f,ef)=>{
    const entries=ui(p=>ii(M(p,f),pf=>fe(app(ue(ef,p),pf),E(i=>C(M(i,d),E(y=>form("pair",p,i,y)))))));
    const total=ui(i=>ii(M(i,d),id=>fe(app(ue(ed,i),id),E(y=>C(Val(f,i,y),A(z=>I(Val(f,i,z),Q(z,y))))))));
    const stages=ui(i=>ii(M(i,d),id=>fe(app(ue(ed,i),id),E(y=>C(Val(f,i,y),Stage(f,i,y))))));
    return ei(E(f=>SG(f,d)),f,ai(ai(entries,total),stages));
  })));

  const good=(h,e,d)=>C(C(Ord(e),subset(e,d)),SG(h,e));
  const goodFamily=(H,d)=>A(h=>I(M(h,H),E(e=>good(h,e,d))));
  const coverFamily=(H,d)=>A(i=>I(M(i,d),E(h=>C(M(h,H),E(e=>C(good(h,e,d),M(i,e)))))));
  const exactUnion=(f,H)=>A(p=>B(M(p,f),E(h=>C(M(h,H),M(p,h)))));
  function glue(H,d,ok,cover,dom,co,tr){
    return withUnion(H,(u,up)=>{
      function fromFamily(h,p,hH,ph){
        return into(up,p,ei(ar(ue(up,p)).goal[1],h,ai(hH,ph)));
      }
      function fromValue(h,i,r,hH,v){
        return open(v,(p,pv)=>ei(Val(u,i,r),p,ai(fromFamily(h,p,hH,al(pv)),ar(pv))));
      }
      function openValue(i,r,v,fn){
        return open(v,(p,pv)=>open(from(up,p,al(pv)),(h,hp)=>{
          const hv=ei(Val(h,i,r),p,ai(ar(hp),ar(pv)));
          return open(app(ue(ok,h),al(hp)),(e,ep)=>{
            const ie=app(us(dom,h,e,i,r),al(ar(ep)),hv);
            return fn(h,e,al(hp),ep,ie,hv);
          });
        }));
      }
      // A union value on a member history's domain agrees with that
      // history. Existence of a value comes from its exact graph.
      function localEq(h,e,hH,ep){
        return ui(i=>ii(M(i,e),ie0=>ui(r=>ai(
          ii(Val(h,i,r),hv=>fromValue(h,i,r,hH,hv)),
          ii(Val(u,i,r),uv=>openValue(i,r,uv,(j,c,jH,cp,ic,jv)=>{
            return open(app(ue(ar(ar(ep)),i),ie0),(y,yp)=>{
              const eqs=app(us(co,j,h,c,e),al(al(cp)),al(al(ep)),ar(cp),ar(ep));
              const eq=app(ue(app(ue(app(ue(eqs,i),ic,ie0),r),jv),y),al(yp));
              return eqSub(sym(eq),z=>Val(h,i,z),al(yp));
            });
          }))
        ))));
      }
      function covered(i,id,fn){
        return open(app(ue(cover,i),id),(h,hp)=>open(ar(hp),(e,ep)=>fn(h,e,al(hp),al(ep),ar(ep))));
      }
      const entries=ui(p=>ii(M(p,u),pu=>{
        return open(from(up,p,pu),(h,hp)=>open(app(ue(ok,h),al(hp)),(e,ep)=>{
          return open(app(ue(al(al(ar(ep))),p),ar(hp)),(i,ip)=>{
            const id=app(ue(ar(al(ep)),i),al(ip));
            return ei(E(i=>C(M(i,d),E(y=>form("pair",p,i,y)))),i,ai(id,ar(ip)));
          });
        }));
      }));
      const total=ui(i=>ii(M(i,d),id=>covered(i,id,(h,e,hH,ep,ie0)=>{
        const eqv=localEq(h,e,hH,ep);
        return open(app(ue(ar(al(ar(ep))),i),ie0),(r,rp)=>{
          return use(app(ue(eqv,i),ie0),at=>{
            const uv=app(al(ue(at,r)),al(rp));
            const uniq=ui(y=>ii(Val(u,i,y),yv=>app(ue(ar(rp),y),app(ar(ue(at,y)),yv))));
            return ei(E(r=>C(Val(u,i,r),A(y=>I(Val(u,i,y),Q(y,r))))),r,ai(uv,uniq));
          });
        });
      })));
      const steps=ui(i=>ii(M(i,d),id=>covered(i,id,(h,e,hH,ep,ie0)=>{
        return open(app(ue(ar(ar(ep)),i),ie0),(r,rp)=>{
          const eqv=localEq(h,e,hH,ep);
          return use(eqv,ev=>{
            const uv=app(al(ue(app(ue(ev,i),ie0),r)),al(rp));
            const sub=ui(j=>ii(M(j,i),ji=>app(ue(ev,j),earlier(al(al(al(ep))),i,ie0,j,ji))));
            const st=app(us(tr,h,u,i,r),sub,ar(rp));
            return ei(E(r=>C(Val(u,i,r),Stage(u,i,r))),r,ai(uv,st));
          });
        });
      })));
      return ei(E(f=>C(SG(f,d),exactUnion(f,H))),u,ai(ai(ai(entries,total),steps),up));
    });
  }
  const glueHistories=using([domainLemma,coh],([dom,co0])=>ii(Functional,fun=>ii(Local,tr=>{
    const co=app(co0,fun,tr);
    return qs(2,(H,d)=>ii(goodFamily(H,d),ok=>ii(coverFamily(H,d),cv=>glue(H,d,ok,cv,dom,co,tr))));
  })));
  const glueSimple=use(glueHistories,gl0=>ii(Functional,fun=>ii(Local,local=>qs(2,(H,d)=>
    ii(goodFamily(H,d),ok=>ii(coverFamily(H,d),cv=>open(app(us(app(gl0,fun,local),H,d),ok,cv),(f,fp)=>ei(E(f=>SG(f,d)),f,al(fp)))))))));
  const Hist=(i,h)=>E(e=>C(Succ(i,e),SG(h,e)));
  const Prop=i=>I(Ord(i),E(h=>Hist(i,h)));
  const histUnique=using([succUnique,unique,ordinalSucc],([su,un0,st])=>ii(Functional,fun=>ii(Local,local=>{
    const un=app(un0,fun,local);
    return qs(3,(i,h,g)=>ii(Ord(i),ti=>ii(Hist(i,h),hh=>ii(Hist(i,g),gg=>{
      return open(hh,(d,dp)=>open(gg,(e,ep)=>{
        const de=app(us(su,i,d,e),al(dp),al(ep));
        const td=app(us(st,i,d),ti,al(dp));
        return app(us(un,h,g,d),td,ar(dp),eqSub(sym(de),x=>SG(g,x),ar(ep)));
      }));
    }))));
  })));
  function histStep(b,ob,ih,hu,gl,ext,suc,st){
    function getHist(i,ib){return app(app(ue(ih,i),ib),ordinalMember(b,i,ob,ib));}
    function histGood(i,ib,h,hh){
      return open(hh,(e,ep)=>{
        const ti=ordinalMember(b,i,ob,ib);
        const te=app(us(st,i,e),ti,al(ep));
        const inc=ui(j=>ii(M(j,e),je=>oe(from(al(ep),j,je),M(j,b),ji=>earlier(al(ob),i,ib,j,ji),eq=>eqSub(sym(eq),z=>M(z,b),ib))));
        const ie0=into(al(ep),i,or(M(i,i),ref(i)));
        return ei(E(e=>C(good(h,e,b),M(i,e))),e,ai(ai(ai(te,inc),ar(ep)),ie0));
      });
    }
    const i0=fresh(),h0=fresh(),spec={name:"replacement",params:parameterCount,body:db(Hist(i0,h0),[h0,i0,...parameters])};
    const total=ui(i=>ii(M(i,b),ib=>open(getHist(i,ib),(h,hh)=>{
      const ti=ordinalMember(b,i,ob,ib);
      const un=ui(g=>ii(Hist(i,g),gg=>app(us(hu,i,g,h),ti,gg,hh)));
      return ei(E(h=>C(Hist(i,h),A(g=>I(Hist(i,g),Q(g,h))))),h,ai(hh,un));
    })));
    return open(app(us(ax(spec),...parameters.slice().reverse(),b),total),(H,img)=>{
      const ok=ui(h=>ii(M(h,H),hH=>open(from(img,h,hH),(i,ip)=>{
        return open(histGood(i,al(ip),h,ar(ip)),(e,ep)=>ei(E(e=>good(h,e,b)),e,al(ep)));
      })));
      const cv=ui(i=>ii(M(i,b),ib=>open(getHist(i,ib),(h,hh)=>{
        const hH=into(img,h,ei(ar(ue(img,h)).goal[1],i,ai(ib,hh)));
        const hg=histGood(i,ib,h,hh);
        return ei(E(h=>C(M(h,H),E(e=>C(good(h,e,b),M(i,e))))),h,ai(hH,hg));
      })));
      return open(app(us(gl,H,b),ok,cv),(f,sf)=>{
        return open(ue(suc,b),(d,sd)=>{
          return open(app(us(ext,f,b,d),ob,sd,sf),(g,sg)=>{
            return ei(E(h=>Hist(b,h)),g,ei(Hist(b,g),d,ai(sd,sg)));
          });
        });
      });
    });
  }
  const b0=fresh(),existInd=boundedInduction(db(Prop(b0),[b0,...parameters]),parameterCount);
  const successorHistoryExistence=using([histUnique,glueSimple,extend,successorExists,ordinalSucc,existInd],([hu0,gl0,ext0,suc,st,ind])=>
    ii(Total,tot=>ii(Functional,fun=>ii(Local,local=>{
      const hu=app(hu0,fun,local),gl=app(gl0,fun,local),ext=app(ext0,tot,local);
      return ui(b=>ii(Ord(b),ob=>open(ue(suc,b),(d,sd)=>{
        const od=app(us(st,b,d),ob,sd);
        const stepProof=ui(i=>ii(M(i,d),id=>ii(A(j=>I(M(j,i),Prop(j))),ih=>ii(Ord(i),oi=>histStep(i,oi,ih,hu,gl,ext,suc,st)))));
        const all=app(us(ind,...parameters,d),al(od),stepProof);
        const bd=into(sd,b,or(M(b,b),ref(b)));
        return app(app(ue(all,b),bd),ob);
      })));
    }))));
  const historyExists=using([successorHistoryExistence,restrict],([he0,re0])=>ii(Total,tot=>ii(Functional,fun=>ii(Local,local=>{
    const he=app(he0,tot,fun,local),re=app(re0,local);
    return ui(b=>ii(Ord(b),ob=>{
      return open(app(ue(he,b),ob),(g,gh)=>open(gh,(d,dh)=>{
        const inc=ui(i=>ii(M(i,b),ib=>into(al(dh),i,ol(ib,Q(i,b)))));
        return open(app(us(re,g,d,b),al(ob),inc,ar(dh)),(f,fp)=>ei(E(f=>SG(f,b)),f,al(fp)));
      }));
    }));
  }))));
  const historyExistsUnique=using([historyExists,unique],([he0,un0])=>ii(Total,tot=>ii(Functional,fun=>ii(Local,local=>{
    const he=app(he0,tot,fun,local),un=app(un0,fun,local);
    return ui(b=>ii(Ord(b),ob=>{
      return open(app(ue(he,b),ob),(f,sf)=>{
        const uq=ui(g=>ii(SG(g,b),sg=>app(us(un,g,f,b),ob,sg,sf)));
        return ei(E(f=>C(SG(f,b),A(g=>I(SG(g,b),Q(g,f))))),f,ai(sf,uq));
      });
    }));
  }))));
  const graphTotalImpliesTotal=ii(GraphTotal,gt=>qs(2,(f,b)=>ii(Ord(b),ob=>ii(SG(f,b),sf=>app(us(gt,f,b),al(sf))))));
  const graphHistoryExistsUnique=using([historyExistsUnique,graphTotalImpliesTotal],([he,bridge])=>ii(GraphTotal,gt=>ii(Functional,fun=>ii(Local,local=>app(he,app(bridge,gt),fun,local)))));

  const stageWitness=(b,r)=>E(d=>C(Succ(b,d),E(f=>C(SG(f,d),Val(f,b,r)))));
  const ordinalValueExists=use(successorHistoryExistence,he0=>ii(Total,tot=>ii(Functional,fun=>ii(Local,local=>{
    const he=app(he0,tot,fun,local);
    return ui(b=>ii(Ord(b),ob=>{
      return open(app(ue(he,b),ob),(f,fh)=>open(fh,(d,dh)=>{
        const bd=into(al(dh),b,or(M(b,b),ref(b)));
        return open(app(ue(ar(al(ar(dh))),b),bd),(r,rp)=>
          ei(E(r=>stageWitness(b,r)),r,ei(stageWitness(b,r),d,ai(al(dh),ei(E(f=>C(SG(f,d),Val(f,b,r))),f,ai(ar(dh),al(rp)))))));
      }));
    }));
  }))));
  const ordinalValueUnique=using([coh,ordinalSucc],([co0,os])=>ii(Functional,fun=>ii(Local,local=>{
    const co=app(co0,fun,local);
    return qs(3,(b,r,s)=>ii(Ord(b),ob=>ii(stageWitness(b,r),wr=>ii(stageWitness(b,s),ws=>{
      return open(wr,(d,dp)=>open(ar(dp),(f,fp)=>open(ws,(e,ep)=>open(ar(ep),(g,gp)=>{
        const od=app(us(os,b,d),ob,al(dp)),oe0=app(us(os,b,e),ob,al(ep));
        const bd=into(al(dp),b,or(M(b,b),ref(b))),be=into(al(ep),b,or(M(b,b),ref(b)));
        const agree=app(us(co,f,g,d,e),od,oe0,al(fp),al(gp));
        return app(ue(app(ue(app(ue(agree,b),bd,be),r),ar(fp)),s),ar(gp));
      }))));
    }))));
  })));

  function close(p){
    for(const x of parameters.slice().reverse()){
      const q=p;p=P(['A',x,q.goal],(e,h)=>['uI',q.emit([x,...e],h)]);
    }
    return p;
  }
  const proofs={
    history_restriction_exact:restrict,
    ordinal_successor:ordinalSucc,
    history_coherence:coh,
    history_unique:unique,
    history_extension:extend,
    empty_history_exists:emptyGraph,
    compatible_history_union_exact:glueHistories,
    successor_history_unique:histUnique,
    successor_history_exists:successorHistoryExistence,
    ordinal_history_exists:historyExists,
    ordinal_history_exists_unique:historyExistsUnique,
    graph_total_implies_history_total:graphTotalImpliesTotal,
    graph_total_ordinal_history_exists_unique:graphHistoryExistsUnique,
    ordinal_value_exists:ordinalValueExists,
    ordinal_value_unique:ordinalValueUnique
  };
  const f=fresh(),g=fresh(),d=fresh(),e=fresh(),b=fresh(),r=fresh(),H=fresh();
  const formulas={
    step:structuredClone(step),history:db(SG(f,d),[f,d,...parameters]),
    total:db(Total,parameters),graph_total:db(GraphTotal,parameters),
    functional:db(Functional,parameters),local:db(Local,parameters),
    value_agreement:db(eqvVals(f,g,b),[f,g,b]),
    restriction:db(exactRestriction(g,f,e),[g,f,e]),
    good_family:db(goodFamily(H,d),[H,d,...parameters]),
    cover_family:db(coverFamily(H,d),[H,d,...parameters]),
    union_graph:db(exactUnion(f,H),[f,H]),
    successor_history:db(Hist(b,f),[b,f,...parameters]),
    value_witness:db(stageWitness(b,r),[b,r,...parameters])
  };
  const selected=options.only===undefined?Object.keys(proofs):options.only;
  if(!Array.isArray(selected)||selected.some(name=>!Object.hasOwn(proofs,name)))throw Error('unknown uniform recursion proof selection');
  return {parameterCount,formulas,proofs:Object.fromEntries(selected.map(name=>{
    const p=proofs[name];
    const q=close(p);return [name,{goal:db(q.goal,[]),proof:q.emit([],[])}];
  }))};
}

export { buildUniformHistoryRecursion };
