import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildI } from './stage_recursion.mjs';
function buildL(defs,prior,finite,stages,extended=false){
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


  const se=imported(stages.successor_exists),su=imported(stages.successor_unique),st=imported(prior.ordinal_successor_transitivity);
  const om=imported(stages.ordinal_member),nc=imported(prior.no_two_cycle),os=imported(stages.ordinal_successor);
  const ov=imported(stages.ordinal_stage_value_exists),mono=imported(stages.ordinal_stage_value_monotone);
  const sm=imported(stages.stage_members_constructible),ot=imported(stages.ordinal_stage_value_transitive),dc=imported(stages.definable_subset_constructible);
  const L=x=>form("L",x);
  const W=(a,r)=>E(d=>C(Succ(a,d),E(f=>C(SG(f,d),Val(f,a,r)))));
  const noSelf=ui(x=>ii(M(x,x),xx=>app(us(nc,x,x),xx,xx)));
  const cmp=(a,b)=>["|",M(a,b),["|",Q(a,b),M(b,a)]];
  const cmpP=a=>I(Ord(a),A(b=>I(Ord(b),cmp(a,b))));
  const v0=fresh(),cmpInd=boundedInduction(db(cmpP(v0),[v0]),0);
  function comparisonStep(a,oa,ih,b,ob){
    const target=cmp(a,b);
    return oe(em(M(b,a)),target,ba=>or(M(a,b),or(Q(a,b),ba)),nba=>{
      const ab=ui(x=>ii(M(x,a),xa=>{
        const ox=app(us(om,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),b),ob);
        return oe(cx,M(x,b),xb=>xb,rest=>oe(rest,M(x,b),eq=>{
          return fe(app(nba,eqSub(eq,z=>M(z,a),xa)),M(x,b));
        },bx=>fe(app(nba,app(ue(app(ue(al(oa),x),xa),b),bx)),M(x,b))));
      }));
      const bad=E(y=>C(M(y,b),N(M(y,a))));
      return oe(em(bad),target,some=>{
        const y0=fresh(),spec={name:"separation",params:1,body:db(N(M(y0,a)),[y0,a])};
        return open(us(ax(spec),a,b),(c,cp)=>{
          const ne=open(some,(y,yp)=>ei(E(x=>M(x,c)),y,into(cp,y,yp)));
          return open(app(ue(ax({name:"foundation"}),c),ne),(y,yp)=>{
            const bc=from(cp,y,al(yp)),yb=al(bc),nya=ar(bc),oy=app(us(om,b,y),ob,yb);
            const ya=ui(z=>ii(M(z,y),zy=>dn(ii(N(M(z,a)),nza=>{
              const zb=app(ue(app(ue(al(ob),y),yb),z),zy);
              const zc=into(cp,z,ai(zb,nza));
              return app(app(ue(ar(yp),z),zy),zc);
            }))));
            const ay=ui(x=>ii(M(x,a),xa=>{
              const ox=app(us(om,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),y),oy);
              return oe(cx,M(x,y),xy=>xy,rest=>oe(rest,M(x,y),eq=>fe(app(nya,eqSub(eq,z=>M(z,a),xa)),M(x,y)),yx=>fe(app(nya,app(ue(app(ue(al(oa),x),xa),y),yx)),M(x,y))));
            }));
            const eq=extEq(a,y,x=>ai(ii(M(x,a),xa=>app(ue(ay,x),xa)),ii(M(x,y),xy=>app(ue(ya,x),xy))));
            return ol(eqSub(sym(eq),z=>M(z,b),yb),target[2]);
          });
        });
      },none=>{
        const ba=ui(y=>ii(M(y,b),yb=>dn(ii(N(M(y,a)),nya=>app(none,ei(bad,y,ai(yb,nya)))))));
        const eq=extEq(a,b,x=>ai(ii(M(x,a),xa=>app(ue(ab,x),xa)),ii(M(x,b),xb=>app(ue(ba,x),xb))));
        return or(M(a,b),ol(eq,M(b,a)));
      });
    });
  }
  const compare=use(cmpInd,ind=>ui(a=>ii(Ord(a),oa=>{
    return open(ue(se,a),(d,sd)=>{
      const td=app(us(st,a,d),al(oa),sd),ad=into(sd,a,or(M(a,a),ref(a)));
      const step=ui(i=>ii(M(i,d),id=>ii(A(j=>I(M(j,i),cmpP(j))),ih=>ii(Ord(i),oi=>ui(b=>ii(Ord(b),ob=>comparisonStep(i,oi,ih,b,ob)))))));
      return app(app(ue(app(ue(ind,d),td,step),a),ad),oa);
    });
  })));
  const Appears=(x,a)=>C(Ord(a),E(r=>C(W(a,r),M(x,r))));
  const Rank=(x,a)=>C(Appears(x,a),A(i=>I(M(i,a),N(Appears(x,i)))));
  function unpackL(x,lx,fn){
    return open(lx,(a,ap)=>open(ar(ap),(d,dp)=>open(ar(dp),(f,fp)=>open(ar(fp),(r,rp)=>{
      const w=W(a,r),inner=replace(w[2],w[1],d)[2];
      const wp=ei(w,d,ai(al(dp),ei(inner,f,ai(al(fp),al(rp)))));
      const appear=ai(al(ap),ei(Appears(x,a)[2],r,ai(wp,ar(rp))));
      return fn(a,d,al(dp),appear);
    }))));
  }
  const leastRank=ui(x=>ii(L(x),lx=>unpackL(x,lx,(a,d,sd,ap)=>{
    const v=fresh(),spec={name:"separation",params:1,body:db(Appears(x,v),[v,x])};
    return open(us(ax(spec),x,d),(c,cp)=>{
      const ad=into(sd,a,or(M(a,a),ref(a)));
      const ac=into(cp,a,ai(ad,ap));
      const ne=ei(E(y=>M(y,c)),a,ac);
      const td=app(us(st,a,d),al(al(ap)),sd);
      return open(app(ue(ax({name:"foundation"}),c),ne),(b,bp)=>{
        const bv=from(cp,b,al(bp)),bd=al(bv),appear=ar(bv);
        const minimal=ui(i=>ii(M(i,b),ib=>ii(Appears(x,i),ia=>{
          const id=app(ue(app(ue(td,b),bd),i),ib),ic=into(cp,i,ai(id,ia));
          return app(app(ue(ar(bp),i),ib),ic);
        })));
        return ei(E(b=>Rank(x,b)),b,ai(appear,minimal));
      });
    });
  })));
  const rankUnique=use(compare,cmp0=>qs(3,(x,a,b)=>ii(Rank(x,a),ra=>ii(Rank(x,b),rb=>{
    const cc=app(ue(app(ue(cmp0,a),al(al(ra))),b),al(al(rb)));
    return oe(cc,Q(a,b),ab=>fe(app(app(ue(ar(rb),a),ab),al(ra)),Q(a,b)),rest=>oe(rest,Q(a,b),eq=>eq,ba=>fe(app(app(ue(ar(ra),b),ba),al(rb)),Q(a,b))));
  }))));
  const rankExistsUnique=use(leastRank,lr=>use(rankUnique,ru=>ui(x=>ii(L(x),lx=>{
    return open(app(ue(lr,x),lx),(a,ra)=>{
      const uq=ui(b=>ii(Rank(x,b),rb=>app(us(ru,x,b,a),rb,ra)));
      return ei(E(a=>C(Rank(x,a),A(b=>I(Rank(x,b),Q(b,a))))),a,ai(ra,uq));
    });
  }))));
  const proofs={ordinal_comparison_induction:cmpInd,ordinal_comparison:compare,least_constructible_rank:leastRank,least_rank_unique:rankUnique,least_rank_exists_unique:rankExistsUnique};
  return Object.fromEntries(Object.entries(proofs).map(([name,p])=>[name,{goal:db(p.goal,[]),proof:p.emit([],[])}]));
}
