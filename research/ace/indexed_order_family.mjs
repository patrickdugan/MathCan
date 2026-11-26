// ACE-03X. Convert an indexed coherent order history into a directed family.
import {kernel,same} from './zf_interface.mjs';
import {buildF} from './finite_witnesses.mjs';
import {buildE} from './hierarchy_closure.mjs';
import {canonicalLimitOrderFormulas,buildCanonicalLimitOrder} from './canonical_limit_order.mjs';
import {canonicalStageOrderFormulas,buildCanonicalStageOrder} from './canonical_stage_order.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`sc${serial++}`;
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],F=['F'];
  const I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q],N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh();return [op,x,fn(x)];};
  const A=fn=>bind('A',fn),E=fn=>bind('E',fn);
  function named(p,env) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,env[a],env[b]];
    if(op==='A'||op==='E'){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env=[]) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='='){
      const i=env.indexOf(a),j=env.indexOf(b);
      if(i<0||j<0)throw Error(`unbound ${a} ${b}`);
      return [op,i,j];
    }
    if(op==='A'||op==='E')return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }
  function replace(p,x,y) {
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,a===x?y:a,b===x?y:b];
    if(op==='A'||op==='E'){
      if(a===x)return p;
      if(a===y){const z=fresh();return [op,z,replace(replace(b,a,z),x,y)];}
      return [op,a,replace(b,x,y)];
    }
    return [op,replace(a,x,y),replace(b,x,y)];
  }
  const P=(goal,emit)=>({goal,emit});
  function assume(goal) {
    const id=fresh();return {id,p:P(goal,(_,h)=>{const i=h.indexOf(id);if(i<0)throw Error('unbound hypothesis');return ['h',i];})};
  }
  function ui(fn){const x=fresh(),p=fn(x);return P(['A',x,p.goal],(e,h)=>['uI',p.emit([x,...e],h)]);}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>['iI',db(g,e),p.emit(e,[...h,a.id])]);}
  const al=p=>P(p.goal[1],(e,h)=>['aL',p.emit(e,h)]),ar=p=>P(p.goal[2],(e,h)=>['aR',p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>['aI',p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>['iE',p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>['uE',p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p),app=(p,...qs)=>qs.reduce(ie,p);
  const ref=x=>P(Q(x,x),(e,h)=>['refl',e.indexOf(x)]);
  const dn=p=>P(p.goal[1][1],(e,h)=>['dne',p.emit(e,h)]);
  const fe=(p,g)=>P(g,(e,h)=>['fE',p.emit(e,h),db(g,e)]);
  function ei(g,x,p){return P(g,(e,h)=>['eI',db(g[2],[g[1],...e]),e.indexOf(x),p.emit(e,h)]);}
  function open(p,fn){
    if(p.goal[0]!=='E')throw Error('expected existential');
    const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
    return P(q.goal,(e,h)=>['eE',p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);
  }
  function oe(p,g,left,right){
    const a=assume(p.goal[1]),b=assume(p.goal[2]),l=left(a.p),r=right(b.p);
    return P(g,(e,h)=>['oE',p.emit(e,h),l.emit(e,[...h,a.id]),r.emit(e,[...h,b.id])]);
  }
  const ol=(p,g)=>P(O(p.goal,g),(e,h)=>['oL',p.emit(e,h),db(g,e)]);
  const or=(g,p)=>P(O(g,p.goal),(e,h)=>['oR',db(g,e),p.emit(e,h)]);
  function eqSub(eq,prop,p){const v=fresh(),g=prop(v);return P(replace(g,v,eq.goal[2]),(e,h)=>['eqS',db(g,[v,...e]),eq.emit(e,h),p.emit(e,h)]);}
  const sym=p=>eqSub(p,z=>Q(z,p.goal[1]),ref(p.goal[1]));
  const use=(p,fn)=>ie(ii(p.goal,fn),p);
  const ax=spec=>P(named(kernel(0,[],['axiom',spec],false,'ZF').goal,[]),()=>['axiom',spec]);
  function separation(a,params,predicate) {
    const x=fresh(),spec={name:'separation',params:params.length,body:db(predicate(x),[x,...params])};
    return us(ax(spec),...params.slice().reverse(),a);
  }
  const from=(p,x,px)=>app(al(ue(p,x)),px),into=(p,x,px)=>app(ar(ue(p,x)),px);
  function liftHyp(p,n){if(!Array.isArray(p))return p;if(p[0]==='h')return ['h',p[1]+n];return p.map(x=>liftHyp(x,n));}
  function imported(p){return P(named(p.goal,[]),(_,h)=>liftHyp(p.proof,h.length));}
  const form=(name,...args)=>named(defs[name],args);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const subset=(s,a)=>all(s,x=>M(x,a)),Trans=a=>all(a,x=>subset(x,a));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {fresh,M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ie,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled};
}

function indexedLanguage(defs) {
  const l=language(defs),{M,I,C,A,E,named,db,form,all,some,subset,Trans}=l;
  const lf=canonicalLimitOrderFormulas(defs),f=(key,...args)=>named(lf[key],args);
  const Val=(r,x,y)=>form('val',r,x,y),Pair=(p,a,r)=>form('pair',p,a,r);
  const Graph=(g,d)=>form('graph',g,d),Ord=d=>form('ordinal',d);
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const Range=(g,d,h)=>A(p=>iff(M(p,h),some(d,i=>Val(g,i,p))));
  const At=(g,i,a,r)=>E(p=>C(Val(g,i,p),Pair(p,a,r)));
  const W=(a,r)=>f('well_order',a,r),Restriction=(a,r,s)=>f('restriction',a,r,s),Initial=(a,b,s)=>f('initial',a,b,s);
  const Embed=(a,r,b,s)=>C(subset(a,b),C(Restriction(a,r,s),Initial(a,b,s)));
  const IndexedLocal=(g,d)=>A(i=>A(a=>A(r=>I(M(i,d),I(At(g,i,a,r),W(a,r))))));
  const IndexedTrans=(g,d)=>A(i=>A(a=>A(r=>I(M(i,d),I(At(g,i,a,r),Trans(a))))));
  const Forward=(g,d)=>A(i=>A(j=>A(a=>A(r=>A(b=>A(s=>I(M(i,d),I(M(j,d),I(At(g,i,a,r),
    I(At(g,j,b,s),I(M(i,j),Embed(a,r,b,s))))))))))));
  const Local=h=>f('local',h),LocalTrans=h=>f('local_transitive',h),Directed=h=>f('directed',h),Extends=h=>f('extends',h);
  const State=(h,b,t)=>f('state',h,b,t),AllExtensions=(h,b,t)=>f('all_extensions',h,b,t);
  const IndexedExtensions=(g,d,b,t)=>A(i=>A(a=>A(r=>I(M(i,d),I(At(g,i,a,r),Embed(a,r,b,t))))));
  const sf=canonicalStageOrderFormulas(defs),Good=p=>named(sf.good,[p]),PackedEmbed=(p,q)=>named(sf.embed,[p,q]);
  const Pointwise=(g,d)=>all(d,i=>A(p=>I(Val(g,i,p),Good(p))));
  const PackedForward=(g,d)=>all(d,i=>all(d,j=>I(M(i,j),A(p=>A(q=>I(Val(g,i,p),I(Val(g,j,q),PackedEmbed(p,q))))))));
  const Prior=(g,d,q)=>all(d,i=>A(p=>I(Val(g,i,p),PackedEmbed(p,q))));
  const Value=(h,p)=>f('value',h,p);
  const formulas={
    prefix_range:db(Range('f','d','h'),['f','d','h']),at:db(At('f','i','a','r'),['f','i','a','r']),
    embedding:db(Embed('a','r','b','s'),['a','r','b','s']),
    indexed_local:db(IndexedLocal('f','d'),['f','d']),indexed_transitive:db(IndexedTrans('f','d'),['f','d']),
    forward:db(Forward('f','d'),['f','d']),indexed_extensions:db(IndexedExtensions('f','d','b','t'),['f','d','b','t']),
    local:lf.local,local_transitive:lf.local_transitive,directed:lf.directed,extends:lf.extends,
    limit_state:lf.state,all_extensions:lf.all_extensions,well_order:lf.well_order,transitive:lf.transitive,
    good:sf.good,packed_embed:sf.embed,packed_pointwise:db(Pointwise('f','d'),['f','d']),
    packed_forward:db(PackedForward('f','d'),['f','d']),packed_prior:db(Prior('f','d','q'),['f','d','q']),limit_value:lf.value
  };
  return {...l,Val,Pair,Graph,Ord,Range,At,W,Restriction,Initial,Embed,IndexedLocal,IndexedTrans,Forward,Local,LocalTrans,Directed,Extends,
    State,AllExtensions,IndexedExtensions,Good,PackedEmbed,Pointwise,PackedForward,Prior,Value,formulas};
}

function indexedOrderFamilyFormulas(defs) {return indexedLanguage(defs).formulas;}

function buildIndexedOrderFamily(defs) {
  const {M,Q,F,I,C,O,N,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,Succ,subset,Trans,qs,compiled,
    Val,Pair,Graph,Ord,Range,At,W,Restriction,Initial,Embed,IndexedLocal,IndexedTrans,Forward,Local,LocalTrans,Directed,Extends,
    State,AllExtensions,IndexedExtensions,Good,PackedEmbed,Pointwise,PackedForward,Prior,Value,formulas}=indexedLanguage(defs);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);return proofs[id];};
  const finite=buildF(defs),prior=buildE(defs,true),injective=imported(finite.pair_injective);
  const inner=(g,x)=>replace(g[2],g[1],x),chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inner(goal,xs[0]),xs.slice(1),p));
  const identitySubset=a=>ui(x=>ii(M(x,a),p=>p));
  function at(g,i,a,r,p,value,pair){return ei(At(g,i,a,r),p,ai(value,pair));}
  function openStage(g,d,h,range,a,r,stage,fn){
    return open(stage,(p,pp)=>open(from(range,p,al(pp)),(i,ip)=>fn(i,al(ip),at(g,i,a,r,p,ar(ip),ar(pp)))));
  }
  function familyValue(g,d,h,range,i,a,r,id,atProof){
    return open(atProof,(p,pp)=>{
      const hit=E(j=>C(M(j,d),Val(g,j,p)));
      const ph=into(range,p,ei(hit,i,ai(id,al(pp))));
      return ei(Val(h,a,r),p,ai(ph,ar(pp)));
    });
  }

  save('indexed_ordinal_member',qs(2,(d,i)=>ii(Ord(d),od=>ii(M(i,d),id=>{
    const ti=app(ue(ar(od),i),id);
    const members=ui(j=>ii(M(j,i),ji=>app(ue(ar(od),j),app(ue(app(ue(al(od),i),id),j),ji))));
    return ai(ti,members);
  }))));

  // This is the ordinal-comparison proof used by constructible_power, rebuilt
  // locally so the adapter need not construct unrelated stage/rank proof trees.
  const em=p=>dn(ii(N(O(p,N(p))),h=>app(h,or(p,ii(p,hp=>app(h,ol(hp,N(p))))))));
  const extEq=(a,b,fn)=>app(us(ax({name:'extensionality'}),a,b),ui(fn));
  function successorExists(a,fn) {
    return open(us(ax({name:'pairing'}),a,a),(singleton,ss)=>
      open(us(ax({name:'pairing'}),a,singleton),(pair,ps)=>open(ue(ax({name:'union'}),pair),(d,union)=>{
        const memberA=into(ps,a,ol(ref(a),Q(a,singleton))),memberS=into(ps,singleton,or(Q(singleton,a),ref(singleton)));
        const exact=ui(x=>ai(
          ii(M(x,d),xd=>open(from(union,x,xd),(y,yp)=>oe(from(ps,y,al(yp)),O(M(x,a),Q(x,a)),
            ya=>ol(eqSub(ya,z=>M(x,z),ar(yp)),Q(x,a)),
            ys=>or(M(x,a),oe(from(ss,x,eqSub(ys,z=>M(x,z),ar(yp))),Q(x,a),p=>p,p=>p))))),
          ii(O(M(x,a),Q(x,a)),hit=>oe(hit,M(x,d),
            xa=>into(union,x,ei(E(y=>C(M(y,pair),M(x,y))),a,ai(memberA,xa))),
            equal=>into(union,x,ei(E(y=>C(M(y,pair),M(x,y))),singleton,ai(memberS,into(ss,x,ol(equal,Q(x,a))))))))
        ));
        return use(exact,succ=>fn(d,succ));
      }))
    );
  }
  const cmp=(a,b)=>O(M(a,b),O(Q(a,b),M(b,a))),cmpP=a=>I(Ord(a),A(b=>I(Ord(b),cmp(a,b))));
  const comparisonInduction=ui(d=>ii(Trans(d),td=>ii(A(y=>I(M(y,d),I(A(z=>I(M(z,y),cmpP(z))),cmpP(y)))),step=>ui(x=>ii(M(x,d),xd=>
    dn(ii(N(cmpP(x)),nx=>{
      const q='comparison_separation_x',sep=ue(ax({name:'separation',params:0,body:db(N(cmpP(q)),[q])}),d);
      return open(sep,(bad,exact)=>{
        const xb=into(exact,x,ai(xd,nx));
        return open(app(ue(ax({name:'foundation'}),bad),ei(E(y=>M(y,bad)),x,xb)),(y,yp)=>{
          const member=from(exact,y,al(yp)),yd=al(member),ny=ar(member);
          const ih=ui(z=>ii(M(z,y),zy=>dn(ii(N(cmpP(z)),nz=>{
            const zd=app(ue(app(ue(td,y),yd),z),zy),zb=into(exact,z,ai(zd,nz));
            return app(app(ue(ar(yp),z),zy),zb);
          }))));
          return app(ny,app(app(ue(step,y),yd),ih));
        });
      });
    }))
  )))));
  function comparisonStep(a,oa,ih,b,ob) {
    const target=cmp(a,b),member=imported(proofs.indexed_ordinal_member);
    return oe(em(M(b,a)),target,ba=>or(M(a,b),or(Q(a,b),ba)),nba=>{
      const ab=ui(x=>ii(M(x,a),xa=>{
        const ox=app(us(member,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),b),ob);
        return oe(cx,M(x,b),xb=>xb,rest=>oe(rest,M(x,b),
          eq=>fe(app(nba,eqSub(eq,z=>M(z,a),xa)),M(x,b)),
          bx=>fe(app(nba,app(ue(app(ue(al(oa),x),xa),b),bx)),M(x,b))));
      }));
      const bad=E(y=>C(M(y,b),N(M(y,a))));
      return oe(em(bad),target,hit=>{
        const q='comparison_bad_x',spec={name:'separation',params:1,body:db(N(M(q,a)),[q,a])};
        return open(us(ax(spec),a,b),(c,cp)=>{
          const ne=open(hit,(y,yp)=>ei(E(x=>M(x,c)),y,into(cp,y,yp)));
          return open(app(ue(ax({name:'foundation'}),c),ne),(y,yp)=>{
            const bc=from(cp,y,al(yp)),yb=al(bc),nya=ar(bc),oy=app(us(member,b,y),ob,yb);
            const ya=ui(z=>ii(M(z,y),zy=>dn(ii(N(M(z,a)),nza=>{
              const zb=app(ue(app(ue(al(ob),y),yb),z),zy),zc=into(cp,z,ai(zb,nza));
              return app(app(ue(ar(yp),z),zy),zc);
            }))));
            const ay=ui(x=>ii(M(x,a),xa=>{
              const ox=app(us(member,a,x),oa,xa),cx=app(ue(app(app(ue(ih,x),xa),ox),y),oy);
              return oe(cx,M(x,y),xy=>xy,rest=>oe(rest,M(x,y),
                eq=>fe(app(nya,eqSub(eq,z=>M(z,a),xa)),M(x,y)),
                yx=>fe(app(nya,app(ue(app(ue(al(oa),x),xa),y),yx)),M(x,y))));
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
  save('indexed_ordinal_comparison',use(comparisonInduction,ind=>ui(a=>ii(Ord(a),oa=>successorExists(a,(d,succ)=>{
    const td=app(us(imported(prior.ordinal_successor_transitivity),a,d),al(oa),succ),ad=into(succ,a,or(M(a,a),ref(a)));
    const step=ui(i=>ii(M(i,d),id=>ii(A(j=>I(M(j,i),cmpP(j))),ih=>ii(Ord(i),oi=>ui(b=>ii(Ord(b),ob=>comparisonStep(i,oi,ih,b,ob)))))));
    return app(app(ue(app(ue(ind,d),td,step),a),ad),oa);
  })))));
  const comparison=imported(proofs.indexed_ordinal_comparison);

  save('indexed_coordinates_unique',qs(7,(g,d,i,a,r,b,s)=>ii(Graph(g,d),graph=>ii(M(i,d),id=>
    ii(At(g,i,a,r),first=>ii(At(g,i,b,s),second=>
      open(first,(p,pp)=>open(second,(q,qp)=>open(app(ue(ar(graph),i),id),(v,vp)=>{
        const pq=chain(app(ue(ar(vp),p),al(pp)),sym(app(ue(ar(vp),q),al(qp))));
        return app(us(injective,q,a,r,b,s),eqSub(pq,z=>Pair(z,a,r),ar(pp)),ar(qp));
      })))
    ))
  ))));

  save('indexed_family_local',qs(3,(g,d,h)=>ii(Range(g,d,h),range=>ii(IndexedLocal(g,d),local=>
    qs(2,(a,r)=>ii(Val(h,a,r),stage=>openStage(g,d,h,range,a,r,stage,(i,id,atProof)=>
      app(us(local,i,a,r),id,atProof)
    )))
  ))));
  save('indexed_family_transitive',qs(3,(g,d,h)=>ii(Range(g,d,h),range=>ii(IndexedTrans(g,d),local=>
    qs(2,(a,r)=>ii(Val(h,a,r),stage=>openStage(g,d,h,range,a,r,stage,(i,id,atProof)=>
      app(us(local,i,a,r),id,atProof)
    )))
  ))));

  function compareIndices(d,i,j,od,id,jd,fn) {
    const oi=app(us(imported(proofs.indexed_ordinal_member),d,i),od,id),oj=app(us(imported(proofs.indexed_ordinal_member),d,j),od,jd);
    return fn(app(ue(app(ue(comparison,i),oi),j),oj));
  }
  function forwardStep(forward,g,d,i,j,a,r,b,s,id,jd,ia,jb,ij) {
    return app(us(forward,i,j,a,r,b,s),id,jd,ia,jb,ij);
  }
  save('indexed_family_directed',qs(3,(g,d,h)=>ii(Ord(d),od=>ii(Graph(g,d),graph=>ii(Range(g,d,h),range=>ii(Forward(g,d),forward=>
    qs(4,(a,r,b,s)=>ii(Val(h,a,r),ha=>ii(Val(h,b,s),hb=>
      openStage(g,d,h,range,a,r,ha,(i,id,ia)=>openStage(g,d,h,range,b,s,hb,(j,jd,jb)=>{
        const goal=E(c=>E(t=>C(Val(h,c,t),C(subset(a,c),subset(b,c)))));
        function choose(c,t,stage,ac,bc){return ei(goal,c,ei(inner(goal,c),t,ai(stage,ai(ac,bc))));}
        return compareIndices(d,i,j,od,id,jd,cmp=>oe(cmp,goal,
          ij=>choose(b,s,hb,al(forwardStep(forward,g,d,i,j,a,r,b,s,id,jd,ia,jb,ij)),identitySubset(b)),
          rest=>oe(rest,goal,
            equal=>{
              const atI=eqSub(sym(equal),x=>At(g,x,b,s),jb);
              const coords=app(us(imported(proofs.indexed_coordinates_unique),g,d,i,a,r,b,s),graph,id,ia,atI);
              const ab=ui(x=>ii(M(x,a),xa=>eqSub(al(coords),z=>M(x,z),xa)));
              return choose(b,s,hb,ab,identitySubset(b));
            },
            ji=>choose(a,r,ha,identitySubset(a),al(forwardStep(forward,g,d,j,i,b,s,a,r,jd,id,jb,ia,ji))))
        ));
      }))
    )))
  ))))));

  save('indexed_family_extends',qs(3,(g,d,h)=>ii(Ord(d),od=>ii(Graph(g,d),graph=>ii(Range(g,d,h),range=>ii(Forward(g,d),forward=>
    qs(4,(a,r,b,s)=>ii(Val(h,a,r),ha=>ii(Val(h,b,s),hb=>ii(subset(a,b),ab=>
      openStage(g,d,h,range,a,r,ha,(i,id,ia)=>openStage(g,d,h,range,b,s,hb,(j,jd,jb)=>{
        const goal=C(Restriction(a,r,s),Initial(a,b,s));
        return compareIndices(d,i,j,od,id,jd,cmp=>oe(cmp,goal,
          ij=>ar(forwardStep(forward,g,d,i,j,a,r,b,s,id,jd,ia,jb,ij)),
          rest=>oe(rest,goal,
            equal=>{
              const atI=eqSub(sym(equal),x=>At(g,x,b,s),jb);
              return use(app(us(imported(proofs.indexed_coordinates_unique),g,d,i,a,r,b,s),graph,id,ia,atI),coords=>{
                const restriction=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>ai(
                  ii(Val(s,x,y),xy=>eqSub(sym(ar(coords)),z=>Val(z,x,y),xy)),
                  ii(Val(r,x,y),xy=>eqSub(ar(coords),z=>Val(z,x,y),xy))
                ))));
                const initial=ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,b),yb=>ii(Val(s,y,x),yx=>eqSub(sym(al(coords)),z=>M(y,z),yb))))));
                return ai(restriction,initial);
              });
            },
            ji=>use(forwardStep(forward,g,d,j,i,b,s,a,r,jd,id,jb,ia,ji),back=>{
              const restriction=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
                const equivalence=app(us(al(ar(back)),x,y),app(ue(ab,x),xa),app(ue(ab,y),ya));
                return ai(ar(equivalence),al(equivalence));
              })));
              const initial=ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,b),yb=>ii(Val(s,y,x),yx=>app(ue(al(back),y),yb))))));
              return ai(restriction,initial);
            }))
        ));
      }))
    ))))
  ))))));

  save('indexed_family_extensions',qs(5,(g,d,h,b,t)=>ii(Range(g,d,h),range=>ii(AllExtensions(h,b,t),extensions=>
    qs(3,(i,a,r)=>ii(M(i,d),id=>ii(At(g,i,a,r),atProof=>
      app(us(extensions,a,r),familyValue(g,d,h,range,i,a,r,id,atProof))
    )))
  ))));

  const stage=buildCanonicalStageOrder(defs,'relations');
  for(const [a,b] of [['well_order','well_order'],['embedding','extension'],['good','good'],['packed_embed','embed']])
    if(!same(formulas[a],stage.formulas[b]))throw Error('indexed packed stage interface '+a);
  save('packed_indexed_local',qs(2,(g,d)=>ii(Pointwise(g,d),pointwise=>
    qs(3,(i,a,r)=>ii(M(i,d),id=>ii(At(g,i,a,r),atProof=>open(atProof,(p,pp)=>
      ar(app(us(imported(stage.proofs.good_coordinates),p,a,r),app(ue(app(ue(pointwise,i),id),p),al(pp)),ar(pp)))
    ))))
  )));
  save('packed_indexed_transitive',qs(2,(g,d)=>ii(Pointwise(g,d),pointwise=>
    qs(3,(i,a,r)=>ii(M(i,d),id=>ii(At(g,i,a,r),atProof=>open(atProof,(p,pp)=>
      al(app(us(imported(stage.proofs.good_coordinates),p,a,r),app(ue(app(ue(pointwise,i),id),p),al(pp)),ar(pp)))
    ))))
  )));
  save('packed_indexed_forward',qs(2,(g,d)=>ii(PackedForward(g,d),forward=>
    qs(6,(i,j,a,r,b,s)=>ii(M(i,d),id=>ii(M(j,d),jd=>ii(At(g,i,a,r),ia=>ii(At(g,j,b,s),jb=>ii(M(i,j),ij=>
      open(ia,(p,pp)=>open(jb,(q,qp)=>{
        const embedded=app(us(app(ue(app(ue(forward,i),id),j),jd,ij),p,q),al(pp),al(qp));
        return app(us(imported(stage.proofs.embed_coordinates),p,q,a,r,b,s),embedded,ar(pp),ar(qp));
      }))
    ))))))
  )));

  const limit=buildCanonicalLimitOrder(defs);
  save('indexed_canonical_limit_complete',qs(3,(g,d,h)=>ii(Ord(d),od=>ii(Graph(g,d),graph=>ii(Range(g,d,h),range=>
    ii(IndexedLocal(g,d),local=>ii(IndexedTrans(g,d),trans=>ii(Forward(g,d),forward=>{
      const localH=app(us(imported(proofs.indexed_family_local),g,d,h),range,local);
      const transH=app(us(imported(proofs.indexed_family_transitive),g,d,h),range,trans);
      const directed=app(us(imported(proofs.indexed_family_directed),g,d,h),od,graph,range,forward);
      const extendsH=app(us(imported(proofs.indexed_family_extends),g,d,h),od,graph,range,forward);
      return open(app(ue(imported(limit.proofs.canonical_limit_complete),h),localH,directed,extendsH),(b,bp)=>open(bp,(t,tp)=>{
        const state=al(tp),order=al(ar(tp)),extensions=ar(ar(tp));
        const tb=app(us(imported(limit.proofs.union_carrier_transitive),h,b),al(state),transH);
        const indexed=app(us(imported(proofs.indexed_family_extensions),g,d,h,b,t),range,extensions);
        const goal=E(b=>E(t=>C(State(h,b,t),C(C(Trans(b),W(b,t)),IndexedExtensions(g,d,b,t)))));
        return ei(goal,b,ei(inner(goal,b),t,ai(state,ai(ai(tb,order),indexed))));
      }));
    })))
  )))));

  save('packed_indexed_limit_properties',qs(4,(g,d,h,p)=>ii(Ord(d),od=>ii(Graph(g,d),graph=>ii(Range(g,d,h),range=>
    ii(Pointwise(g,d),pointwise=>ii(PackedForward(g,d),forward=>ii(Value(h,p),value=>{
      const local=app(us(imported(proofs.packed_indexed_local),g,d),pointwise);
      const trans=app(us(imported(proofs.packed_indexed_transitive),g,d),pointwise);
      return use(app(us(imported(proofs.packed_indexed_forward),g,d),forward),componentForward=>{
        const localH=app(us(imported(proofs.indexed_family_local),g,d,h),range,local);
        const transH=app(us(imported(proofs.indexed_family_transitive),g,d,h),range,trans);
        const directed=app(us(imported(proofs.indexed_family_directed),g,d,h),od,graph,range,componentForward);
        const extension=app(us(imported(proofs.indexed_family_extends),g,d,h),od,graph,range,componentForward);
        return use(directed,dh=>use(extension,eh=>open(value,(b,bp)=>open(bp,(t,tp)=>{
          const pair=al(tp),state=ar(tp);
          const transB=app(us(imported(limit.proofs.union_carrier_transitive),h,b),al(state),transH);
          const order=app(us(imported(limit.proofs.limit_state_well_order),h,b,t),localH,dh,eh,state);
          const good=pack(Good(p),[b,t],ai(pair,ai(transB,order)));
          return use(app(us(imported(limit.proofs.limit_state_extensions),h,b,t),dh,eh,state),allExtensions=>{
            const prior=ui(i=>ii(M(i,d),id=>ui(q=>ii(Val(g,i,q),iq=>{
              const goodQ=app(ue(app(ue(pointwise,i),id),q),iq);
              return open(goodQ,(a,ap)=>open(ap,(r,rp)=>{
                const qpair=al(rp),atProof=at(g,i,a,r,q,iq,qpair);
                const hp=familyValue(g,d,h,range,i,a,r,id,atProof);
                const embedded=app(us(allExtensions,a,r),hp);
                return pack(PackedEmbed(q,p),[a,r,b,t],ai(ai(qpair,pair),embedded));
              }));
            }))));
            return ai(good,prior);
          });
        }))));
      });
    })))
  )))));

  save('packed_indexed_limit_complete',qs(3,(g,d,h)=>ii(Ord(d),od=>ii(Graph(g,d),graph=>ii(Range(g,d,h),range=>
    ii(Pointwise(g,d),pointwise=>ii(PackedForward(g,d),forward=>
      open(ue(imported(limit.proofs.packed_limit_value_exists),h),(p,value)=>{
        const properties=app(us(imported(proofs.packed_indexed_limit_properties),g,d,h,p),od,graph,range,pointwise,forward,value);
        return ei(E(p=>C(Value(h,p),C(Good(p),Prior(g,d,p)))),p,ai(value,properties));
      })
    ))
  )))));
  return {formulas,proofs};
}

export {indexedOrderFamilyFormulas,buildIndexedOrderFamily};

