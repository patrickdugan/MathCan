// ACE-03X. Project packed canonical order histories to the pinned L hierarchy.
// Replacement constructs the exact graph of carriers from a functional history.
import {kernel} from './zf_interface.mjs';
import {buildF} from './finite_witnesses.mjs';
import {buildE} from './hierarchy_closure.mjs';
import {canonicalStageOrderFormulas} from './canonical_stage_order.mjs';
import {canonicalLimitOrderFormulas} from './canonical_limit_order.mjs';
import {constructibleOrderHistoryFormulas} from './constructible_order_history.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`t${serial++}`;
  const M=(a,b)=>['M',a,b], Q=(a,b)=>['=',a,b], F=['F'];
  const I=(p,q)=>['>',p,q], C=(p,q)=>['&',p,q], O=(p,q)=>['|',p,q], N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh(); return [op,x,fn(x)];};
  const A=fn=>bind('A',fn), E=fn=>bind('E',fn);
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
    const id=fresh();
    return {id,p:P(goal,(_,h)=>{const i=h.indexOf(id);if(i<0)throw Error('unbound hypothesis');return ['h',i];})};
  }
  function ui(fn){const x=fresh(),p=fn(x);return P(['A',x,p.goal],(e,h)=>['uI',p.emit([x,...e],h)]);}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>['iI',db(g,e),p.emit(e,[...h,a.id])]);}
  const al=p=>P(p.goal[1],(e,h)=>['aL',p.emit(e,h)]);
  const ar=p=>P(p.goal[2],(e,h)=>['aR',p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>['aI',p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>['iE',p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>['uE',p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p), app=(p,...qs)=>qs.reduce(ie,p);
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
  const from=(p,x,px)=>app(al(ue(p,x)),px);
  const into=(p,x,px)=>app(ar(ue(p,x)),px);
  function liftHyp(p,n){if(!Array.isArray(p))return p;if(p[0]==='h')return ['h',p[1]+n];return p.map(x=>liftHyp(x,n));}
  function imported(p){return P(named(p.goal,[]),(_,h)=>liftHyp(p.proof,h.length));}


  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,all,some,qs,compiled};
}

function projectionLanguage(defs) {
  const L=language(defs),{M,Q,I,C,O,N,A,E,named,db,all,some}=L;
  const hf=constructibleOrderHistoryFormulas(defs),sf=canonicalStageOrderFormulas(defs),lf=canonicalLimitOrderFormulas(defs);
  const Val=(f,i,a)=>named(defs.val,[f,i,a]),Pair=(p,a,r)=>named(defs.pair,[p,a,r]);
  const Graph=(f,d)=>named(defs.graph,[f,d]),Ord=d=>named(defs.ordinal,[d]);
  const Def=(a,b)=>named(defs.Def,[a,b]),Succ=(a,b)=>named(defs.successor,[a,b]);
  const PinnedStage=(g,i,a)=>named(defs.stage,[g,i,a]),PinnedHistory=(g,d)=>named(defs.stageGraph,[g,d]);
  const Hist=(f,d)=>named(hf.history,[f,d]),Step=(f,i,p)=>named(hf.step,[f,i,p]),Range=(f,i,h)=>named(hf.range,[f,i,h]);
  const Good=p=>named(sf.good,[p]),W=(a,r)=>named(sf.well_order,[a,r]);
  const UnionCarrier=(h,a)=>named(lf.union_carrier,[h,a]);
  const Sub=(a,b)=>all(a,x=>M(x,b)),Trans=a=>all(a,x=>Sub(x,a)),iff=(p,q)=>C(I(p,q),I(q,p));
  const Carrier=(f,i,a)=>E(p=>E(r=>C(Val(f,i,p),Pair(p,a,r))));
  const Packed=(f,d)=>all(d,i=>A(p=>I(Val(f,i,p),E(a=>E(r=>Pair(p,a,r))))));
  const ProjectedPair=(q,f,i)=>E(a=>C(Carrier(f,i,a),Pair(q,i,a)));
  const Exact=(f,d,g)=>A(q=>iff(M(q,g),some(d,i=>ProjectedPair(q,f,i))));
  const Agreement=(f,d,g)=>all(d,i=>A(a=>iff(Val(g,i,a),Carrier(f,i,a))));
  const Pointwise=(f,d)=>all(d,i=>A(p=>I(Val(f,i,p),Good(p))));
  const LimitStage=(g,i,a)=>A(x=>iff(M(x,a),some(i,j=>E(b=>C(Val(g,j,b),M(x,b))))));
  const Complete=(f,d,g)=>C(C(Graph(g,d),Agreement(f,d,g)),PinnedHistory(g,d));
  const GoodCarriers=(g,d)=>all(d,i=>A(a=>I(Val(g,i,a),E(r=>C(Trans(a),W(a,r))))));
  const forms={
    carrier:db(Carrier('f','i','a'),['f','i','a']),packed_values:db(Packed('f','d'),['f','d']),
    projected_pair:db(ProjectedPair('q','f','i'),['q','f','i']),exact_projection:db(Exact('f','d','g'),['f','d','g']),
    carrier_agreement:db(Agreement('f','d','g'),['f','d','g']),pointwise:db(Pointwise('f','d'),['f','d']),
    limit_stage:db(LimitStage('g','i','a'),['g','i','a']),complete:db(Complete('f','d','g'),['f','d','g']),
    good_carriers:db(GoodCarriers('g','d'),['g','d']),history:hf.history,step:hf.step,range:hf.range,
    pinned_stage:defs.stage,pinned_stage_graph:defs.stageGraph,transitive:db(Trans('a'),['a']),well_order:sf.well_order
  };
  return {...L,Val,Pair,Graph,Ord,Def,Succ,PinnedStage,PinnedHistory,Hist,Step,Range,Good,W,UnionCarrier,Sub,Trans,iff,
    Carrier,Packed,ProjectedPair,Exact,Agreement,Pointwise,LimitStage,Complete,GoodCarriers,forms};
}

function carrierHistoryProjectionFormulas(defs) {return projectionLanguage(defs).forms;}

function buildCarrierHistoryProjection(defs) {
  const {M,Q,F,I,C,O,N,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,all,some,qs,compiled,
    Val,Pair,Graph,Ord,Def,Succ,PinnedStage,PinnedHistory,Hist,Step,Range,Good,W,UnionCarrier,Sub,Trans,
    Carrier,Packed,ProjectedPair,Exact,Agreement,Pointwise,LimitStage,Complete,GoodCarriers,forms}=projectionLanguage(defs);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);return proofs[id];};
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inside(goal,xs[0]),xs.slice(1),p));
  const finite=buildF(defs),earlier=buildE(defs,true);
  const pairExists=imported(finite.pair_exists),pairInjective=imported(finite.pair_injective),pairUnique=imported(earlier.ordered_pair_unique);
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  function valUnique(graph,i,id,p,q,pi,qi) {
    return open(app(ue(ar(graph),i),id),(v,vp)=>chain(app(ue(ar(vp),p),pi),sym(app(ue(ar(vp),q),qi))));
  }
  function carrierIn(f,i,a,p,r,value,pair) {return pack(Carrier(f,i,a),[p,r],ai(value,pair));}
  function openCarrier(p,fn) {return open(p,(v,vp)=>open(vp,(r,rp)=>fn(v,r,al(rp),ar(rp))));}
  function projectedIn(q,f,i,a,carrier,pair) {return ei(ProjectedPair(q,f,i),a,ai(carrier,pair));}
  function agreed(agreement,i,id,a){return ue(app(ue(agreement,i),id),a);}
  function priorIndex(trans,d,i,id,j,ji){return app(ue(app(ue(trans,i),id),j),ji);}

  save('carrier_value_unique',use(pairInjective,inj=>qs(5,(f,d,i,a,b)=>ii(Graph(f,d),graph=>ii(M(i,d),id=>
    ii(Carrier(f,i,a),ca=>ii(Carrier(f,i,b),cb=>openCarrier(ca,(p,r,pi,pa)=>openCarrier(cb,(q,s,qi,qb)=>{
      const pq=valUnique(graph,i,id,p,q,pi,qi);
      const atP=eqSub(sym(pq),z=>Pair(z,b,s),qb);
      return al(app(us(inj,p,a,r,b,s),pa,atP));
    }))))
  )))));
  save('carrier_value_total',qs(2,(f,d)=>ii(Graph(f,d),graph=>ii(Packed(f,d),packed=>
    ui(i=>ii(M(i,d),id=>open(app(ue(ar(graph),i),id),(p,pv)=>
      open(app(ue(app(ue(packed,i),id),p),al(pv)),(a,ap)=>open(ap,(r,pr)=>
        ei(E(a=>Carrier(f,i,a)),a,carrierIn(f,i,a,p,r,al(pv),pr))
      ))
    )))
  ))));
  save('projected_pair_total_unique',use(pairExists,pex=>use(pairUnique,pu=>use(imported(proofs.carrier_value_unique),cu=>
    use(imported(proofs.carrier_value_total),ct=>qs(2,(f,d)=>ii(Graph(f,d),graph=>ii(Packed(f,d),packed=>
      ui(i=>ii(M(i,d),id=>open(app(ue(app(us(ct,f,d),graph,packed),i),id),(a,ca)=>
        open(us(pex,i,a),(q,pair)=>{
          const unique=ui(z=>ii(ProjectedPair(z,f,i),zp=>open(zp,(b,bp)=>{
            const ba=app(us(cu,f,d,i,b,a),graph,id,al(bp),ca);
            const atA=eqSub(ba,x=>Pair(z,i,x),ar(bp));
            return app(us(pu,i,a,z,q),atA,pair);
          })));
          return ei(E(q=>C(ProjectedPair(q,f,i),A(z=>I(ProjectedPair(z,f,i),Q(z,q))))),q,
            ai(projectedIn(q,f,i,a,ca,pair),unique));
        })
      )))
    ))))
  ))));
  const q0='projection_value',i0='projection_index',f0='projection_history';
  const replacement={name:'replacement',params:1,body:db(ProjectedPair(q0,f0,i0),[q0,i0,f0])};
  save('exact_projection_exists',use(imported(proofs.projected_pair_total_unique),total=>qs(2,(f,d)=>
    ii(Graph(f,d),graph=>ii(Packed(f,d),packed=>app(us(ax(replacement),f,d),app(us(total,f,d),graph,packed))))
  )));
  save('exact_projection_unique',qs(4,(f,d,g,h)=>ii(Exact(f,d,g),fg=>ii(Exact(f,d,h),fh=>
    app(us(ax({name:'extensionality'}),g,h),ui(q=>ai(
      ii(M(q,g),qg=>into(fh,q,from(fg,q,qg))),ii(M(q,h),qh=>into(fg,q,from(fh,q,qh)))
    )))
  ))));
  save('exact_projection_agreement',use(pairExists,pex=>use(pairInjective,inj=>qs(3,(f,d,g)=>ii(Exact(f,d,g),exact=>
    ui(i=>ii(M(i,d),id=>ui(a=>ai(
      ii(Val(g,i,a),value=>open(value,(q,qv)=>open(from(exact,q,al(qv)),(j,jp)=>open(ar(jp),(b,bp)=>{
        const equal=app(us(inj,q,i,a,j,b),ar(qv),ar(bp));
        const atI=eqSub(sym(al(equal)),x=>Carrier(f,x,b),al(bp));
        return eqSub(sym(ar(equal)),x=>Carrier(f,i,x),atI);
      })))),
      ii(Carrier(f,i,a),carrier=>open(us(pex,i,a),(q,pair)=>{
        const hit=some(d,j=>ProjectedPair(q,f,j));
        const qg=into(exact,q,ei(hit,i,ai(id,projectedIn(q,f,i,a,carrier,pair))));
        return ei(Val(g,i,a),q,ai(qg,pair));
      }))
    ))))
  )))));
  save('exact_projection_graph',use(imported(proofs.carrier_value_total),ct=>use(imported(proofs.carrier_value_unique),cu=>
    use(imported(proofs.exact_projection_agreement),agree=>qs(3,(f,d,g)=>ii(Graph(f,d),graph=>ii(Packed(f,d),packed=>ii(Exact(f,d,g),exact=>{
      const shape=ui(q=>ii(M(q,g),qg=>open(from(exact,q,qg),(i,ip)=>open(ar(ip),(a,ap)=>{
        const goal=some(d,i=>E(a=>Pair(q,i,a)));
        return ei(goal,i,ai(al(ip),ei(inside(goal,i)[2],a,ar(ap))));
      }))));
      const ag=app(us(agree,f,d,g),exact);
      const total=ui(i=>ii(M(i,d),id=>open(app(ue(app(us(ct,f,d),graph,packed),i),id),(a,ca)=>{
        const value=app(ar(agreed(ag,i,id,a)),ca);
        const unique=ui(b=>ii(Val(g,i,b),vb=>app(us(cu,f,d,i,b,a),graph,id,app(al(agreed(ag,i,id,b)),vb),ca)));
        return ei(E(a=>C(Val(g,i,a),A(b=>I(Val(g,i,b),Q(b,a))))),a,ai(value,unique));
      })));
      return ai(shape,total);
    }))))
  ))));

  save('history_values_are_good',qs(2,(f,d)=>ii(Hist(f,d),history=>
    ui(i=>ii(M(i,d),id=>ui(p=>ii(Val(f,i,p),pi=>
      open(app(ue(ar(history),i),id),(q,qp)=>{
        const pq=valUnique(al(history),i,id,p,q,pi,al(qp));
        return eqSub(sym(pq),Good,al(ar(qp)));
      })
    ))))
  )));
  save('history_values_are_packed',use(imported(proofs.history_values_are_good),good=>qs(2,(f,d)=>ii(Hist(f,d),history=>
    ui(i=>ii(M(i,d),id=>ui(p=>ii(Val(f,i,p),pi=>
      open(app(ue(app(ue(app(us(good,f,d),history),i),id),p),pi),(a,ap)=>open(ap,(r,rp)=>
        pack(E(a=>E(r=>Pair(p,a,r))),[a,r],al(rp))
      ))
    ))))
  ))));

  save('limit_carrier_projects',qs(6,(f,d,g,i,h,a)=>ii(Trans(d),td=>ii(Agreement(f,d,g),agreement=>ii(M(i,d),id=>
    ii(Range(f,i,h),range=>ii(UnionCarrier(h,a),union=>ui(x=>ai(
      ii(M(x,a),xa=>open(from(union,x,xa),(b,bp)=>open(bp,(r,rp)=>
        open(al(rp),(p,pp)=>open(from(range,p,al(pp)),(j,jp)=>{
          const jd=priorIndex(td,d,i,id,j,al(jp));
          const val=app(ar(agreed(agreement,j,jd,b)),carrierIn(f,j,b,p,r,ar(jp),ar(pp)));
          const goal=some(i,j=>E(b=>C(Val(g,j,b),M(x,b))));
          return ei(goal,j,ai(al(jp),ei(inside(goal,j)[2],b,ai(val,ar(rp)))));
        }))
      ))),
      ii(some(i,j=>E(b=>C(Val(g,j,b),M(x,b)))),hit=>open(hit,(j,jp)=>open(ar(jp),(b,bp)=>{
        const jd=priorIndex(td,d,i,id,j,al(jp));
        return openCarrier(app(al(agreed(agreement,j,jd,b)),al(bp)),(p,r,value,pair)=>{
          const ph=into(range,p,ei(some(i,j=>Val(f,j,p)),j,ai(al(jp),value)));
          const stage=ei(Val(h,b,r),p,ai(ph,pair));
          const goal=E(b=>E(r=>C(Val(h,b,r),M(x,b))));
          return into(union,x,pack(goal,[b,r],ai(stage,ar(bp))));
        });
      })))
    )))))))
  ));
  save('step_projects_stage',use(pairInjective,inj=>use(imported(proofs.limit_carrier_projects),limit=>
    qs(7,(f,d,g,i,p,a,r)=>ii(Trans(d),td=>ii(Agreement(f,d,g),agreement=>ii(M(i,d),id=>ii(Step(f,i,p),step=>ii(Pair(p,a,r),pair=>{
      const goal=PinnedStage(g,i,a);
      return oe(ar(ar(step)),goal,successor=>open(successor,(j,jp)=>open(ar(ar(jp)),(v,vp)=>
        open(ar(vp),(b,bp)=>open(bp,(s,sp)=>open(sp,(c,cp)=>open(cp,(t,tp)=>{
          const input=al(al(tp)),output=ar(al(tp)),stage=ar(tp);
          const ca=al(app(us(inj,p,c,t,a,r),output,pair));
          const def=eqSub(ca,x=>Def(b,x),al(al(stage)));
          const jd=priorIndex(td,d,i,id,j,al(jp));
          const previous=app(ar(agreed(agreement,j,jd,b)),carrierIn(f,j,b,v,s,al(vp),input));
          const left=goal[1],atJ=inside(left,j);
          return ol(ei(left,j,ai(al(jp),ai(al(ar(jp)),ei(atJ[2][2],b,ai(previous,def))))),goal[2]);
        }))))
      )),lim=>open(ar(lim),(h,hp)=>open(ar(hp),(b,bp)=>open(bp,(s,sp)=>{
        const ba=al(app(us(inj,p,b,s,a,r),al(sp),pair));
        const union=eqSub(ba,x=>UnionCarrier(h,x),al(ar(sp)));
        return or(goal[1],ai(al(lim),app(us(limit,f,d,g,i,h,a),td,agreement,id,al(hp),union)));
      }))));
    }))))))
  )));

  save('history_projection_stage_graph',use(imported(proofs.history_values_are_packed),packed=>
    use(imported(proofs.exact_projection_graph),graph=>use(imported(proofs.exact_projection_agreement),agree=>
      use(imported(proofs.step_projects_stage),step=>qs(3,(f,d,g)=>ii(Trans(d),td=>ii(Hist(f,d),history=>ii(Exact(f,d,g),exact=>{
        const packedValues=app(us(packed,f,d),history),ag=app(us(agree,f,d,g),exact);
        const gg=app(us(graph,f,d,g),al(history),packedValues,exact);
        const stages=ui(i=>ii(M(i,d),id=>open(app(ue(ar(history),i),id),(p,pp)=>
          open(al(ar(pp)),(a,ap)=>open(ap,(r,rp)=>{
            const value=app(ar(agreed(ag,i,id,a)),carrierIn(f,i,a,p,r,al(pp),al(rp)));
            const stage=app(us(step,f,d,g,i,p,a,r),td,ag,id,ar(pp),al(rp));
            return ei(E(a=>C(Val(g,i,a),PinnedStage(g,i,a))),a,ai(value,stage));
          }))
        )));
        return ai(gg,stages);
      }))))
    ))
  )));
  save('carrier_history_projection_exists',use(imported(proofs.history_values_are_packed),packed=>
    use(imported(proofs.exact_projection_exists),exists=>use(imported(proofs.exact_projection_agreement),agree=>
      use(imported(proofs.history_projection_stage_graph),stage=>qs(2,(f,d)=>ii(Trans(d),td=>ii(Hist(f,d),history=>
        open(app(us(exists,f,d),al(history),app(us(packed,f,d),history)),(g,exact)=>{
          const sg=app(us(stage,f,d,g),td,history,exact),ag=app(us(agree,f,d,g),exact);
          return ei(E(g=>Complete(f,d,g)),g,ai(ai(al(sg),ag),sg));
        })
      )))
    ))
  )));
  save('ordinal_carrier_history_projection',use(imported(proofs.carrier_history_projection_exists),exists=>qs(2,(f,d)=>
    ii(Ord(d),od=>ii(Hist(f,d),history=>app(us(exists,f,d),al(od),history)))
  )));
  save('projected_carriers_are_good',use(pairInjective,inj=>use(imported(proofs.history_values_are_good),good=>
    qs(3,(f,d,g)=>ii(Hist(f,d),history=>ii(Agreement(f,d,g),agreement=>ui(i=>ii(M(i,d),id=>ui(a=>ii(Val(g,i,a),value=>
      openCarrier(app(al(agreed(agreement,i,id,a)),value),(p,r,pi,pair)=>
        open(app(ue(app(ue(app(us(good,f,d),history),i),id),p),pi),(b,bp)=>open(bp,(s,sp)=>{
          const equal=app(us(inj,p,b,s,a,r),al(sp),pair);
          const atA=eqSub(al(equal),x=>C(Trans(x),W(x,s)),ar(sp));
          const atR=eqSub(ar(equal),x=>C(Trans(a),W(a,x)),atA);
          return ei(E(r=>C(Trans(a),W(a,r))),r,atR);
        }))
      )
    ))))))
  ))));
  return {proofs,formulas:forms,replacement_schema:replacement};
}

export {carrierHistoryProjectionFormulas,buildCarrierHistoryProjection};
