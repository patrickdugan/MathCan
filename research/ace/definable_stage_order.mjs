// ACE-03W. Actual partial evaluation graph and least-code well-order on pinned Def(A).
// All source assumptions are discharged through complete embedded proof trees.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildPairProductOrder } from './pair_product_order.mjs';
import { buildDescriptionCarrier, descriptionCarrierFormulas } from './description_carrier.mjs';
import { buildDescriptionEvaluation, descriptionEvaluationFormulas } from './description_evaluation.mjs';
import { buildSyntaxInstructionCodes, syntaxInstructionCodeFormulas } from './syntax_instruction_codes.mjs';
import { buildWellOrder } from './constructible_well_order.mjs';
import { buildCanonicalRelations } from './canonical_relation.mjs';
import { buildSuccessorWellOrder } from './successor_well_order.mjs';

function buildDefinableStageOrder(defs, part='all') {
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


  if(!['relations','all'].includes(part))throw Error('definable stage part');
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const Pair=(p,a,b)=>named(defs.pair,[p,a,b]),Val=(r,x,y)=>named(defs.val,[r,x,y]);
  const Omega=w=>named(defs.omega,[w]),Def=(a,b)=>named(defs.Def,[a,b]);
  const finite=buildF(defs),products=buildPairProductOrder(defs),well=buildWellOrder(defs);
  const ef=descriptionEvaluationFormulas(defs),df=descriptionCarrierFormulas(defs),tagForm=syntaxInstructionCodeFormulas(defs);
  const Eval=(d,x,a,w,ts)=>named(ef.evaluation,[d,x,a,w,...ts]);
  const Bank=(w,ts)=>named(ef.canonical_bank,[w,...ts]);
  const Distinct=ts=>named(tagForm.distinct,ts);
  const Triple=(i,w)=>named(df.triple_carrier,[i,w]);
  const Raw=(c,w,i,a)=>named(df.raw_carrier,[c,w,i,a]);
  const Product=(a,b,c)=>named(products.formulas.product,[a,b,c]);
  const W=(a,r)=>named(well.formulas.well_order,[a,r]);
  const Trans=a=>all(a,x=>all(x,y=>M(y,a)));
  const Restriction=(a,r,s)=>A(x=>A(y=>I(M(x,a),I(M(y,a),iff(Val(s,x,y),Val(r,x,y))))));
  const Initial=(a,b,s)=>A(x=>A(y=>I(M(x,a),I(M(y,b),I(Val(s,y,x),M(y,a))))));
  const Func=(c,f)=>named(well.formulas.functional,[c,f]);
  const Surj=(c,b,f)=>named(well.formulas.surjective,[c,b,f]);
  const Full=(d,x,c,b,a,w,ts)=>C(C(M(d,c),M(x,b)),Eval(d,x,a,w,ts));
  const Hit=(p,c,b,a,w,ts)=>some(c,d=>some(b,x=>C(Pair(p,d,x),Eval(d,x,a,w,ts))));
  const Exact=(f,c,b,a,w,ts)=>A(p=>iff(M(p,f),Hit(p,c,b,a,w,ts)));
  const Agreement=(f,c,b,a,w,ts)=>A(d=>A(x=>iff(Val(f,d,x),Full(d,x,c,b,a,w,ts))));
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const bounded=(goal,x,m,p)=>ei(goal,x,ai(m,p));
  const proofs={};
  const save=(id,p)=>{proofs[id]={goal:db(p.goal),proof:p.emit([],[])};};
  const ts=Array.from({length:5},(_,k)=>'tag'+k);
  const formulas={evaluation:ef.evaluation,canonical_bank:ef.canonical_bank,distinct:tagForm.distinct,
    raw_carrier:df.raw_carrier,triple_carrier:df.triple_carrier,
    exact_evaluation_graph:db(Exact('f','c','b','a','w',ts),['f','c','b','a','w',...ts]),
    evaluation_agreement:db(Agreement('f','c','b','a','w',ts),['f','c','b','a','w',...ts]),
    restriction:db(Restriction('a','r','s'),['a','r','s']),
    initial_segment:db(Initial('a','b','s'),['a','b','s']),
    functional:well.formulas.functional,surjective:well.formulas.surjective,well_order:well.formulas.well_order};

  save('evaluation_relation_exists',qs(9,(c,b,a,w,...ts)=>
    open(us(imported(products.proofs.pair_product_exists),c,b),(p,product)=>
      open(separation(p,[c,b,a,w,...ts],q=>Hit(q,c,b,a,w,ts)),(f,sep)=>{
        const exact=ui(q=>ai(
          ii(M(q,f),qf=>ar(from(sep,q,qf))),
          ii(Hit(q,c,b,a,w,ts),hit=>open(hit,(d,dp)=>open(ar(dp),(x,xp)=>{
            const pred=some(c,d=>some(b,x=>Pair(q,d,x))),inner=inside(pred,d)[2];
            const inProduct=into(product,q,bounded(pred,d,al(dp),bounded(inner,x,al(xp),al(ar(xp)))));
            return into(sep,q,ai(inProduct,hit));
          })))
        ));
        return ei(E(f=>Exact(f,c,b,a,w,ts)),f,exact);
      })
    )
  ));
  save('evaluation_relation_unique',qs(11,(c,b,a,w,...rest)=>{
    const ts=rest.slice(0,5),f=rest[5],g=rest[6];
    return ii(Exact(f,c,b,a,w,ts),ff=>ii(Exact(g,c,b,a,w,ts),gg=>
      app(us(ax({name:'extensionality'}),f,g),ui(p=>ai(
        ii(M(p,f),pf=>into(gg,p,from(ff,p,pf))),
        ii(M(p,g),pg=>into(ff,p,from(gg,p,pg)))
      )))
    ));
  }));
  save('evaluation_relation_agreement',qs(10,(c,b,a,w,...rest)=>{
    const ts=rest.slice(0,5),f=rest[5];
    return ii(Exact(f,c,b,a,w,ts),exact=>
      use(imported(finite.pair_injective),injective=>use(imported(finite.pair_exists),exists=>
        qs(2,(d,x)=>ai(
          ii(Val(f,d,x),value=>open(value,(p,pp)=>
            open(from(exact,p,al(pp)),(u,up)=>open(ar(up),(v,vp)=>{
              const eq=app(us(injective,p,d,x,u,v),ar(pp),al(ar(vp)));
              const full=ai(ai(al(up),al(vp)),ar(ar(vp)));
              const atD=eqSub(sym(al(eq)),z=>Full(z,v,c,b,a,w,ts),full);
              return eqSub(sym(ar(eq)),z=>Full(d,z,c,b,a,w,ts),atD);
            }))
          )),
          ii(Full(d,x,c,b,a,w,ts),full=>open(us(exists,d,x),(p,pair)=>{
            const hit=Hit(p,c,b,a,w,ts),inner=inside(hit,d)[2];
            const member=into(exact,p,bounded(hit,d,al(al(full)),bounded(inner,x,ar(al(full)),ai(pair,ar(full)))));
            return ei(Val(f,d,x),p,ai(member,pair));
          }))
        ))
      ))
    );
  }));
  if(part==='relations')return {proofs,formulas};

  const evaluation=buildDescriptionEvaluation(defs),descriptions=buildDescriptionCarrier(defs);
  const tags=buildSyntaxInstructionCodes(defs),canonical=buildCanonicalRelations(defs),earlier=buildE(defs,true);
  save('evaluation_relation_functional',qs(10,(c,b,a,w,...rest)=>{
    const ts=rest.slice(0,5),f=rest[5];
    return ii(Omega(w),ow=>ii(Distinct(ts),distinct=>ii(Exact(f,c,b,a,w,ts),exact=>
      use(app(us(imported(proofs.evaluation_relation_agreement),c,b,a,w,...ts,f),exact),agreement=>
        qs(3,(d,x,y)=>ii(M(d,c),_=>ii(Val(f,d,x),dx=>ii(Val(f,d,y),dy=>
          app(us(imported(evaluation.proofs.evaluation_functional),w,a,...ts,d,x,y),ow,distinct,
            ar(app(al(us(agreement,d,x)),dx)),ar(app(al(us(agreement,d,y)),dy)))
        ))))
      )
    )));
  }));
  save('evaluation_relation_surjective',qs(11,(w,a,i,c,b,f,...ts)=>ii(Omega(w),ow=>ii(Bank(w,ts),bank=>
    ii(Triple(i,w),triple=>ii(Raw(c,w,i,a),raw=>ii(Def(a,b),def=>ii(Exact(f,c,b,a,w,ts),exact=>
      use(app(us(imported(proofs.evaluation_relation_agreement),c,b,a,w,...ts,f),exact),agreement=>
        ui(x=>ii(M(x,b),xb=>{
          const equivalence=app(us(imported(evaluation.proofs.definable_iff_description_evaluation),w,a,i,c,...ts,x),ow,bank,triple,raw);
          return open(app(al(equivalence),from(def,x,xb)),(d,dp)=>{
            const value=app(ar(us(agreement,d,x)),ai(ai(al(dp),xb),ar(dp)));
            return bounded(some(c,d=>Val(f,d,x)),d,al(dp),value);
          });
        }))
      )
    ))))))
  ));
  save('coded_def_well_order',qs(11,(w,a,i,c,b,t,...ts)=>ii(Omega(w),ow=>ii(Bank(w,ts),bank=>
    ii(Triple(i,w),triple=>ii(Raw(c,w,i,a),raw=>ii(W(c,t),codeOrder=>ii(Def(a,b),def=>
      open(us(imported(proofs.evaluation_relation_exists),c,b,a,w,...ts),(f,exact)=>{
        const functional=app(us(imported(proofs.evaluation_relation_functional),c,b,a,w,...ts,f),ow,ar(bank),exact);
        const onto=app(us(imported(proofs.evaluation_relation_surjective),w,a,i,c,b,f,...ts),ow,bank,triple,raw,def,exact);
        return open(app(us(imported(canonical.induced.proofs.composed_canonical_well_order),c,b,t,f),codeOrder,functional,onto),
          (r,complete)=>ei(E(r=>W(b,r)),r,ar(al(complete))));
      })
    ))))))
  ));
  save('definable_carrier_well_order',qs(4,(w,a,r,b)=>ii(Omega(w),ow=>ii(W(a,r),wa=>ii(Def(a,b),def=>
    open(app(us(imported(descriptions.proofs.raw_description_well_order_exists),w,a,r),ow,wa),(i,ie0)=>
      open(ie0,(c,ce)=>open(ce,(t,info)=>{
        const triple=al(info),raw=al(ar(info)),codeOrder=ar(ar(info));
        function choose(p,ts) {
          if(ts.length<5)return open(p,(tag,next)=>choose(next,[...ts,tag]));
          return app(us(imported(proofs.coded_def_well_order),w,a,i,c,b,t,...ts),ow,p,triple,raw,codeOrder,def);
        }
        return choose(app(ue(imported(tags.proofs.canonical_first_five_exist),w),ow),[]);
      }))
    )
  )))));
  save('definable_stage_order_exists',qs(2,(a,r)=>ii(W(a,r),wa=>
    open(imported(finite.omega_exists),(w,ow)=>
      open(ue(imported(earlier.def_exists),a),(b,def)=>
        open(app(us(imported(proofs.definable_carrier_well_order),w,a,r,b),ow,wa,def),(s,wb)=>{
          const goal=E(b=>E(s=>C(Def(a,b),W(b,s))));
          return ei(goal,b,ei(inside(goal,b),s,ai(def,wb)));
        })
      )
    )
  )));
  const successor=buildSuccessorWellOrder(defs);
  save('definable_successor_end_extension',qs(3,(a,b,r)=>ii(Def(a,b),def=>ii(Trans(a),ta=>ii(W(a,r),wa=>{
    const subset=app(us(imported(finite.def_inflation),a,b),def,ta);
    return use(subset,ab=>open(imported(finite.omega_exists),(w,ow)=>
      open(app(us(imported(proofs.definable_carrier_well_order),w,a,r,b),ow,wa,def),(s,wb)=>
        open(app(us(imported(canonical.successor.proofs.composed_canonical_well_order),a,b,r,s),ab,wa,wb),(t,info)=>{
          const agree=ar(al(al(info))),order=ar(al(info));
          const restrict=app(us(imported(successor.proofs.successor_restriction),a,b,r,s),ab);
          const initial=us(imported(successor.proofs.successor_initial_segment),a,b,r,s);
          const restriction=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
            const previous=app(us(restrict,x,y),xa,ya),transport=us(agree,x,y);
            return ai(
              ii(Val(t,x,y),xy=>app(al(previous),app(al(transport),xy))),
              ii(Val(r,x,y),xy=>app(ar(transport),app(ar(previous),xy)))
            );
          })));
          const isInitial=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,b),yb=>ii(Val(t,y,x),yx=>
            app(us(initial,x,y),xa,yb,app(al(us(agree,y,x)),yx))
          ))));
          return ei(E(t=>C(C(W(b,t),Restriction(a,r,t)),Initial(a,b,t))),t,ai(ai(order,restriction),isInitial));
        })
      )
    ));
  })))));
  return {proofs,formulas};
}

export {buildDefinableStageOrder};
