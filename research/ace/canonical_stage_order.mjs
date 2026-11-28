// ACE-03X. A unique canonical successor state for the exact pinned Def schema.
// Exact recipes retain every choice of auxiliary set until Extensionality
// identifies it. Packed states expose a pure functional recursion interface.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { canonicalDescriptionOrderFormulas, buildCanonicalDescriptionOrder } from './canonical_description_order.mjs';
import { descriptionEvaluationFormulas } from './description_evaluation.mjs';
import { buildSyntaxInstructionCodes } from './syntax_instruction_codes.mjs';
import { buildDefinableStageOrder } from './definable_stage_order.mjs';
import { buildCanonicalRelations } from './canonical_relation.mjs';
import { buildSuccessorWellOrder } from './successor_well_order.mjs';

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
  function imported(p){return P(named(p.goal,[]),(_,h)=>h.length===0?p.proof:liftHyp(p.proof,h.length));}
  const form=(name,...args)=>named(defs[name],args);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const subset=(s,a)=>all(s,x=>M(x,a)),Trans=a=>all(a,x=>subset(x,a));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {fresh,M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ie,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled};
}

function stageLanguage(defs) {
  const L=language(defs),{M,Q,I,C,O,N,A,E,named,db,all,some,subset,Trans,Omega}=L;
  const d=canonicalDescriptionOrderFormulas(defs),ev=descriptionEvaluationFormulas(defs);
  const Pair=(p,a,b)=>named(defs.pair,[p,a,b]),Val=(r,x,y)=>named(defs.val,[r,x,y]);
  const Def=(a,b)=>named(defs.Def,[a,b]),W=(a,r)=>named(d.well_order,[a,r]);
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const Restriction=(a,r,s)=>A(x=>A(y=>I(M(x,a),I(M(y,a),iff(Val(s,x,y),Val(r,x,y))))));
  const Initial=(a,b,s)=>A(x=>I(M(x,a),A(y=>I(M(y,b),I(Val(s,y,x),M(y,a))))));
  const Construction=(w,a,r,i,c,t)=>named(d.construction,[w,a,r,i,c,t]);
  const Bank=(w,ts)=>named(ev.canonical_bank,[w,...ts]);
  const Eval=(d,x,a,w,ts)=>named(ev.evaluation,[d,x,a,w,...ts]);
  const ExactEval=(f,c,b,a,w,ts)=>A(p=>iff(M(p,f),some(c,d=>some(b,x=>C(Pair(p,d,x),Eval(d,x,a,w,ts))))));
  const Minimum=(c,q,f,x,d)=>C(C(M(d,c),Val(f,d,x)),all(c,e=>I(Val(f,e,x),N(Val(q,e,d)))));
  const Induced=(c,b,q,f,x,y)=>C(C(M(x,b),M(y,b)),E(d=>E(e=>C(C(Minimum(c,q,f,x,d),Minimum(c,q,f,y,e)),Val(q,d,e)))));
  const Successor=(a,b,r,u,x,y)=>C(C(M(x,b),M(y,b)),O(
    C(C(M(x,a),M(y,a)),Val(r,x,y)),O(C(M(x,a),N(M(y,a))),C(C(N(M(x,a)),N(M(y,a))),Val(u,x,y)))
  ));
  const Exact=(t,phi)=>A(p=>iff(M(p,t),E(x=>E(y=>C(Pair(p,x,y),phi(x,y))))));
  const ExactInduced=(u,c,b,q,f)=>Exact(u,(x,y)=>Induced(c,b,q,f,x,y));
  const ExactSuccessor=(s,a,b,r,u)=>Exact(s,(x,y)=>Successor(a,b,r,u,x,y));
  const exs=(n,fn,xs=[])=>xs.length===n?fn(xs):E(x=>exs(n,fn,[...xs,x]));
  const Facts=(a,r,b,s,w,ts,i,c,q,f,u)=>C(C(C(Construction(w,a,r,i,c,q),ExactEval(f,c,b,a,w,ts)),ExactInduced(u,c,b,q,f)),ExactSuccessor(s,a,b,r,u));
  const Core=(a,r,b,s)=>E(w=>C(Omega(w),exs(5,ts=>C(Bank(w,ts),exs(5,([i,c,q,f,u])=>Facts(a,r,b,s,w,ts,i,c,q,f,u))))));
  const Extension=(a,r,b,s)=>C(subset(a,b),C(Restriction(a,r,s),Initial(a,b,s)));
  const Stage=(a,r,b,s)=>C(C(Def(a,b),Core(a,r,b,s)),C(C(Trans(b),W(b,s)),Extension(a,r,b,s)));
  const Good=p=>E(a=>E(r=>C(Pair(p,a,r),C(Trans(a),W(a,r)))));
  const Next=(p,q)=>exs(4,([a,r,b,s])=>C(C(Pair(p,a,r),Pair(q,b,s)),Stage(a,r,b,s)));
  const Embed=(p,q)=>exs(4,([a,r,b,s])=>C(C(Pair(p,a,r),Pair(q,b,s)),Extension(a,r,b,s)));
  const forms={
    stage:db(Stage('a','r','b','s'),['a','r','b','s']),core:db(Core('a','r','b','s'),['a','r','b','s']),
    facts:db(Facts('a','r','b','s','w',['t0','t1','t2','t3','t4'],'i','c','q','f','u'),['a','r','b','s','w','t0','t1','t2','t3','t4','i','c','q','f','u']),
    exact_evaluation_graph:db(ExactEval('f','c','b','a','w',['t0','t1','t2','t3','t4']),['f','c','b','a','w','t0','t1','t2','t3','t4']),
    exact_induced_order:db(ExactInduced('u','c','b','q','f'),['u','c','b','q','f']),
    exact_successor_order:db(ExactSuccessor('s','a','b','r','u'),['s','a','b','r','u']),
    good:db(Good('p'),['p']),next:db(Next('p','q'),['p','q']),embed:db(Embed('p','q'),['p','q']),
    extension:db(Extension('a','r','b','s'),['a','r','b','s']),
    restriction:db(Restriction('a','r','s'),['a','r','s']),initial:db(Initial('a','b','s'),['a','b','s']),
    subset:db(subset('a','b'),['a','b']),transitive:db(Trans('a'),['a']),well_order:d.well_order
  };
  return {...L,Pair,Val,Def,W,iff,Restriction,Initial,Construction,Bank,ExactEval,ExactInduced,ExactSuccessor,Facts,Core,Extension,Stage,Good,Next,Embed,forms};
}

function canonicalStageOrderFormulas(defs) {return stageLanguage(defs).forms;}

function buildCanonicalStageOrder(defs,part='all',options={}) {
  if(!['relations','unique','existence','all'].includes(part))throw Error('canonical stage part');
  const {M,Q,C,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,ei,open,eqSub,sym,use,ax,from,into,imported,Omega,subset,Trans,qs,compiled,
    Pair,Val,Def,W,Restriction,Initial,Construction,Bank,ExactEval,ExactInduced,ExactSuccessor,Facts,Core,Extension,Stage,Good,Next,Embed,forms}=stageLanguage(defs);
  const proofs={},save=(id,p)=>{proofs[id]=compiled(p);return proofs[id];};
  const inside=(goal,x)=>replace(goal[2],goal[1],x);
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inside(goal,xs[0]),xs.slice(1),p));
  const unpack=(p,n,fn,xs=[])=>n===0?fn(xs,p):open(p,(x,px)=>unpack(px,n-1,fn,[...xs,x]));
  const project=(p,index,n)=>n===1?p:index===n-1?ar(p):project(al(p),index,n-1);
  const result=()=>{
    const selected=options.only??Object.keys(proofs);
    if(!Array.isArray(selected)||selected.some(id=>!Object.hasOwn(proofs,id)))throw Error('unknown canonical stage proof selection');
    return {proofs:Object.fromEntries(selected.map(id=>[id,proofs[id]])),formulas:forms};
  };
  const finite=buildF(defs),earlier=buildE(defs,true);
  const injective=imported(finite.pair_injective);
  function alignPair(p,a,r,b,s,left,right,formula,proof) {
    return use(app(us(injective,p,a,r,b,s),left,right),eq=>
      eqSub(sym(ar(eq)),z=>formula(a,z),eqSub(sym(al(eq)),z=>formula(z,s),proof)));
  }
  function openGood(p,fn){return unpack(p,2,([a,r],body)=>fn(a,r,al(body),al(ar(body)),ar(ar(body))));}
  function openState(p,fn){return unpack(p,4,([a,r,b,s],body)=>fn(a,r,b,s,al(al(body)),ar(al(body)),ar(body)));}
  function stateIn(goal,a,r,b,s,pa,pb,property){return pack(goal,[a,r,b,s],ai(ai(pa,pb),property));}

  // Packed-state operations used by the indexed-family adapter.
  save('good_coordinates',qs(3,(p,a,r)=>ii(Good(p),good=>ii(Pair(p,a,r),pair=>
    openGood(good,(b,s,other,tb,wb)=>alignPair(p,a,r,b,s,pair,other,(x,y)=>C(Trans(x),W(x,y)),ai(tb,wb)))
  ))));
  save('embed_coordinates',qs(6,(p,q,a,r,b,s)=>ii(Embed(p,q),embedded=>ii(Pair(p,a,r),pa=>ii(Pair(q,b,s),pb=>
    openState(embedded,(u,v,x,y,pp,qp,property)=>
      alignPair(p,a,r,u,v,pa,pp,(aa,rr)=>Extension(aa,rr,b,s),
        alignPair(q,b,s,x,y,pb,qp,(bb,ss)=>Extension(u,v,bb,ss),property)))
  )))));
  save('extension_reflexive',qs(2,(a,r)=>
    ai(ui(x=>ii(M(x,a),p=>p)),ai(
      qs(2,(x,y)=>ii(M(x,a),_=>ii(M(y,a),_=>ai(ii(Val(r,x,y),p=>p),ii(Val(r,x,y),p=>p))))),
      ui(x=>ii(M(x,a),_=>ui(y=>ii(M(y,a),ya=>ii(Val(r,y,x),_=>ya)))))
    ))
  ));
  save('extension_transitive',qs(6,(a,r,b,s,c,t)=>ii(Extension(a,r,b,s),ab=>ii(Extension(b,s,c,t),bc=>{
    const sub=ui(x=>ii(M(x,a),xa=>app(ue(al(bc),x),app(ue(al(ab),x),xa))));
    const restriction=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
      const first=app(us(al(ar(ab)),x,y),xa,ya),second=app(us(al(ar(bc)),x,y),app(ue(al(ab),x),xa),app(ue(al(ab),y),ya));
      return ai(ii(Val(t,x,y),xy=>app(al(first),app(al(second),xy))),ii(Val(r,x,y),xy=>app(ar(second),app(ar(first),xy))));
    })));
    const initial=ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,c),yc=>ii(Val(t,y,x),yx=>{
      const xb=app(ue(al(ab),x),xa),yb=app(ue(app(ue(ar(ar(bc)),x),xb),y),yc,yx);
      const old=app(al(app(us(al(ar(bc)),y,x),yb,xb)),yx);
      return app(ue(app(ue(ar(ar(ab)),x),xa),y),yb,old);
    })))));
    return ai(sub,ai(restriction,initial));
  }))));
  save('embed_reflexive',ui(p=>ii(Good(p),good=>openGood(good,(a,r,pair)=>
    stateIn(Embed(p,p),a,r,a,r,pair,pair,us(imported(proofs.extension_reflexive),a,r))
  ))));
  save('embed_transitive',qs(3,(p,q,v)=>ii(Embed(p,q),pq=>ii(Embed(q,v),qv=>
    openState(pq,(a,r,b,s,pa,qb,ab)=>openState(qv,(c,t,d,u,qc,vd,cd)=>{
      const bd=alignPair(q,b,s,c,t,qb,qc,(x,y)=>Extension(x,y,d,u),cd);
      return stateIn(Embed(p,v),a,r,d,u,pa,vd,app(us(imported(proofs.extension_transitive),a,r,b,s,d,u),ab,bd));
    }))
  ))));
  save('next_preserves_good',qs(2,(p,q)=>ii(Next(p,q),next=>openState(next,(a,r,b,s,pa,pb,stage)=>
    pack(Good(q),[b,s],ai(pb,al(ar(stage))))
  ))));
  save('next_embeds',qs(2,(p,q)=>ii(Next(p,q),next=>openState(next,(a,r,b,s,pa,pb,stage)=>
    stateIn(Embed(p,q),a,r,b,s,pa,pb,ar(ar(stage)))
  ))));
  save('next_def_step',qs(6,(p,q,a,r,b,s)=>ii(Next(p,q),next=>ii(Pair(p,a,r),pa=>ii(Pair(q,b,s),pb=>
    openState(next,(u,v,x,y,pp,qp,stage)=>
      alignPair(p,a,r,u,v,pa,pp,(aa,rr)=>Def(aa,b),
        alignPair(q,b,s,x,y,pb,qp,(bb,ss)=>Def(u,bb),al(al(stage)))))
  )))));
  if(part==='relations')return result();

  const raw=buildCanonicalDescriptionOrder(defs),evals=buildDefinableStageOrder(defs,part==='unique'?'relations':'all');
  const tags=buildSyntaxInstructionCodes(defs);
  const canonical=buildCanonicalRelations(defs),successor=buildSuccessorWellOrder(defs);

  if(part!=='unique') {
  save('canonical_stage_given_Def',qs(3,(a,r,b)=>ii(Trans(a),ta=>ii(W(a,r),wa=>ii(Def(a,b),def=>
    use(app(us(imported(finite.def_inflation),a,b),def,ta),ab=>
      open(imported(finite.omega_exists),(w,ow)=>
        unpack(app(us(imported(raw.proofs.canonical_description_order_exists),w,a,r),ow,wa),3,([i,c,q],construction)=>
          unpack(app(ue(imported(tags.proofs.canonical_first_five_exist),w),ow),5,(ts,bank)=>
            open(us(imported(evals.proofs.evaluation_relation_exists),c,b,a,w,...ts),(f,exactF)=>{
              const functional=app(us(imported(evals.proofs.evaluation_relation_functional),c,b,a,w,...ts,f),ow,ar(bank),exactF);
              const onto=app(us(imported(evals.proofs.evaluation_relation_surjective),w,a,i,c,b,f,...ts),ow,bank,al(al(ar(construction))),ar(al(ar(construction))),def,exactF);
              return open(app(us(imported(canonical.induced.proofs.composed_canonical_well_order),c,b,q,f),ar(ar(construction)),functional,onto),(u,induced)=>
                open(app(us(imported(canonical.successor.proofs.composed_canonical_well_order),a,b,r,u),ab,wa,ar(al(induced))),(s,complete)=>{
                  const agree=ar(al(al(complete))),order=ar(al(complete));
                  const previous=app(us(imported(successor.proofs.successor_restriction),a,b,r,u),ab);
                  const before=us(imported(successor.proofs.successor_initial_segment),a,b,r,u);
                  const restriction=qs(2,(x,y)=>ii(M(x,a),xa=>ii(M(y,a),ya=>{
                    const old=app(us(previous,x,y),xa,ya),at=us(agree,x,y);
                    return ai(ii(Val(s,x,y),xy=>app(al(old),app(al(at),xy))),ii(Val(r,x,y),xy=>app(ar(at),app(ar(old),xy))));
                  })));
                  const initial=ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,b),yb=>ii(Val(s,y,x),yx=>app(us(before,x,y),xa,yb,app(al(us(agree,y,x)),yx)))))));
                  const facts=ai(ai(ai(construction,exactF),al(al(al(induced)))),al(al(al(complete))));
                  const coreGoal=Core(a,r,b,s),atW=inside(coreGoal,w);
                  let tsGoal=atW[2];for(const t of ts)tsGoal=inside(tsGoal,t);
                  const aux=pack(tsGoal[2],[i,c,q,f,u],facts);
                  const core=ei(coreGoal,w,ai(ow,pack(atW[2],ts,ai(bank,aux))));
                  const tb=app(us(imported(earlier.successor_transitivity),a,b),def,ab);
                  return ei(E(s=>Stage(a,r,b,s)),s,ai(ai(def,core),ai(ai(tb,order),ai(ab,ai(restriction,initial)))));
                })
              );
            })
          )
        )
      )
    )
  )))));
  save('canonical_stage_exists',qs(2,(a,r)=>ii(Trans(a),ta=>ii(W(a,r),wa=>
    open(ue(imported(earlier.def_exists),a),(b,def)=>open(app(us(imported(proofs.canonical_stage_given_Def),a,r,b),ta,wa,def),(s,stage)=>
      pack(E(b=>E(s=>Stage(a,r,b,s))),[b,s],stage)
    ))
  ))));

  }

  // Align each hidden canonical input before applying exact membership uniqueness.
  function openCore(p,fn) {return open(p,(w,wp)=>unpack(ar(wp),5,(ts,tp)=>unpack(ar(tp),5,([i,c,q,f,u],facts)=>fn(w,al(wp),ts,al(tp),i,c,q,f,u,facts))));}
  // Check the imported trees in sibling branches before the composition
  // introduces the large expanded recipe hypotheses.
  const withProofs=(items,fn)=>use(items.map(imported).reduce(ai),p=>fn(...items.map((_,i)=>project(p,i,items.length))));
  if(part!=='existence') {
  const omegaUnique=compiled(qs(2,(w,v)=>ii(Omega(w),ow=>ii(Omega(v),ov=>
    app(us(ax({name:'extensionality'}),w,v),ui(x=>ai(
      ii(M(x,w),xw=>app(ue(app(ue(ar(ow),v),al(ov)),x),xw)),
      ii(M(x,v),xv=>app(ue(app(ue(ar(ov),w),al(ow)),x),xv))
    )))
  ))));
  save('canonical_stage_core_unique',withProofs([
    omegaUnique,tags.proofs.canonical_first_five_unique,
    raw.proofs.canonical_description_order_unique,evals.proofs.evaluation_relation_unique,
    canonical.induced.proofs.exact_membership_unique,canonical.successor.proofs.exact_membership_unique
  ],(omegaUnique,tagUnique,rawUnique,evalUnique,inducedUnique,successorUnique)=>
    qs(5,(a,r,b,s,t)=>ii(Core(a,r,b,s),left=>ii(Core(a,r,b,t),right=>
      openCore(left,(w,ow,ts,bank,i,c,q,f,u,facts)=>openCore(right,(v,ov,vs,other,j,d,k,g,z,otherFacts)=>
        use(app(us(omegaUnique,v,w),ov,ow),vw=>
          use(app(us(tagUnique,...vs,...ts),al(al(other)),al(al(bank))),equalTags=>{
            const rightRaw=eqSub(vw,x=>Construction(x,a,r,j,d,k),al(al(al(otherFacts))));
            return use(app(us(rawUnique,w,a,r,i,c,q,j,d,k),al(al(al(facts))),rightRaw),eq=>{
              let rightEval=eqSub(vw,x=>ExactEval(g,d,b,a,x,vs),ar(al(al(otherFacts))));
              let current=vs.slice();
              for(let index=0;index<5;index++){
                const template=current.slice();template[index]=null;
                rightEval=eqSub(project(equalTags,index,5),x=>ExactEval(g,d,b,a,w,template.map(v=>v===null?x:v)),rightEval);
                current[index]=ts[index];
              }
              rightEval=eqSub(ar(al(eq)),x=>ExactEval(g,x,b,a,w,ts),rightEval);
              return use(app(us(evalUnique,c,b,a,w,...ts,g,f),rightEval,ar(al(al(facts)))),gf=>{
                let rightInduced=eqSub(ar(al(eq)),x=>ExactInduced(z,x,b,k,g),ar(al(otherFacts)));
                rightInduced=eqSub(ar(eq),x=>ExactInduced(z,c,b,x,g),rightInduced);
                rightInduced=eqSub(gf,x=>ExactInduced(z,c,b,q,x),rightInduced);
                return use(app(us(inducedUnique,c,b,q,f,u,z),ar(al(facts)),rightInduced),zu=>{
                  const rightSuccessor=eqSub(zu,x=>ExactSuccessor(t,a,b,r,x),ar(otherFacts));
                  return sym(app(us(successorUnique,a,b,r,u,s,t),ar(facts),rightSuccessor));
                });
              });
            });
          })
        )
      ))
    )))
  ));
  save('canonical_stage_unique',withProofs([earlier.def_unique,proofs.canonical_stage_core_unique],(defUnique,coreUnique)=>
    qs(6,(a,r,b,s,d,t)=>ii(Stage(a,r,b,s),left=>ii(Stage(a,r,d,t),right=>
      use(app(us(defUnique,a,b,d),al(al(left)),al(al(right))),bd=>{
        const moved=eqSub(sym(bd),x=>Core(a,r,x,t),ar(al(right)));
        return ai(bd,app(us(coreUnique,a,r,b,s,t),ar(al(left)),moved));
      })
    )))
  ));
  }

  if(part!=='unique') {
  save('next_exists',ui(p=>ii(Good(p),good=>openGood(good,(a,r,pair,ta,wa)=>
    unpack(app(us(imported(proofs.canonical_stage_exists),a,r),ta,wa),2,([b,s],stage)=>
      open(us(imported(finite.pair_exists),b,s),(q,pb)=>ei(E(q=>Next(p,q)),q,stateIn(Next(p,q),a,r,b,s,pair,pb,stage)))
    )
  ))));
  }

  if(part!=='existence') {
  save('next_unique',withProofs([proofs.canonical_stage_unique,earlier.ordered_pair_unique],(stageUnique,pairUnique)=>
    qs(3,(p,q,t)=>ii(Next(p,q),pq=>ii(Next(p,t),pt=>
      openState(pq,(a,r,b,s,pa,qb,left)=>openState(pt,(c,u,d,v,pc,td,right)=>{
        const atInput=alignPair(p,a,r,c,u,pa,pc,(x,y)=>Stage(x,y,d,v),right);
        return use(app(us(stageUnique,a,r,b,s,d,v),left,atInput),equal=>{
          const atB=eqSub(sym(al(equal)),x=>Pair(t,x,v),td);
          const atS=eqSub(sym(ar(equal)),x=>Pair(t,b,x),atB);
          return app(us(pairUnique,b,s,q,t),qb,atS);
        });
      }))
    )))
  ));
  }
  return result();
}

export { canonicalStageOrderFormulas, buildCanonicalStageOrder };

