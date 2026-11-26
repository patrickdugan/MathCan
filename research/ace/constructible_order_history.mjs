// ACE-03X. The canonical constructible order history and its recursion contracts.
import { kernel, same } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { canonicalStageOrderFormulas, buildCanonicalStageOrder } from './canonical_stage_order.mjs';
import { canonicalLimitOrderFormulas, buildCanonicalLimitOrder } from './canonical_limit_order.mjs';
import { buildUniformHistoryRecursion } from './uniform_history_recursion.mjs';
import { buildIndexedOrderFamily } from './indexed_order_family.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`ch${serial++}`;
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
  function imported(p){return P(named(p.goal,[]),(_,h)=>h.length?liftHyp(p.proof,h.length):p.proof);}
  const form=(name,...args)=>named(defs[name],args);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const subset=(s,a)=>all(s,x=>M(x,a)),Trans=a=>all(a,x=>subset(x,a));
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const compiled=p=>({goal:db(p.goal),proof:p.emit([],[])});
  return {fresh,M,Q,F,I,C,O,N,A,E,named,db,replace,P,ui,ii,al,ar,ai,ie,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,separation,from,into,imported,form,Empty,Succ,Omega,all,some,subset,Trans,qs,compiled};
}

function historyLanguage(defs){
  const L=language(defs),{M,Q,I,C,O,N,A,E,named,db,all,Succ}=L;
  const stages=canonicalStageOrderFormulas(defs),limits=canonicalLimitOrderFormulas(defs);
  const Pair=(p,a,r)=>named(defs.pair,[p,a,r]),Val=(f,i,r)=>named(defs.val,[f,i,r]);
  const Graph=(f,d)=>named(defs.graph,[f,d]),Ord=d=>named(defs.ordinal,[d]);
  const Good=p=>named(stages.good,[p]),Next=(p,q)=>named(stages.next,[p,q]),Embed=(p,q)=>named(stages.embed,[p,q]);
  const Value=(h,r)=>named(limits.value,[h,r]);
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const Range=(f,d,h)=>A(p=>iff(M(p,h),E(j=>C(M(j,d),Val(f,j,p)))));
  const Eq=(f,g,d)=>all(d,i=>A(r=>iff(Val(f,i,r),Val(g,i,r))));
  const Pred=d=>E(i=>C(M(i,d),Succ(i,d)));
  const Prior=(f,d,r)=>all(d,i=>A(p=>I(Val(f,i,p),Embed(p,r))));
  const SuccCase=(f,d,r)=>E(i=>C(M(i,d),C(Succ(i,d),E(p=>C(Val(f,i,p),Next(p,r))))));
  const LimitCase=(f,d,r)=>C(N(Pred(d)),E(h=>C(Range(f,d,h),Value(h,r))));
  const Step=(f,d,r)=>C(Good(r),C(Prior(f,d,r),O(SuccCase(f,d,r),LimitCase(f,d,r))));
  const Hist=(f,d)=>C(Graph(f,d),all(d,i=>E(r=>C(Val(f,i,r),Step(f,i,r)))));
  const Pointwise=(f,d)=>all(d,i=>A(p=>I(Val(f,i,p),Good(p))));
  const Forward=(f,d)=>all(d,i=>all(d,j=>I(M(i,j),A(p=>A(q=>I(Val(f,i,p),I(Val(f,j,q),Embed(p,q))))))));
  const Total=A(f=>A(d=>I(Ord(d),I(Hist(f,d),E(r=>Step(f,d,r))))));
  const Functional=A(f=>A(d=>A(r=>A(s=>I(Hist(f,d),I(Step(f,d,r),I(Step(f,d,s),Q(r,s))))))));
  const Local=A(f=>A(g=>A(d=>A(r=>I(Eq(f,g,d),I(Step(f,d,r),Step(g,d,r)))))));
  const forms={
    range:db(Range('f','d','h'),['f','d','h']),prior:db(Prior('f','d','r'),['f','d','r']),
    pointwise:db(Pointwise('f','d'),['f','d']),forward:db(Forward('f','d'),['f','d']),
    predecessor:db(Pred('d'),['d']),successor_case:db(SuccCase('f','d','r'),['f','d','r']),
    limit_case:db(LimitCase('f','d','r'),['f','d','r']),step:db(Step('f','d','r'),['f','d','r']),
    history:db(Hist('f','d'),['f','d']),value_agreement:db(Eq('f','g','d'),['f','g','d']),
    total:db(Total),functional:db(Functional),local:db(Local)
  };
  return {...L,Pair,Val,Graph,Ord,Good,Next,Embed,Value,iff,Range,Eq,Pred,Prior,SuccCase,LimitCase,Step,Hist,Pointwise,Forward,Total,Functional,Local,forms};
}

function constructibleOrderHistoryFormulas(defs){return historyLanguage(defs).forms;}

function buildConstructibleOrderHistory(defs,part='structure',options={}){
  const trace=options.onProgress||(()=>{});
  if(!['range','structure','functional','coherence','total','existence','all'].includes(part))throw Error('constructible history part');
  const {M,Q,F,I,C,O,N,A,E,db,ui,ii,al,ar,ai,ue,us,app,ref,dn,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,
    Succ,qs,compiled,Val,Graph,Ord,Good,Next,Embed,Value,Range,Eq,Pred,Prior,SuccCase,LimitCase,Step,Hist,Pointwise,Forward,forms}=historyLanguage(defs);
  const proofs={},save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  function using(ps,fn){
    const joined=ps.reduce(ai),project=(p,i,n)=>n===1?p:i===n-1?ar(p):project(al(p),i,n-1);
    return use(joined,p=>fn(ps.map((_,i)=>project(p,i,ps.length))));
  }
  const em=p=>dn(ii(N(O(p,N(p))),h=>app(h,or(p,ii(p,hp=>app(h,ol(hp,N(p))))))));
  const extEq=(a,b,fn)=>app(us(ax({name:'extensionality'}),a,b),ui(fn));
  save('prefix_range_exists',qs(2,(f,d)=>ii(Graph(f,d),graph=>{
    const i='rangeIndex',p='rangeValue',spec={name:'replacement',params:1,body:db(Val(f,i,p),[p,i,f])};
    return app(us(ax(spec),f,d),ar(graph));
  })));
  save('prefix_range_unique',qs(4,(f,d,h,k)=>ii(Range(f,d,h),left=>ii(Range(f,d,k),right=>
    extEq(h,k,p=>ai(ii(M(p,h),ph=>into(right,p,from(left,p,ph))),ii(M(p,k),pk=>into(left,p,from(right,p,pk)))))
  ))));
  save('prefix_range_transport',qs(4,(f,g,d,h)=>ii(Eq(f,g,d),eq=>ii(Range(f,d,h),range=>ui(p=>{
    function move(q,target,reverse){
      return open(q,(i,ip)=>{
        const at=ue(app(ue(eq,i),al(ip)),p),value=app(reverse?ar(at):al(at),ar(ip));
        return ei(E(i=>C(M(i,d),Val(target,i,p))),i,ai(al(ip),value));
      });
    }
    return ai(ii(M(p,h),ph=>move(from(range,p,ph),g,false)),ii(E(i=>C(M(i,d),Val(g,i,p))),q=>into(range,p,move(q,f,true))));
  })))));
  if(part==='range')return {proofs,formulas:forms};

  function valueUnique(hist,i,id,p,q,vp,vq){
    return open(app(ue(ar(al(hist)),i),id),(r,rp)=>{
      const pr=app(ue(ar(rp),p),vp),qr=app(ue(ar(rp),q),vq);
      return eqSub(sym(qr),x=>Q(p,x),pr);
    });
  }
  save('history_value_step',qs(4,(f,d,i,p)=>ii(Hist(f,d),hist=>ii(M(i,d),id=>ii(Val(f,i,p),value=>
    open(app(ue(ar(hist),i),id),(r,rp)=>{
      const rpEq=valueUnique(hist,i,id,r,p,al(rp),value);
      return eqSub(rpEq,x=>Step(f,i,x),ar(rp));
    })
  )))));
  save('history_pointwise',use(imported(proofs.history_value_step),valueStep=>qs(2,(f,d)=>ii(Hist(f,d),hist=>
    ui(i=>ii(M(i,d),id=>ui(p=>ii(Val(f,i,p),value=>al(app(us(valueStep,f,d,i,p),hist,id,value))))))
  ))));
  save('history_forward_embeddings',use(imported(proofs.history_value_step),valueStep=>qs(2,(f,d)=>ii(Hist(f,d),hist=>
    ui(i=>ii(M(i,d),id=>ui(j=>ii(M(j,d),jd=>ii(M(i,j),ij=>qs(2,(p,q)=>ii(Val(f,i,p),vp=>ii(Val(f,j,q),vq=>{
      const st=app(us(valueStep,f,d,j,q),hist,jd,vq);
      return app(ue(app(ue(al(ar(st)),i),ij),p),vp);
    }))))))))
  ))));
  save('step_prefix_local',use(imported(proofs.prefix_range_transport),rangeTransport=>qs(4,(f,g,d,r)=>ii(Eq(f,g,d),eq=>ii(Step(f,d,r),step=>{
    const prior=ui(i=>ii(M(i,d),id=>ui(p=>ii(Val(g,i,p),value=>{
      const old=app(ar(ue(app(ue(eq,i),id),p)),value);
      return app(ue(app(ue(al(ar(step)),i),id),p),old);
    }))));
    const cases=oe(ar(ar(step)),O(SuccCase(g,d,r),LimitCase(g,d,r)),succ=>
      open(succ,(i,ip)=>open(ar(ar(ip)),(p,pp)=>{
        const value=app(al(ue(app(ue(eq,i),al(ip)),p)),al(pp));
        const goal=SuccCase(g,d,r);
        return ol(ei(goal,i,ai(al(ip),ai(al(ar(ip)),ei(E(p=>C(Val(g,i,p),Next(p,r))),p,ai(value,ar(pp)))))),LimitCase(g,d,r));
      })),limit=>open(ar(limit),(h,hp)=>{
        const moved=app(us(rangeTransport,f,g,d,h),eq,al(hp));
        return or(SuccCase(g,d,r),ai(al(limit),ei(E(h=>C(Range(g,d,h),Value(h,r))),h,ai(moved,ar(hp)))));
      }));
    return ai(al(step),ai(prior,cases));
  })))));
  if(part==='structure')return {proofs,formulas:forms};

  if(part!=='total'){
  trace('before_unique_source');
  const uniqueSource=buildCanonicalStageOrder(defs,'unique',{only:['next_unique']});
  trace('after_unique_source');
  const {packed_limit_value_unique}=buildCanonicalLimitOrder(defs).proofs;
  const {successor_predecessor_unique}=buildE(defs,true);
  trace('before_functional_tree');
  save('step_functional',using([
    imported(successor_predecessor_unique),imported(uniqueSource.proofs.next_unique),
    imported(packed_limit_value_unique),imported(proofs.prefix_range_unique)
  ],([predecessorUnique,nextUnique,limitUnique,rangeUnique])=>
    qs(4,(f,d,r,s)=>ii(Hist(f,d),hist=>ii(Step(f,d,r),left=>ii(Step(f,d,s),right=>{
        function impossible(succ,lim){return open(succ,(i,ip)=>app(al(lim),ei(Pred(d),i,ai(al(ip),al(ar(ip))))));}
        function bothSucc(a,b){
          return open(a,(i,ip)=>open(b,(j,jp)=>open(ar(ar(ip)),(p,pp)=>open(ar(ar(jp)),(q,qp)=>{
            const ij=app(us(predecessorUnique,i,j,d),al(ar(ip)),al(ar(jp)));
            const atI=eqSub(sym(ij),x=>Val(f,x,q),al(qp));
            const pq=valueUnique(hist,i,al(ip),p,q,al(pp),atI);
            const sameInput=eqSub(pq,x=>Next(x,r),ar(pp));
            return app(us(nextUnique,q,r,s),sameInput,ar(qp));
          }))));
        }
        function bothLimit(a,b){return open(ar(a),(h,hp)=>open(ar(b),(k,kp)=>{
          const hk=app(us(rangeUnique,f,d,h,k),al(hp),al(kp));
          const sameRange=eqSub(sym(hk),x=>Value(x,s),ar(kp));
          return app(us(limitUnique,h,r,s),ar(hp),sameRange);
        }));}
        return oe(ar(ar(left)),Q(r,s),a=>oe(ar(ar(right)),Q(r,s),b=>bothSucc(a,b),b=>fe(impossible(a,b),Q(r,s))),
          a=>oe(ar(ar(right)),Q(r,s),b=>fe(impossible(b,a),Q(r,s)),b=>bothLimit(a,b)));
      }))))));
  trace('after_functional_tree');
  }
  if(part==='functional')return {proofs,formulas:forms};
  if(part==='coherence'){
    const recursion=buildUniformHistoryRecursion(defs,forms.step,0,{only:['history_coherence']});
    save('ordinal_order_history_coherence',using([
      imported(recursion.proofs.history_coherence),imported(proofs.step_functional),imported(proofs.step_prefix_local)
    ],([theorem,functional,local])=>app(theorem,functional,local)));
    return {proofs:{ordinal_order_history_coherence:proofs.ordinal_order_history_coherence},formulas:forms};
  }

  if(typeof globalThis.gc==='function')globalThis.gc();
  trace('before_existence_source');
  const source=buildCanonicalStageOrder(defs,'existence',{only:['next_exists','next_preserves_good','next_embeds','embed_transitive']});
  trace('after_existence_source');
  if(typeof globalThis.gc==='function')globalThis.gc();
  trace('before_indexed_source');
  const indexed=buildIndexedOrderFamily(defs);
  trace('after_indexed_source');
  trace('before_total_tree');
  save('step_total',using([
    imported(source.proofs.next_exists),imported(source.proofs.next_preserves_good),
    imported(source.proofs.next_embeds),imported(source.proofs.embed_transitive),
    imported(indexed.proofs.packed_indexed_limit_complete),imported(proofs.prefix_range_exists),
    imported(proofs.history_value_step),imported(proofs.history_pointwise),imported(proofs.history_forward_embeddings)
  ],([nextExists,nextGood,nextEmbed,embedTrans,limitComplete,rangeExists,valueStep,pointwise,forward])=>
    qs(2,(f,d)=>ii(Ord(d),od=>ii(Hist(f,d),hist=>{
      const goal=E(r=>Step(f,d,r));
      return oe(em(Pred(d)),goal,pred=>open(pred,(i,ip)=>open(app(ue(ar(al(hist)),i),al(ip)),(p,pp)=>{
        const oldStep=app(us(valueStep,f,d,i,p),hist,al(ip),al(pp));
        return open(app(ue(nextExists,p),al(oldStep)),(r,next)=>{
          const good=app(us(nextGood,p,r),next),embedded=app(us(nextEmbed,p,r),next);
          const prior=ui(j=>ii(M(j,d),jd=>ui(q=>ii(Val(f,j,q),qv=>
            oe(from(ar(ip),j,jd),Embed(q,r),ji=>{
              const earlier=app(ue(app(ue(al(ar(oldStep)),j),ji),q),qv);
              return app(us(embedTrans,q,p,r),earlier,embedded);
            },eq=>{
              const atI=eqSub(eq,x=>Val(f,x,q),qv);
              const qp=valueUnique(hist,i,al(ip),q,p,atI,al(pp));
              return eqSub(sym(qp),x=>Embed(x,r),embedded);
            })
          ))));
          const succ=ei(SuccCase(f,d,r),i,ai(al(ip),ai(ar(ip),ei(E(p=>C(Val(f,i,p),Next(p,r))),p,ai(al(pp),next)))));
          return ei(goal,r,ai(good,ai(prior,ol(succ,LimitCase(f,d,r)))));
        });
      })),notPred=>open(app(us(rangeExists,f,d),al(hist)),(h,range)=>{
        const local=app(us(pointwise,f,d),hist),coherent=app(us(forward,f,d),hist);
        return open(app(us(limitComplete,f,d,h),od,al(hist),range,local,coherent),(r,rp)=>{
          const limitStep=ai(notPred,ei(E(h=>C(Range(f,d,h),Value(h,r))),h,ai(range,al(rp))));
          return ei(goal,r,ai(al(ar(rp)),ai(ar(ar(rp)),or(SuccCase(f,d,r),limitStep))));
        });
      }));
    })))));
  trace('after_total_tree');
  if(part==='total')return {proofs,formulas:forms};

  if(typeof globalThis.gc==='function')globalThis.gc();
  trace('before_generic_tree');
  const recursion=buildUniformHistoryRecursion(defs,forms.step,0,{only:part==='all'?['ordinal_history_exists_unique','history_coherence']:['ordinal_history_exists_unique']});
  trace('after_generic_tree');
  for(const name of ['history','total','functional','local'])
    if(!same(recursion.formulas[name],forms[name]))throw Error('canonical history recursion interface: '+name);
  save('ordinal_order_history_exists_unique',using([
    imported(recursion.proofs.ordinal_history_exists_unique),imported(proofs.step_total),
    imported(proofs.step_functional),imported(proofs.step_prefix_local)
  ],([theorem,total,functional,local])=>app(theorem,total,functional,local)));
  if(part==='all')save('ordinal_order_history_coherence',using([
    imported(recursion.proofs.history_coherence),imported(proofs.step_functional),imported(proofs.step_prefix_local)
  ],([theorem,functional,local])=>app(theorem,functional,local)));
  return {proofs:part==='existence'?{ordinal_order_history_exists_unique:proofs.ordinal_order_history_exists_unique}:proofs,formulas:forms};

}

export { constructibleOrderHistoryFormulas, buildConstructibleOrderHistory };
