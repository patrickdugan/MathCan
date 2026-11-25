// ACE-03U. Finite witness assembly for arbitrary fixed candidate formulas.
// Every assumption is displayed in the conclusions. The original ZF kernel
// and pinned constructible-class definition remain unchanged.
import { kernel, same, scoped } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';

function buildFiniteWitnessSelection(defs, relation, paramCount, appendProof=null) {
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

  if(!Number.isSafeInteger(paramCount)||paramCount<0||paramCount>32||!scoped(relation,paramCount+2,false))
    throw Error('finite candidate formula scope');
  const form=(name,...args)=>named(defs[name],args);
  const Val=(g,i,c)=>form('val',g,i,c),Graph=(g,n)=>form('graph',g,n);
  const Empty=z=>form('empty',z),Succ=(n,d)=>form('successor',n,d),Omega=w=>form('omega',w);
  const Pair=(p,i,c)=>form('pair',p,i,c);
  const quant=(n,fn,xs=[])=>xs.length===n?fn(...xs):ui(x=>quant(n,fn,[...xs,x]));
  const Candidate=(ps,i,c)=>named(relation,[i,c,...ps]);
  const Total=(ps,n)=>A(i=>I(M(i,n),E(c=>Candidate(ps,i,c))));
  const Preserves=(ps,g,n)=>A(i=>I(M(i,n),A(c=>I(Val(g,i,c),Candidate(ps,i,c)))));
  const Selected=(ps,n)=>E(g=>C(Graph(g,n),Preserves(ps,g,n)));
  const Good=(ps,n)=>I(Total(ps,n),Selected(ps,n));
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  function valueUnique(g,n,i,id,c,v,gc,gv,graph) {
    return open(app(ue(ar(graph),i),id),(u,up)=>
      chain(app(ue(ar(up),v),gv),sym(app(ue(ar(up),c),gc))));
  }
  const append=appendProof||buildF(defs,'relations').graph_append_exists;
  const proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  save('empty_domain_selection',quant(paramCount,(...ps)=>ui(z=>ii(Empty(z),ez=>{
    const entries=ui(p=>{
      const goal=E(i=>C(M(i,z),E(c=>Pair(p,i,c))));
      return ii(M(p,z),pz=>fe(app(ue(ez,p),pz),goal));
    });
    const values=ui(i=>{
      const goal=E(c=>C(Val(z,i,c),A(v=>I(Val(z,i,v),Q(v,c)))));
      return ii(M(i,z),iz=>fe(app(ue(ez,i),iz),goal));
    });
    const graph=ai(entries,values);
    const preserves=ui(i=>ii(M(i,z),iz=>fe(app(ue(ez,i),iz),A(c=>I(Val(z,i,c),Candidate(ps,i,c))))));
    return ei(Selected(ps,z),z,ai(graph,preserves));
  }))));

  save('successor_domain_selection',quant(paramCount,(...ps)=>ui(n=>ui(d=>ii(Succ(n,d),sd=>ii(Good(ps,n),good=>ii(Total(ps,d),total=>{
    const previousTotal=ui(i=>ii(M(i,n),im=>app(ue(total,i),into(sd,i,ol(im,Q(i,n))))));
    return open(app(good,previousTotal),(f,fp)=>{
      const fg=al(fp),preserved=ar(fp),nd=into(sd,n,or(M(n,n),ref(n)));
      return open(app(ue(total,n),nd),(c,candidate)=>
        open(app(us(imported(append),f,n,d,c),fg,sd),(g,gp)=>{
          const gg=al(al(gp)),equiv=ar(al(gp)),gc=ar(gp);
          const each=ui(i=>ii(M(i,d),id=>ui(v=>ii(Val(g,i,v),gv=>
            oe(from(sd,i,id),Candidate(ps,i,v),
              im=>{
                const fv=app(ar(ue(app(ue(equiv,i),im),v)),gv);
                return app(ue(app(ue(preserved,i),im),v),fv);
              },
              eq=>{
                const atN=eqSub(eq,j=>Val(g,j,v),gv);
                const vc=valueUnique(g,d,n,nd,c,v,gc,atN,gg);
                const newCandidate=eqSub(sym(vc),y=>Candidate(ps,n,y),candidate);
                return eqSub(sym(eq),j=>Candidate(ps,j,v),newCandidate);
              })
          ))));
          return ei(Selected(ps,d),g,ai(gg,each));
        })
      );
    });
  })))))));

  // Good(n) is the implication from row-wise existence to a finite graph.
  // Separating Good inside omega and proving that subset inductive uses
  // the least-inductive-set clause of the existing Omega definition.
  save('omega_finite_selection_induction',quant(paramCount,(...ps)=>ui(w=>ii(Omega(w),ow=>
    open(separation(w,ps,n=>Good(ps,n)),(c,cp)=>{
      const base=open(al(al(ow)),(z,zp)=>{
        const selected=app(us(imported(proofs.empty_domain_selection),...ps,z),ar(zp));
        const good=ii(Total(ps,z),()=>selected);
        const zc=into(cp,z,ai(al(zp),good));
        return ei(E(z=>C(M(z,c),Empty(z))),z,ai(zc,ar(zp)));
      });
      const step=ui(n=>ii(M(n,c),nc=>{
        const previous=from(cp,n,nc),nw=al(previous),good=ar(previous);
        return open(app(ue(ar(al(ow)),n),nw),(d,dp)=>{
          const next=app(us(imported(proofs.successor_domain_selection),...ps,n,d),ar(dp),good);
          const dc=into(cp,d,ai(al(dp),next));
          return ei(E(d=>C(M(d,c),Succ(n,d))),d,ai(dc,ar(dp)));
        });
      }));
      const included=app(ue(ar(ow),c),ai(base,step));
      return ui(m=>ii(M(m,w),mw=>ar(from(cp,m,app(ue(included,m),mw)))));
    })
  ))));

  save('finite_witness_selection',quant(paramCount,(...ps)=>ui(w=>ui(m=>ii(Omega(w),ow=>ii(M(m,w),mw=>ii(Total(ps,m),total=>
    app(app(ue(app(us(imported(proofs.omega_finite_selection_induction),...ps,w),ow),m),mw),total)
  )))))));

  return {proofs,relation,paramCount};
}

function reindex(p,indices,d=0) {
  const [op,a,b]=p;
  if(op==='F')return p;
  if(op==='A'||op==='E')return [op,reindex(a,indices,d+1)];
  if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
  return [op,reindex(a,indices,d),reindex(b,indices,d)];
}

function buildFiniteSelectionInstances(defs) {
  const append=buildF(defs,'relations').graph_append_exists;
  return {
    candidate_graph:buildFiniteWitnessSelection(defs,reindex(defs.val,[2,0,1]),1,append),
    unbounded_formula:buildFiniteWitnessSelection(defs,['A',['>',['M',1,0],['M',2,0]]],0,append)
  };
}

export { buildFiniteWitnessSelection, buildFiniteSelectionInstances };
