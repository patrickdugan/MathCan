// ACE-03V: five distinct instruction tags from a supplied omega set.
// The pinned definitions and executable kernel are unchanged.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';

function buildInstructionTags(defs) {
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

  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const form=(name,...args)=>named(defs[name],args);
  const ands=xs=>xs.reduce(C), proofs={};
  const pairs=[];
  for(let i=0;i<5;i++)for(let j=i+1;j<5;j++)pairs.push([i,j]);
  const distinct=ts=>ands(pairs.map(([i,j])=>N(Q(ts[i],ts[j]))));
  const chain=ts=>ands(ts.slice(0,-1).map((t,i)=>form('successor',t,ts[i+1])));
  const members=(ts,w)=>ands(ts.map(t=>M(t,w)));
  const conj=(p,i,n)=>n===1?p:i===n-1?ar(p):conj(al(p),i,n-1);
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(replace(goal[2],goal[1],xs[0]),xs.slice(1),p));
  const save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};};
  const previous=buildF(defs,'relations').foundation_no_self;

  // Successor membership alone supplies t_i in t_j for every i<j.
  function member(ts,steps,i,j) {
    if(!(i<j))throw Error('strict tag index');
    const alternative=j===i+1?or(M(ts[i],ts[i]),ref(ts[i])):
      ol(member(ts,steps,i,j-1),Q(ts[i],ts[j-1]));
    return into(steps[j-1],ts[i],alternative);
  }
  save('successor_chain_tags_distinct',use(imported(previous),noSelf=>qs(5,(...ts)=>
    ii(chain(ts),ch=>{
      const steps=Array.from({length:4},(_,i)=>conj(ch,i,4));
      return pairs.map(([i,j])=>ii(Q(ts[i],ts[j]),eq=>
        app(ue(noSelf,ts[i]),eqSub(sym(eq),z=>M(ts[i],z),member(ts,steps,i,j))))).reduce(ai);
    }))));

  save('five_distinct_omega_tags',ui(w=>ii(form('omega',w),ow=>
    open(al(al(ow)),(zero,zp)=>{
      const target=exs(5,ts=>C(members(ts,w),distinct(ts)));
      function next(ts,inside,steps) {
        if(ts.length===5) {
          const inequalities=app(us(imported(proofs.successor_chain_tags_distinct),...ts),steps.reduce(ai));
          return pack(target,ts,ai(inside.reduce(ai),inequalities));
        }
        const k=ts.length-1;
        return open(app(ue(ar(al(ow)),ts[k]),inside[k]),(t,tp)=>
          next([...ts,t],[...inside,al(tp)],[...steps,ar(tp)]));
      }
      return next([zero],[al(zp)],[]);
    })
  )));

  return {proofs,formulas:{
    distinct:db(distinct(['t0','t1','t2','t3','t4']),['t0','t1','t2','t3','t4']),
    successor_chain:db(chain(['t0','t1','t2','t3','t4']),['t0','t1','t2','t3','t4'])
  }};
}

export { buildInstructionTags };
