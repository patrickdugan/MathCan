// ACE-03V: finite trace decoration and exact decoded-syntax Def equivalence.
// Complete object proofs compose the tag, packing and decoding constructions.
import { kernel } from './zf_interface.mjs';
import { buildInstructionTags } from './instruction_tags.mjs';
import { buildInstructionWitnesses } from './instruction_witnesses.mjs';
import { buildInstructionDecoding } from './instruction_decoding.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';

function buildSyntaxDecoration(defs) {
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

  const tags=buildInstructionTags(defs),witnesses=buildInstructionWitnesses(defs);
  const decoder=buildInstructionDecoding(defs),syntax=buildSyntaxTraceAdequacy(defs);
  const qs=(n,fn,vs=[])=>vs.length===n?fn(...vs):ui(x=>qs(n,fn,[...vs,x]));
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const form=(name,...args)=>named(defs[name],args);
  const Syn=(ps,m,n)=>named(syntax.formulas.syntax,[m,n,...ps]);
  const Trace=(ps,f,m,n,a)=>named(syntax.formulas.trace,[f,m,n,a,...ps]);
  const Decorated=(f,m,n,a)=>exs(5,ps=>C(Syn(ps,m,n),Trace(ps,f,m,n,a)));
  const Valid=(f,m,n,a)=>form('validProgram',f,m,n,a);
  const Omega=w=>form('omega',w),Nonempty=x=>E(y=>M(y,x));
  const Last=(f,m,n,a,x)=>form('lastSlice',f,m,n,a,x);
  const DecodedDef=(a,x)=>O(form('empty',x),E(w=>C(Omega(w),
    some(w,n=>some(w,m=>C(C(Nonempty(n),Nonempty(m)),
      E(f=>C(Decorated(f,m,n,a),Last(f,m,n,a,x)))))))));
  const DecodedDefSet=(a,b)=>A(x=>B(M(x,b),DecodedDef(a,x)));
  const proofs={};
  const save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};};
  function openMany(p,count,fn,vs=[]) {
    return count===0?fn(vs,p):open(p,(v,vp)=>openMany(vp,count-1,fn,[...vs,v]));
  }
  function recoverValid(f,m,n,a,decorated) {
    return openMany(decorated,5,(ps,st)=>app(us(imported(syntax.proofs.syntax_trace_is_valid_program),
      f,m,n,a,...ps),al(st),ar(st)));
  }

  save('finite_trace_has_decoded_syntax',qs(5,(w,f,m,n,a)=>
    ii(Omega(w),ow=>ii(M(m,w),mw=>ii(Valid(f,m,n,a),valid=>
      openMany(app(ue(imported(tags.proofs.five_distinct_omega_tags),w),ow),5,(ts,tp)=>{
        const selected=app(us(imported(witnesses.proofs.finite_valid_program_tagged_graph),
          w,f,m,n,a,...ts),ow,mw,valid);
        return open(selected,(g,gp)=>app(us(imported(decoder.proofs.tagged_program_has_decoded_syntax),
          g,f,m,n,a,...ts),al(valid),ar(tp),gp));
      })
    )))));

  save('finite_valid_program_iff_decoded_syntax',qs(5,(w,f,m,n,a)=>
    ii(Omega(w),ow=>ii(M(m,w),mw=>ai(
      ii(Valid(f,m,n,a),valid=>app(us(imported(proofs.finite_trace_has_decoded_syntax),w,f,m,n,a),ow,mw,valid)),
      ii(Decorated(f,m,n,a),decorated=>recoverValid(f,m,n,a,decorated))
    )))));

  // Preserve the exact outer Def witnesses, including the nonempty widths,
  // finite lengths, empty-set branch and full-base-tuple lastSlice clause.
  function convertDef(a,x,input,forward) {
    const target=forward?DecodedDef(a,x):form('definable',a,x);
    return oe(input,target,empty=>ol(empty,target[2]),program=>
      open(program,(w,wp)=>{
        const tw=replace(target[2][2],target[2][1],w);
        const nw=open(ar(wp),(n,np)=>{
          const tn=replace(tw[2][2],tw[2][1],n);
          const mm=open(ar(np),(m,mp)=>{
            const tm=replace(tn[2][2],tn[2][1],m),tf=tm[2][2];
            const ff=open(ar(ar(mp)),(f,fp)=>{
              const next=forward?
                app(us(imported(proofs.finite_trace_has_decoded_syntax),w,f,m,n,a),al(wp),al(mp),al(fp)):
                recoverValid(f,m,n,a,al(fp));
              return ei(tf,f,ai(next,ar(fp)));
            });
            return ei(tn[2],m,ai(al(mp),ai(al(ar(mp)),ff)));
          });
          return ei(tw[2],n,ai(al(np),mm));
        });
        return or(target[1],ei(target[2],w,ai(al(wp),nw)));
      }));
  }
  save('pinned_definable_has_decoded_syntax',qs(2,(a,x)=>
    ii(form('definable',a,x),given=>convertDef(a,x,given,true))));
  save('decoded_syntax_is_pinned_definable',qs(2,(a,x)=>
    ii(DecodedDef(a,x),given=>convertDef(a,x,given,false))));
  save('definable_iff_decoded_syntax',qs(2,(a,x)=>ai(
    us(imported(proofs.pinned_definable_has_decoded_syntax),a,x),
    us(imported(proofs.decoded_syntax_is_pinned_definable),a,x))));

  save('def_set_iff_decoded_syntax',use(imported(proofs.definable_iff_decoded_syntax),equivalence=>
    qs(2,(a,b)=>ai(
      ii(form('Def',a,b),old=>ui(x=>use(us(equivalence,a,x),eqv=>ai(
        ii(M(x,b),xb=>app(al(eqv),app(al(ue(old,x)),xb))),
        ii(DecodedDef(a,x),dx=>app(ar(ue(old,x)),app(ar(eqv),dx)))
      )))),
      ii(DecodedDefSet(a,b),current=>ui(x=>use(us(equivalence,a,x),eqv=>ai(
        ii(M(x,b),xb=>app(ar(eqv),app(al(ue(current,x)),xb))),
        ii(form('definable',a,x),dx=>app(ar(ue(current,x)),app(al(eqv),dx)))
      ))))
    ))));

  return {proofs,formulas:{
    decorated:db(Decorated('f','m','n','a'),['f','m','n','a']),
    decoded_definable:db(DecodedDef('a','x'),['a','x']),
    decoded_Def:db(DecodedDefSet('a','b'),['a','b'])
  }};
}

export { buildSyntaxDecoration };
