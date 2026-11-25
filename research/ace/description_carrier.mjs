// ACE-03W. Actual well-ordered carriers for finite syntax descriptions.
import { kernel, same } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildPairProductOrder } from './pair_product_order.mjs';
import { buildNaturalCodeOrder } from './natural_code_order.mjs';
import { buildFiniteSequenceCarrier, finiteSequenceCarrierFormulas } from './finite_sequence_carrier.mjs';
import { buildSyntaxInstructionCodes, syntaxInstructionCodeFormulas } from './syntax_instruction_codes.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';

function descriptionCarrierFormulas(defs) {
  let serial=0;
  const fresh=()=>`fs${serial++}`;
  const M=(a,b)=>['M',a,b],Q=(a,b)=>['=',a,b],F=['F'];
  const I=(p,q)=>['>',p,q],C=(p,q)=>['&',p,q],O=(p,q)=>['|',p,q],N=p=>I(p,F);
  const bind=(op,fn)=>{const x=fresh();return [op,x,fn(x)];};
  const A=fn=>bind('A',fn),E=fn=>bind('E',fn);
  function named(p,env){
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='=')return [op,env[a],env[b]];
    if(op==='A'||op==='E'){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env){
    const [op,a,b]=p;
    if(op==='F')return F;
    if(op==='M'||op==='='){
      const i=env.indexOf(a),j=env.indexOf(b);
      if(i<0||j<0)throw Error('finite sequence interface free variable');
      return [op,i,j];
    }
    if(op==='A'||op==='E')return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }

  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const form=(name,...args)=>named(defs[name],args);
  const Pair=(p,x,y)=>form('pair',p,x,y),Tuple=(g,m,a)=>form('tuple',g,m,a);
  const finite=(g,w,a)=>some(w,m=>Tuple(g,m,a));
  const description=(d,n,g,b)=>E(p=>C(Pair(p,g,b),Pair(d,n,p)));
  const member=(d,w,i,a)=>some(w,n=>E(g=>C(finite(g,w,i),E(b=>C(finite(b,w,a),description(d,n,g,b))))));
  const raw=(c,w,i,a)=>A(d=>iff(M(d,c),member(d,w,i,a)));
  const codes=syntaxInstructionCodeFormulas(defs),sf=buildSyntaxTraceAdequacy(defs).formulas;
  const tags=['t0','t1','t2','t3','t4'],fields=['p0','p1','p2','p3','p4'];
  const Encodes=(g,m,ps,ts)=>named(codes.encodes,[g,m,...ps,...ts]);
  const Bank=(w,ts)=>C(C(named(codes.first_five,ts),named(codes.tag_members,[w,...ts])),named(codes.distinct,ts));
  const exs=(fn,ts=[])=>ts.length===5?fn(ts):E(t=>exs(fn,[...ts,t]));
  const Canonical=(g,m,w,ps)=>exs(ts=>C(Bank(w,ts),Encodes(g,m,ps,ts)));
  return {
    description:db(description('d','n','g','b'),['d','n','g','b']),
    finite_sequence:db(finite('g','w','a'),['g','w','a']),
    raw_member:db(member('d','w','i','a'),['d','w','i','a']),
    raw_carrier:db(raw('c','w','i','a'),['c','w','i','a']),
    canonical_encodes:db(Canonical('g','m','w',fields),['g','m','w',...fields]),
    canonical_tag_bank:db(Bank('w',tags),['w',...tags]),
    triple_carrier:codes.triple_carrier,encodes:codes.encodes,tag_members:codes.tag_members,
    syntax:sf.syntax
  };
}

function buildDescriptionCarrier(defs) {
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
  const all=(s,fn)=>A(x=>I(M(x,s),fn(x))),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  const iff=(p,q)=>C(I(p,q),I(q,p));
  const form=(name,...args)=>named(defs[name],args);
  const Pair=(p,x,y)=>form('pair',p,x,y),Tuple=(g,m,a)=>form('tuple',g,m,a),Omega=w=>form('omega',w);
  const formulas=descriptionCarrierFormulas(defs),finite=buildF(defs);
  const products=buildPairProductOrder(defs),natural=buildNaturalCodeOrder(defs);
  const sequences=buildFiniteSequenceCarrier(defs),instructions=buildSyntaxInstructionCodes(defs);
  const Description=(d,n,g,b)=>named(formulas.description,[d,n,g,b]);
  const Finite=(g,w,a)=>named(formulas.finite_sequence,[g,w,a]);
  const RawMember=(d,w,i,a)=>named(formulas.raw_member,[d,w,i,a]);
  const Raw=(c,w,i,a)=>named(formulas.raw_carrier,[c,w,i,a]);
  const TripleCarrier=(i,w)=>named(formulas.triple_carrier,[i,w]);
  const Seq=(s,w,a)=>named(sequences.formulas.finite_tuple_carrier,[s,w,a]);
  const Product=(a,b,c)=>named(products.formulas.product,[a,b,c]);
  const W=(a,r)=>named(products.formulas.well_order,[a,r]);
  const Syntax=(ps,m,n)=>named(formulas.syntax,[m,n,...ps]);
  const Encodes=(g,m,ps,ts)=>named(formulas.encodes,[g,m,...ps,...ts]);
  const Members=(w,ts)=>named(formulas.tag_members,[w,...ts]);
  const Bank=(w,ts)=>named(formulas.canonical_tag_bank,[w,...ts]);
  const Canonical=(g,m,w,ps)=>named(formulas.canonical_encodes,[g,m,w,...ps]);
  const inner=(p,x)=>replace(p[2],p[1],x),boundedInner=(p,x)=>inner(p,x)[2];
  const bounded=(goal,x,xs,p)=>ei(goal,x,ai(xs,p));
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inner(goal,xs[0]),xs.slice(1),p));
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const proofs={},save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];};
  if(!same(natural.formulas.triple_carrier,formulas.triple_carrier))throw Error('shared natural instruction carrier mismatch');
  if(!same(natural.formulas.well_order,products.formulas.well_order))throw Error('shared natural order mismatch');

  save('description_packing_exists',qs(3,(n,g,b)=>use(imported(finite.pair_exists),pairExists=>
    open(us(pairExists,g,b),(p,pairGB)=>open(us(pairExists,n,p),(d,pairNP)=>
      ei(E(d=>Description(d,n,g,b)),d,ei(Description(d,n,g,b),p,ai(pairGB,pairNP)))
    ))
  )));

  save('nested_products_are_raw_carrier',qs(7,(w,i,a,sg,sb,p,c)=>
    ii(Seq(sg,w,i),seqG=>ii(Seq(sb,w,a),seqB=>ii(Product(sg,sb,p),innerProduct=>ii(Product(w,p,c),outerProduct=>
      ui(d=>ai(
        ii(M(d,c),dc=>open(from(outerProduct,d,dc),(n,np)=>open(ar(np),(q,qp)=>
          open(from(innerProduct,q,al(qp)),(g,gp)=>open(ar(gp),(b,bp)=>{
            const goal=RawMember(d,w,i,a),afterN=boundedInner(goal,n),afterG=inner(afterN,g)[2];
            const described=ei(Description(d,n,g,b),q,ai(ar(bp),ar(qp)));
            return bounded(goal,n,al(np),ei(afterN,g,ai(from(seqG,g,al(gp)),
              ei(afterG,b,ai(from(seqB,b,al(bp)),described)))));
          }))
        ))),
        ii(RawMember(d,w,i,a),member=>open(member,(n,np)=>open(ar(np),(g,gp)=>
          open(ar(gp),(b,bp)=>open(ar(bp),(q,qp)=>{
            const ga=into(seqG,g,al(gp)),ba=into(seqB,b,al(bp));
            const productHit=some(sg,g=>some(sb,b=>Pair(q,g,b)));
            const qpMem=into(innerProduct,q,bounded(productHit,g,ga,bounded(boundedInner(productHit,g),b,ba,al(qp))));
            const outerHit=some(w,n=>some(p,q=>Pair(d,n,q)));
            return into(outerProduct,d,bounded(outerHit,n,al(np),bounded(boundedInner(outerHit,n),q,qpMem,ar(qp))));
          }))
        )))
      ))
    ))))
  ));

  save('raw_carrier_unique',qs(5,(c,d,w,i,a)=>ii(Raw(c,w,i,a),rc=>ii(Raw(d,w,i,a),rd=>
    app(us(ax({name:'extensionality'}),c,d),ui(x=>ai(
      ii(M(x,c),xc=>into(rd,x,from(rc,x,xc))),
      ii(M(x,d),xd=>into(rc,x,from(rd,x,xd)))
    )))
  ))));

  save('ordered_description_from_components',qs(6,(w,i,a,rw,ri,ra)=>ii(Omega(w),ow=>
    ii(W(w,rw),ww=>ii(W(i,ri),wi=>ii(W(a,ra),wa=>
      use(imported(sequences.proofs.finite_sequence_carrier_and_canonical_order),sequence=>
      use(imported(products.proofs.ordered_product_exists),product=>
        open(app(us(sequence,w,i,ri),ow,wi),(sg,sgp)=>open(ar(sgp),(rg,og)=>
        open(app(us(sequence,w,a,ra),ow,wa),(sb,sbp)=>open(ar(sbp),(rb,ob)=>
        open(app(us(product,sg,sb,rg,rb),ar(al(og)),ar(al(ob))),(p,pp)=>open(pp,(rp,pi)=>
        open(app(us(product,w,p,rw,rp),ww,ar(pi)),(c,cp)=>open(cp,(r,ci)=>{
          const raw=app(us(imported(proofs.nested_products_are_raw_carrier),w,i,a,sg,sb,p,c),al(sgp),al(sbp),al(pi),al(ci));
          const goal=E(c=>E(r=>C(Raw(c,w,i,a),W(c,r))));
          return pack(goal,[c,r],ai(raw,ar(ci)));
        }))
        ))))))
      ))
    )))
  )));

  save('raw_description_well_order_exists',qs(3,(w,a,r)=>ii(Omega(w),ow=>ii(W(a,r),wa=>
    open(app(ue(imported(natural.proofs.natural_triple_well_order_exists),w),ow),(i,ip)=>open(ip,(ri,iinfo)=>
    open(app(ue(imported(natural.proofs.omega_set_well_order_exists),w),ow),(rw,ww)=>
    open(app(us(imported(proofs.ordered_description_from_components),w,i,a,rw,ri,r),ow,ww,ar(iinfo),wa),(c,cp)=>
    open(cp,(t,ordered)=>{
      const goal=E(i=>E(c=>E(t=>C(TripleCarrier(i,w),C(Raw(c,w,i,a),W(c,t))))));
      return pack(goal,[i,c,t],ai(al(iinfo),ordered));
    }))))
    )
  ))));

  // Membership packaging preserves both supplied sequences verbatim. Their
  // lengths can be chosen independently in this broad raw carrier.
  save('sequence_description_member',qs(7,(w,i,a,c,n,g,b)=>ii(Raw(c,w,i,a),raw=>ii(M(n,w),nw=>
    ii(Finite(g,w,i),gf=>ii(Finite(b,w,a),bf=>
      open(us(imported(proofs.description_packing_exists),n,g,b),(d,described)=>{
        const goal=RawMember(d,w,i,a),afterN=boundedInner(goal,n),afterG=inner(afterN,g)[2];
        const member=bounded(goal,n,nw,ei(afterN,g,ai(gf,ei(afterG,b,ai(bf,described)))));
        return ei(E(d=>C(M(d,c),Description(d,n,g,b))),d,ai(into(raw,d,member),described));
      })
    ))
  ))));

  const EncodedMember=(g,d,w,i,a,c,m,n,b,ps,ts)=>C(C(C(Encodes(g,m,ps,ts),Tuple(g,m,i)),Description(d,n,g,b)),M(d,c));
  const CanonicalMember=(g,d,w,i,a,c,m,n,b,ps)=>C(C(C(Canonical(g,m,w,ps),Tuple(g,m,i)),Description(d,n,g,b)),M(d,c));

  save('syntax_description_with_tags',qs(17,(w,i,a,c,m,n,b,...rest)=>{
    const ps=rest.slice(0,5),ts=rest.slice(5);
    return ii(Omega(w),ow=>ii(M(n,w),nw=>ii(M(m,w),mw=>ii(Members(w,ts),members=>
    ii(TripleCarrier(i,w),carrier=>ii(Raw(c,w,i,a),raw=>ii(Syntax(ps,m,n),syntax=>ii(Tuple(b,n,a),base=>
      open(app(us(imported(instructions.proofs.finite_syntax_code_tuple_exists),w,i,m,n,...ps,...ts),ow,nw,mw,members,carrier,syntax),(g,gp)=>{
        const gf=bounded(Finite(g,w,i),m,mw,ar(gp)),bf=bounded(Finite(b,w,a),n,nw,base);
        return open(app(us(imported(proofs.sequence_description_member),w,i,a,c,n,g,b),raw,nw,gf,bf),(d,dp)=>{
          const goal=E(g=>E(d=>EncodedMember(g,d,w,i,a,c,m,n,b,ps,ts)));
          return pack(goal,[g,d],ai(ai(gp,ar(dp)),al(dp)));
        });
      })
    ))))))));
  }));

  save('syntax_description_exists',qs(12,(w,i,a,c,m,n,b,...ps)=>
    ii(Omega(w),ow=>ii(M(n,w),nw=>ii(M(m,w),mw=>ii(TripleCarrier(i,w),carrier=>
    ii(Raw(c,w,i,a),raw=>ii(Syntax(ps,m,n),syntax=>ii(Tuple(b,n,a),base=>{
      const goal=E(g=>E(d=>CanonicalMember(g,d,w,i,a,c,m,n,b,ps)));
      function unpackTags(proof,ts=[]) {
        if(ts.length<5)return open(proof,(t,tp)=>unpackTags(tp,[...ts,t]));
        const bank=proof,members=ar(al(bank));
        const packed=app(us(imported(proofs.syntax_description_with_tags),w,i,a,c,m,n,b,...ps,...ts),
          ow,nw,mw,members,carrier,raw,syntax,base);
        return open(packed,(g,gp)=>open(gp,(d,dp)=>{
          const encoded=al(al(al(dp))),tuple=ar(al(al(dp))),described=ar(al(dp)),member=ar(dp);
          const canonical=pack(Canonical(g,m,w,ps),ts,ai(bank,encoded));
          return pack(goal,[g,d],ai(ai(ai(canonical,tuple),described),member));
        }));
      }
      return unpackTags(app(ue(imported(instructions.proofs.canonical_first_five_exist),w),ow));
    })))))))
  ));

  return {proofs,formulas};
}

export { descriptionCarrierFormulas, buildDescriptionCarrier };
