// ACE-03X. A unique exact raw-description order from a supplied alphabet order.
// Each recipe node records exact membership. Extensionality makes every
// auxiliary unique, so existentially hiding auxiliaries preserves functionality.
import { kernel, same } from './zf_interface.mjs';
import { buildPairProductOrder } from './pair_product_order.mjs';
import { buildNaturalCodeOrder } from './natural_code_order.mjs';
import { buildFiniteSequenceCarrier, finiteSequenceCarrierFormulas } from './finite_sequence_carrier.mjs';
import { buildDescriptionCarrier } from './description_carrier.mjs';

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

function recipeLanguage(defs,l) {
  const {M,Q,I,C,O,N,A,E,named,db,form,all,some,subset}=l;
  const sequences=finiteSequenceCarrierFormulas(defs);
  const Pair=(p,x,y)=>form('pair',p,x,y),Val=(r,x,y)=>form('val',r,x,y);
  const Tuple=(g,m,a)=>form('tuple',g,m,a),iff=(p,q)=>C(I(p,q),I(q,p));
  const Product=(a,b,c)=>A(p=>iff(M(p,c),some(a,x=>some(b,y=>Pair(p,x,y)))));
  const Triple=(c,t,i,j)=>E(d=>C(Pair(d,i,j),Pair(c,t,d)));
  const TripleCarrier=(c,w)=>A(p=>iff(M(p,c),some(w,t=>some(w,i=>some(w,j=>Triple(p,t,i,j))))));
  const Finite=(g,w,a)=>some(w,m=>Tuple(g,m,a));
  const Description=(d,n,g,b)=>E(p=>C(Pair(p,g,b),Pair(d,n,p)));
  const RawMember=(d,w,i,a)=>some(w,n=>E(g=>C(Finite(g,w,i),E(b=>C(Finite(b,w,a),Description(d,n,g,b))))));
  const Raw=(c,w,i,a)=>A(d=>iff(M(d,c),RawMember(d,w,i,a)));
  const Seq=(s,w,a)=>named(sequences.finite_tuple_carrier,[s,w,a]);
  const SequenceOrder=(o,s,w,a,r)=>named(sequences.exact_order,[o,s,w,a,r]);
  const irref=(s,lt)=>all(s,x=>N(lt(x,x)));
  const trans=(s,lt)=>A(x=>A(y=>A(z=>I(M(x,s),I(M(y,s),I(M(z,s),I(lt(x,y),I(lt(y,z),lt(x,z)))))))));
  const total=(s,lt)=>A(x=>A(y=>I(M(x,s),I(M(y,s),O(Q(x,y),O(lt(x,y),lt(y,x)))))));
  const minima=(s,lt)=>A(t=>I(subset(t,s),I(E(x=>M(x,t)),E(x=>C(M(x,t),all(t,y=>N(lt(y,x))))))));
  const W=(s,r)=>{const lt=(x,y)=>Val(r,x,y);return C(C(C(irref(s,lt),trans(s,lt)),total(s,lt)),minima(s,lt));};
  const Exact=(r,phi)=>A(p=>iff(M(p,r),E(x=>E(y=>C(Pair(p,x,y),phi(x,y))))));
  const NaturalOrder=(r,w)=>Exact(r,(x,y)=>C(C(M(x,w),M(y,w)),M(x,y)));
  const Lex=(p,q,a,b,c,r,s)=>C(C(M(p,c),M(q,c)),some(a,x=>some(b,y=>
    C(Pair(p,x,y),some(a,z=>some(b,t=>C(Pair(q,z,t),O(Val(r,x,z),C(Q(x,z),Val(s,y,t))))))))));
  const ProductOrder=(t,a,b,c,r,s)=>Exact(t,(p,q)=>Lex(p,q,a,b,c,r,s));
  const conjunction=xs=>xs.reduce((p,q)=>C(p,q));
  const steps=(w,a,r,v)=>[
    NaturalOrder(v[0],w),
    Product(w,w,v[1]),
    ProductOrder(v[2],w,w,v[1],v[0],v[0]),
    Product(w,v[1],v[3]),
    ProductOrder(v[4],w,v[1],v[3],v[0],v[2]),
    Seq(v[5],w,v[3]),
    SequenceOrder(v[6],v[5],w,v[3],v[4]),
    Seq(v[7],w,a),
    SequenceOrder(v[8],v[7],w,a,r),
    Product(v[5],v[7],v[9]),
    ProductOrder(v[10],v[5],v[7],v[9],v[6],v[8]),
    Product(w,v[9],v[11]),
    ProductOrder(v[12],w,v[9],v[11],v[0],v[10])
  ];
  const Facts=(w,a,r,v)=>conjunction(steps(w,a,r,v));
  const hidden=[0,1,2,4,5,6,7,8,9,10];
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const Recipe=(w,a,r,i,c,t)=>exs(hidden.length,aux=>{
    const v=Array(13);v[3]=i;v[11]=c;v[12]=t;
    hidden.forEach((index,j)=>{v[index]=aux[j];});
    return Facts(w,a,r,v);
  });
  const Construction=(w,a,r,i,c,t)=>C(Recipe(w,a,r,i,c,t),C(C(TripleCarrier(i,w),Raw(c,w,i,a)),W(c,t)));
  const inputs=['w','a','r'],outputs=['rw','p','rp','i','ri','sg','rg','sb','rb','q','rq','c','t'];
  const formulas={
    recipe:db(Recipe('w','a','r','i','c','t'),['w','a','r','i','c','t']),
    construction:db(Construction('w','a','r','i','c','t'),['w','a','r','i','c','t']),
    exact_recipe_facts:db(Facts(...inputs,outputs),[...inputs,...outputs]),
    triple_carrier:db(TripleCarrier('i','w'),['i','w']),
    raw_carrier:db(Raw('c','w','i','a'),['c','w','i','a']),
    well_order:db(W('a','r'),['a','r']),
    product:db(Product('a','b','c'),['a','b','c']),
    natural_exact_order:db(NaturalOrder('r','w'),['r','w']),
    product_exact_order:db(ProductOrder('t','a','b','c','r','s'),['t','a','b','c','r','s']),
    finite_tuple_carrier:sequences.finite_tuple_carrier,
    sequence_exact_order:sequences.exact_order
  };
  return {Product,TripleCarrier,Raw,Seq,W,NaturalOrder,ProductOrder,SequenceOrder,steps,Facts,Recipe,Construction,hidden,formulas};
}

function canonicalDescriptionOrderFormulas(defs) {
  return recipeLanguage(defs,language(defs)).formulas;
}

function buildCanonicalDescriptionOrder(defs) {
  const l=language(defs);
  const {M,Q,C,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ei,open,eqSub,use,ax,from,into,imported,Omega,qs,compiled}=l;
  const {Product,TripleCarrier,Raw,Seq,W,steps,Facts,Recipe,Construction,hidden,formulas}=recipeLanguage(defs,l);
  const proofs={},save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const conjunction=ps=>ps.reduce(ai);
  const project=(p,index,count)=>count===1?p:index===count-1?ar(p):project(al(p),index,count-1);
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(replace(goal[2],goal[1],xs[0]),xs.slice(1),p));
  const openAll=(p,n,fn,vs=[])=>n===0?fn(vs,p):open(p,(x,px)=>openAll(px,n-1,fn,[...vs,x]));
  const outputs=(i,c,t,aux)=>{const v=Array(13);v[3]=i;v[11]=c;v[12]=t;hidden.forEach((k,j)=>{v[k]=aux[j];});return v;};
  const dependencies=[[],[],[0,1],[1],[0,1,2,3],[3],[3,4,5],[],[7],[5,7],[5,6,7,8,9],[9],[0,9,10,11]];

  // Align each earlier output before comparing the next exact membership clause.
  // The proof uses Extensionality alone and proves equality of all auxiliaries.
  save('canonical_description_auxiliaries_unique',qs(29,(w,a,r,...rest)=>{
    const left=rest.slice(0,13),right=rest.slice(13);
    return ii(Facts(w,a,r,left),lf=>ii(Facts(w,a,r,right),rf=>{
      function next(index,eqs) {
        if(index===13)return conjunction(eqs);
        const target=project(lf,index,13),current=[...right];
        let source=project(rf,index,13);
        for(const previous of dependencies[index]) {
          const before=[...current];
          source=eqSub(eqs[previous],x=>{const aligned=[...before];aligned[previous]=x;return steps(w,a,r,aligned)[index];},source);
          current[previous]=left[previous];
        }
        const equality=app(us(ax({name:'extensionality'}),right[index],left[index]),ui(x=>ai(
          ii(M(x,right[index]),xr=>into(target,x,from(source,x,xr))),
          ii(M(x,left[index]),xl=>into(source,x,from(target,x,xl)))
        )));
        return use(equality,eq=>next(index+1,[...eqs,eq]));
      }
      return next(0,[]);
    }));
  }));

  save('canonical_description_recipe_unique',qs(9,(w,a,r,i,c,t,j,d,u)=>
    ii(Recipe(w,a,r,i,c,t),left=>ii(Recipe(w,a,r,j,d,u),right=>
      openAll(left,hidden.length,(lv,lf)=>openAll(right,hidden.length,(rv,rf)=>{
        const v=outputs(i,c,t,lv),z=outputs(j,d,u,rv);
        return use(app(us(imported(proofs.canonical_description_auxiliaries_unique),w,a,r,...v,...z),lf,rf),eqs=>
          ai(ai(project(eqs,3,13),project(eqs,11,13)),project(eqs,12,13)));
      }))
    ))
  ));

  save('canonical_description_order_unique',qs(9,(w,a,r,i,c,t,j,d,u)=>
    ii(Construction(w,a,r,i,c,t),left=>ii(Construction(w,a,r,j,d,u),right=>
      app(us(imported(proofs.canonical_description_recipe_unique),w,a,r,i,c,t,j,d,u),al(left),al(right))
    ))
  ));

  const products=buildPairProductOrder(defs),natural=buildNaturalCodeOrder(defs);
  const sequences=buildFiniteSequenceCarrier(defs),descriptions=buildDescriptionCarrier(defs);
  if(!same(formulas.well_order,products.formulas.well_order)||!same(formulas.product,products.formulas.product))throw Error('canonical description product interface');
  if(!same(formulas.triple_carrier,natural.formulas.triple_carrier)||!same(formulas.raw_carrier,descriptions.formulas.raw_carrier))throw Error('canonical description carrier interface');
  const completeExact=p=>al(al(al(p))),completeOrder=p=>ar(al(p));

  save('canonical_description_order_exists',qs(3,(w,a,r)=>ii(Omega(w),ow=>ii(W(a,r),wa=>
    use(imported(products.proofs.pair_product_exists),product=>
    use(imported(products.proofs.pair_product_canonical_well_order),productOrder=>
    use(imported(sequences.proofs.finite_sequence_carrier_and_canonical_order),sequence=>
      open(app(ue(imported(natural.proofs.omega_canonical_relation),w),ow),(rw,rwc)=>
      open(us(product,w,w),(p,pp)=>
      open(app(us(productOrder,w,w,p,rw,rw),completeOrder(rwc),completeOrder(rwc),pp),(rp,rpc)=>
      open(us(product,w,p),(i,ip)=>
      open(app(us(productOrder,w,p,i,rw,rp),completeOrder(rwc),completeOrder(rpc),ip),(ri,ric)=>
      open(app(us(sequence,w,i,ri),ow,completeOrder(ric)),(sg,sgp)=>open(ar(sgp),(rg,rgc)=>
      open(app(us(sequence,w,a,r),ow,wa),(sb,sbp)=>open(ar(sbp),(rb,rbc)=>
      open(us(product,sg,sb),(q,qp)=>
      open(app(us(productOrder,sg,sb,q,rg,rb),completeOrder(rgc),completeOrder(rbc),qp),(rq,rqc)=>
      open(us(product,w,q),(c,cp)=>
      open(app(us(productOrder,w,q,c,rw,rq),completeOrder(rwc),completeOrder(rqc),cp),(t,tc)=>{
        const v=[rw,p,rp,i,ri,sg,rg,sb,rb,q,rq,c,t];
        const facts=conjunction([completeExact(rwc),pp,completeExact(rpc),ip,completeExact(ric),al(sgp),completeExact(rgc),
          al(sbp),completeExact(rbc),qp,completeExact(rqc),cp,completeExact(tc)]);
        const recipe=pack(Recipe(w,a,r,i,c,t),hidden.map(k=>v[k]),facts);
        const triple=app(us(imported(natural.proofs.nested_products_are_triple_carrier),w,p,i),pp,ip);
        const raw=app(us(imported(descriptions.proofs.nested_products_are_raw_carrier),w,i,a,sg,sb,q,c),al(sgp),al(sbp),qp,cp);
        return pack(E(i=>E(c=>E(t=>Construction(w,a,r,i,c,t)))),[i,c,t],ai(recipe,ai(ai(triple,raw),completeOrder(tc))));
      })))))))))))))
    )))
  ))));

  return {formulas,proofs,auxiliary_order:['rw','p','rp','I','ri','sg','rg','sb','rb','q','rq','C','T'],
    hidden_auxiliary_indices:hidden,step_dependencies:dependencies};
}

export {canonicalDescriptionOrderFormulas,buildCanonicalDescriptionOrder};

