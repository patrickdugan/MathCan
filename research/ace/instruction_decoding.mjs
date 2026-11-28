// ACE-03V. A selected tagged program decodes to actual syntax field sets.
// Every premise is explicit; the pinned formulas and ZF kernel are unchanged.
import { kernel, same } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildOrderRealizations } from './relation_realization.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';
import { instructionWitnessFormulas } from './instruction_witnesses.mjs';
import { buildInstructionTags } from './instruction_tags.mjs';

function buildInstructionDecoding(defs) {
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
  const all=(set,fn)=>A(x=>I(M(x,set),fn(x)));
  const some=(set,fn)=>E(x=>C(M(x,set),fn(x)));
  const ands=xs=>xs.reduce(C), ors=xs=>xs.reduce(O), ais=xs=>xs.reduce(ai);
  const B=(p,q)=>C(I(p,q),I(q,p));
  const form=(name,...args)=>named(defs[name],args);
  const V=(f,k,r)=>form('val',f,k,r), G=(f,m)=>form('graph',f,m);
  const Pair=(p,x,y)=>form('pair',p,x,y);
  const Union=(b,u)=>A(x=>B(M(x,u),E(y=>C(M(y,b),M(x,y)))));
  const subset=(b,c)=>all(b,x=>M(x,c));
  const Power=(b,p)=>A(x=>B(M(x,p),subset(x,b)));
  const OPS=['eq','mem','neg','and','exists'];
  const SEM=['relEq','relMem','relNeg','relAnd','relEx'];
  const wf=instructionWitnessFormulas(defs), sf=buildSyntaxTraceAdequacy(defs).formulas;
  const tf=buildInstructionTags(defs).formulas;
  const Binary=(c,t,i,j)=>named(wf.binary_code,[c,t,i,j]);
  const Code=(op,c,t,i,j)=>op===2?Pair(c,t,i):Binary(c,t,i,j);
  const Witness=(c,f,k,r,n,a,tags)=>named(wf.instruction_witness,[c,f,k,r,n,a,...tags]);
  const Candidate=(k,c,f,n,a,tags)=>named(wf.candidate,[k,c,f,n,a,...tags]);
  const Tagged=(g,f,m,n,a,tags)=>named(wf.tagged_program,[g,f,m,n,a,...tags]);
  const Distinct=tags=>named(tf.distinct,tags);
  const Syntax=(fields,m,n)=>named(sf.syntax,[m,n,...fields]);
  const Trace=(fields,f,m,n,a)=>named(sf.trace,[f,m,n,a,...fields]);
  const Choices=(fields,k,n)=>named(sf.choices,[k,n,...fields]);
  const Rules=(fields,f,k,r,n,a)=>named(sf.rules,[f,k,r,n,a,...fields]);
  const Instr=(op,fields,k,i,j)=>op===2?V(fields[op],k,i):
    E(d=>C(V(fields[op],k,d),Pair(d,i,j)));
  const scopes=(op,k,n)=>op<2?[n,n]:op===3?[k,k]:[k,n];
  function Sem(op,f,r,n,a,i,j) {
    if(op<2)return form(SEM[op],r,n,a,i,j);
    if(op===2)return E(p=>C(V(f,i,p),form('relNeg',r,p,n,a)));
    if(op===3)return E(p=>E(q=>C(C(V(f,i,p),V(f,j,q)),form('relAnd',r,p,q))));
    return E(p=>C(V(f,i,p),form('relEx',r,p,n,a,j)));
  }
  const Decoded=(g,t,k,d)=>E(c=>C(V(g,k,c),Pair(c,t,d)));
  const FieldMember=(g,t,p)=>E(k=>E(d=>C(Pair(p,k,d),Decoded(g,t,k,d))));
  const ExactField=(h,g,t)=>A(p=>B(M(p,h),FieldMember(g,t,p)));
  const Agreement=(h,g,t)=>A(k=>A(d=>B(V(h,k,d),Decoded(g,t,k,d))));
  const ExactFields=(fields,g,tags)=>ands(fields.map((h,op)=>ExactField(h,g,tags[op])));
  const Agreements=(fields,g,tags)=>ands(fields.map((h,op)=>Agreement(h,g,tags[op])));
  const Payload=(op,f,k,d,n,a)=>{
    const sem=(i,j)=>E(r=>C(V(f,k,r),Sem(op,f,r,n,a,i,j)));
    if(op===2)return C(M(d,k),sem(d));
    const [s,t]=scopes(op,k,n);
    return some(s,i=>some(t,j=>C(Pair(d,i,j),sem(i,j))));
  };
  const proofs={},finite=buildF(defs),prior=buildOrderRealizations(defs).induced;
  const save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];};
  const conj=(p,i,n)=>n===1?p:i===n-1?ar(p):conj(al(p),i,n-1);
  function cases(p,goal,fs){return fs.length===1?fs[0](p):oe(p,goal,q=>cases(q,goal,fs.slice(0,-1)),fs.at(-1));}
  function leaf(p,i,n){return n===1?p:i===n-1?p[2]:leaf(p[1],i,n-1);}
  function inject(p,i,n,q){return n===1?q:i===n-1?or(p[1],q):ol(inject(p[1],i,n-1,q),p[2]);}
  const inner=(p,x)=>replace(p[2],p[1],x)[2];
  const someIn=(goal,x,xs,p)=>ei(goal,x,ai(xs,p));
  const chain=(p,q)=>eqSub(q,z=>Q(p.goal[1],z),p);
  const pairExists=()=>imported(finite.pair_exists),pairInj=()=>imported(finite.pair_injective);
  const pairBound=()=>imported(prior.proofs.ordered_pair_double_power_bound);
  function openArm(op,p,fn){return open(p,(i,ip)=>op===2?fn(i,null,al(ip),null,al(ar(ip)),ar(ar(ip))):
    open(ar(ip),(j,jp)=>fn(i,j,al(ip),al(jp),al(ar(jp)),ar(ar(jp)))));}
  function openCode(op,c,t,i,j,code,fn){return op===2?fn(i,code,null):
    open(code,(d,dp)=>fn(d,ar(dp),al(dp)));}
  function unionIn(u,x,y,yb,xy){const goal=ue(u,x).goal[2][1];return into(u,x,ei(goal,y,ai(yb,xy)));}
  function distinctAt(distinct,op,q,equality){
    let index=0;
    for(let i=0;i<5;i++)for(let j=i+1;j<5;j++,index++)if(i===Math.min(op,q)&&j===Math.max(op,q))
      return app(conj(distinct,index,10),op<q?equality:sym(equality));
    throw Error('distinct opcode comparison');
  }

  // If p belongs to b and is <x,y>, both coordinates belong to union(union(b)).
  save('pair_coordinates_double_union',qs(6,(b,u,v,p,x,y)=>
    ii(Union(b,u),bu=>ii(Union(u,v),uv=>ii(M(p,b),pb=>ii(Pair(p,x,y),pair=>
      open(pair,(s,sp)=>open(sp,(d,dp)=>{
        const singleton=al(al(dp)),double=ar(al(dp)),outer=ar(dp);
        const su=unionIn(bu,s,p,pb,into(outer,s,ol(ref(s),Q(s,d))));
        const du=unionIn(bu,d,p,pb,into(outer,d,or(Q(d,s),ref(d))));
        const xv=unionIn(uv,x,s,su,into(singleton,x,ref(x)));
        const yv=unionIn(uv,y,d,du,into(double,y,or(Q(y,x),ref(y))));
        return ai(xv,yv);
      }))
    ))))
  ));

  // The set bound uses only g: its second and fourth iterated unions contain
  // every required coordinate. The exact field then follows by Separation.
  save('decoded_field_exists',qs(2,(g,t)=>
    use(imported(proofs.pair_coordinates_double_union),coords=>use(pairBound(),bound=>
    open(ue(ax({name:'union'}),g),(u1,un1)=>open(ue(ax({name:'union'}),u1),(u2,un2)=>
    open(ue(ax({name:'union'}),u2),(u3,un3)=>open(ue(ax({name:'union'}),u3),(u4,un4)=>
    open(us(ax({name:'pairing'}),u2,u4),(v,vp)=>open(ue(ax({name:'union'}),v),(b,vb)=>
    open(ue(ax({name:'power'}),b),(p1,pow1)=>open(ue(ax({name:'power'}),p1),(p2,pow2)=>
    open(separation(p2,[g,t],p=>FieldMember(g,t,p)),(h,sep)=>{
      const exact=ui(p=>ai(
        ii(M(p,h),ph=>ar(from(sep,p,ph))),
        ii(FieldMember(g,t,p),member=>open(member,(k,kp)=>open(kp,(d,dp)=>
          open(ar(dp),(c,cp)=>open(al(cp),(q,qv)=>{
            const first=app(us(coords,g,u1,u2,q,k,c),un1,un2,al(qv),ar(qv));
            const last=app(us(coords,u2,u3,u4,c,t,d),un3,un4,ar(first),ar(cp));
            const u2v=into(vp,u2,ol(ref(u2),Q(u2,u4))),u4v=into(vp,u4,or(Q(u4,u2),ref(u4)));
            const kb=unionIn(vb,k,u2,u2v,al(first)),dbb=unionIn(vb,d,u4,u4v,ar(last));
            const bounded=app(us(bound,b,p1,p2,p,k,d),pow1,pow2,kb,dbb,al(dp));
            return into(sep,p,ai(bounded,member));
          }))
        )))
      ));
      return ei(E(h=>ExactField(h,g,t)),h,exact);
    }))
    )))))))
    ))
  ));

  save('exact_field_value_agreement',qs(3,(h,g,t)=>ii(ExactField(h,g,t),exact=>
    use(pairExists(),exists=>use(pairInj(),inj=>ui(k=>ui(d=>ai(
      ii(V(h,k,d),value=>open(value,(p,pv)=>open(from(exact,p,al(pv)),(i,ip)=>open(ip,(j,jp)=>{
        const equal=app(us(inj,p,k,d,i,j),ar(pv),al(jp));
        const atK=eqSub(sym(al(equal)),z=>Decoded(g,t,z,j),ar(jp));
        return eqSub(sym(ar(equal)),z=>Decoded(g,t,k,z),atK);
      })))),
      ii(Decoded(g,t,k,d),dec=>open(us(exists,k,d),(p,pair)=>{
        const member=FieldMember(g,t,p),afterK=replace(member[2],member[1],k);
        const pr=into(exact,p,ei(member,k,ei(afterK,d,ai(pair,dec))));
        return ei(V(h,k,d),p,ai(pr,pair));
      }))
    )))))
  )));

  save('graph_values_unique',qs(5,(g,m,k,c,d)=>ii(G(g,m),graph=>ii(M(k,m),km=>
    ii(V(g,k,c),gc=>ii(V(g,k,d),gd=>open(app(ue(ar(graph),k),km),(v,vp)=>{
      const cv=app(ue(ar(vp),c),gc),dv=app(ue(ar(vp),d),gd);
      return chain(cv,sym(dv));
    })))
  ))));

  save('graph_value_in_domain',qs(4,(g,m,k,c)=>ii(G(g,m),graph=>ii(V(g,k,c),val=>
    use(pairInj(),inj=>open(val,(p,pv)=>open(app(ue(al(graph),p),al(pv)),(i,ip)=>open(ar(ip),(d,pair)=>{
      const sameRow=al(app(us(inj,p,k,c,i,d),ar(pv),pair));
      return eqSub(sym(sameRow),z=>M(z,m),al(ip));
    }))))
  ))));

  // Each decoded payload inherits bounds and a semantic witness from the
  // selected code. Distinct tags eliminate the other four entry clauses.
  for(let op=0;op<5;op++)save(OPS[op]+'_decoded_payload',qs(12,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),[k,d]=rest.slice(5);
    return ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>ii(M(k,m),km=>
      ii(Decoded(g,tags[op],k,d),dec=>use(pairInj(),inj=>open(dec,(c,cp)=>{
        const candidate=app(ue(app(ue(ar(tagged),k),km),c),al(cp));
        return open(candidate,(r,rp)=>cases(ar(rp),Payload(op,f,k,d,n,a),OPS.map((_,q)=>arm=>
          openArm(q,arm,(i,j,si,sj,code,sem)=>openCode(q,c,tags[q],i,j,code,(data,outer,innerPair)=>{
            const equal=app(us(inj,c,tags[op],d,tags[q],data),ar(cp),outer);
            if(q!==op)return fe(distinctAt(distinct,op,q,al(equal)),Payload(op,f,k,d,n,a));
            const goal=Payload(op,f,k,d,n,a);
            if(op===2){
              const dk=eqSub(sym(ar(equal)),z=>M(z,k),si);
              const fixed=eqSub(sym(ar(equal)),z=>Sem(op,f,r,n,a,z),sem);
              return ai(dk,ei(goal[2],r,ai(al(rp),fixed)));
            }
            const innerFixed=eqSub(sym(ar(equal)),z=>Pair(z,i,j),innerPair);
            const second=inner(goal,i),body=inner(second,j);
            const rExists=ei(body[2],r,ai(al(rp),sem));
            return someIn(goal,i,si,someIn(second,j,sj,ai(innerFixed,rExists)));
          }))
        )));
      })))
    )));
  }));

  function withProofs(names,fn,ps=[]){return names.length===0?fn(...ps):
    use(imported(proofs[names[0]]),p=>withProofs(names.slice(1),fn,[...ps,p]));}
  const payloadNames=OPS.map(op=>op+'_decoded_payload');
  function decodeInstruction(op,fields,g,tags,k,i,j,agreement,instruction,fn) {
    if(op===2)return open(app(al(us(agreement,k,i)),instruction),(c,cp)=>fn(c,al(cp),ar(cp)));
    return open(instruction,(d,dp)=>open(app(al(us(agreement,k,d)),al(dp)),(c,cp)=>
      fn(c,al(cp),ei(Binary(c,tags[op],i,j),d,ai(ar(dp),ar(cp))))));
  }
  function instructionFromCode(op,fields,g,tags,k,c,i,j,value,code,agreement) {
    return openCode(op,c,tags[op],i,j,code,(d,outer,innerPair)=>{
      const dec=ei(Decoded(g,tags[op],k,d),c,ai(value,outer));
      const fieldValue=app(ar(us(agreement,k,d)),dec);
      return op===2?fieldValue:ei(Instr(op,fields,k,i,j),d,ai(fieldValue,innerPair));
    });
  }
  function compareCodes(op,q,c,tags,i,j,code,u,v,other,inj,distinct) {
    return openCode(op,c,tags[op],i,j,code,(d,outer,pair)=>
      openCode(q,c,tags[q],u,v,other,(e,otherOuter,otherPair)=>{
        const equal=app(us(inj,c,tags[op],d,tags[q],e),outer,otherOuter);
        if(op!==q)return distinctAt(distinct,op,q,al(equal));
        if(op===2)return sym(ar(equal));
        const atE=eqSub(ar(equal),z=>Pair(z,i,j),pair);
        return app(us(inj,e,u,v,i,j),otherPair,atE);
      })
    );
  }
  const Shapes=(fields,m,n)=>Syntax(fields,m,n)[1];
  const EveryChoice=(fields,m,n)=>all(m,k=>Choices(fields,k,n));
  const EveryRule=(fields,f,m,n,a)=>all(m,k=>A(r=>I(V(f,k,r),Rules(fields,f,k,r,n,a))));

  save('decoded_fields_have_shape',qs(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>
      ii(ExactFields(fields,g,tags),exact=>withProofs(['graph_value_in_domain',...payloadNames],(domain,...payloads)=>{
        const shapes=Shapes(fields,m,n);
        return ais(fields.map((h,op)=>{
          const fieldExact=conj(exact,op,5),shape=leaf(shapes,op,5);
          return ui(p=>ii(M(p,h),ph=>open(from(fieldExact,p,ph),(k,kp)=>open(kp,(d,dp)=>{
            const km=open(ar(dp),(c,cp)=>app(us(domain,g,m,k,c),al(tagged),al(cp)));
            return use(km,inDomain=>{
              const payload=app(us(payloads[op],g,f,m,n,a,...tags,k,d),distinct,tagged,inDomain,ar(dp));
              const afterP=replace(shape[2],shape[1],p)[2];
              const afterK=inner(afterP,k),afterD=replace(afterK[2],afterK[1],d);
              if(op===2)return someIn(afterP,k,inDomain,ei(afterK,d,ai(al(dp),al(payload))));
              return open(payload,(i,ip)=>open(ar(ip),(j,jp)=>{
                const operand=afterD[2],afterI=replace(operand[2],operand[1],i);
                const dataProof=ei(operand,i,ei(afterI,j,ai(ai(al(ar(jp)),al(ip)),al(jp))));
                return someIn(afterP,k,inDomain,ei(afterK,d,ai(al(dp),dataProof)));
              }));
            });
          }))));
        }));
      }))
    ));
  }));

  save('decoded_fields_have_choices',qs(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>
      ii(Agreements(fields,g,tags),agreements=>use(pairInj(),inj=>
      withProofs(['graph_values_unique'],unique=>ui(k=>ii(M(k,m),km=>
        open(app(ue(ar(al(tagged)),k),km),(c,gc)=>{
          const value=al(gc),candidate=app(ue(app(ue(ar(tagged),k),km),c),value);
          return open(candidate,(r,rp)=>cases(ar(rp),Choices(fields,k,n),OPS.map((_,op)=>arm=>
            openArm(op,arm,(i,j,si,sj,code,sem)=>{
              const agreement=conj(agreements,op,5);
              const instruction=instructionFromCode(op,fields,g,tags,k,c,i,j,value,code,agreement);
              function compare(q,u,v,otherInstruction) {
                return decodeInstruction(q,fields,g,tags,k,u,v,conj(agreements,q,5),otherInstruction,
                  (otherC,otherValue,otherCode)=>{
                    const codeEqual=app(us(unique,g,m,k,otherC,c),al(tagged),km,otherValue,value);
                    const fixed=eqSub(codeEqual,z=>Code(q,z,tags[q],u,v),otherCode);
                    return compareCodes(op,q,c,tags,i,j,code,u,v,fixed,inj,distinct);
                  });
              }
              const same=op===2?ui(u=>ii(Instr(op,fields,k,u),other=>compare(op,u,null,other))):
                ui(u=>ui(v=>ii(Instr(op,fields,k,u,v),other=>compare(op,u,v,other))));
              const excluded=OPS.map((_,q)=>q).filter(q=>q!==op).map(q=>q===2?
                ui(u=>ii(Instr(q,fields,k,u),other=>compare(q,u,null,other))):
                ui(u=>ui(v=>ii(Instr(q,fields,k,u,v),other=>compare(q,u,v,other)))));
              const only=ais([same,...excluded]),chosen=ai(instruction,only);
              const goal=Choices(fields,k,n),branch=leaf(goal,op,5);
              const tail=op===2?chosen:someIn(inner(branch,i),j,sj,chosen);
              return inject(goal,op,5,someIn(branch,i,si,tail));
            })
          )));
        })
      )))
      ))
    ));
  }));

  save('decoded_fields_follow_rules',qs(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return ii(G(f,m),graph=>ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>
      ii(Agreements(fields,g,tags),agreements=>use(pairInj(),inj=>
      withProofs(['graph_values_unique',...payloadNames],(unique,...payloads)=>
        ui(k=>ii(M(k,m),km=>ui(r=>ii(V(f,k,r),fr=>ais(OPS.map((_,op)=>{
          function instructionRule(i,j,instruction) {
            const agreement=conj(agreements,op,5);
            function atData(d,pair,fieldValue) {
              const dec=app(al(us(agreement,k,d)),fieldValue);
              const payload=app(us(payloads[op],g,f,m,n,a,...tags,k,d),distinct,tagged,km,dec);
              function atRow(row,proof,sem) {
                const equal=app(us(unique,f,m,k,row,r),graph,km,proof,fr);
                return eqSub(equal,z=>Sem(op,f,z,n,a,i,j),sem);
              }
              if(op===2)return open(ar(payload),(row,rp)=>atRow(row,al(rp),ar(rp)));
              return open(payload,(u,up)=>open(ar(up),(v,vp)=>{
                const sameOperands=app(us(inj,d,i,j,u,v),pair,al(ar(vp)));
                return open(ar(ar(vp)),(row,rp)=>{
                  const atI=eqSub(sym(al(sameOperands)),z=>Sem(op,f,row,n,a,z,v),ar(rp));
                  const atJ=eqSub(sym(ar(sameOperands)),z=>Sem(op,f,row,n,a,i,z),atI);
                  return atRow(row,al(rp),atJ);
                });
              }));
            }
            return op===2?atData(i,null,instruction):open(instruction,(d,dp)=>atData(d,ar(dp),al(dp)));
          }
          return op===2?ui(i=>ii(Instr(op,fields,k,i),instruction=>instructionRule(i,null,instruction))):
            ui(i=>ui(j=>ii(Instr(op,fields,k,i,j),instruction=>instructionRule(i,j,instruction))));
        }))))))
      ))
    ))));
  }));

  save('decoded_fields_syntax_and_trace',qs(15,(g,f,m,n,a,...rest)=>{
    const tags=rest.slice(0,5),fields=rest.slice(5);
    return ii(G(f,m),graph=>ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>
      ii(ExactFields(fields,g,tags),exact=>withProofs(['exact_field_value_agreement'],agree=>{
        const agreements=ais(fields.map((h,op)=>app(us(agree,h,g,tags[op]),conj(exact,op,5))));
        return use(agreements,agreements=>{
          const args=[g,f,m,n,a,...tags,...fields];
          const shapes=app(us(imported(proofs.decoded_fields_have_shape),...args),distinct,tagged,exact);
          const choices=app(us(imported(proofs.decoded_fields_have_choices),...args),distinct,tagged,agreements);
          const rules=app(us(imported(proofs.decoded_fields_follow_rules),...args),graph,distinct,tagged,agreements);
          return ai(ai(shapes,choices),ai(graph,rules));
        });
      }))
    )));
  }));

  const existsFields=(fn,fields=[])=>fields.length===5?fn(fields):E(h=>existsFields(fn,[...fields,h]));
  const existentialIntro=(goal,fields,proof)=>fields.length===0?proof:
    ei(goal,fields[0],existentialIntro(replace(goal[2],goal[1],fields[0]),fields.slice(1),proof));
  save('tagged_program_has_decoded_syntax',qs(10,(g,f,m,n,a,...tags)=>
    ii(G(f,m),graph=>ii(Distinct(tags),distinct=>ii(Tagged(g,f,m,n,a,tags),tagged=>
      use(imported(proofs.decoded_field_exists),fieldExists=>{
        const goal=existsFields(fields=>C(Syntax(fields,m,n),Trace(fields,f,m,n,a)));
        function construct(fields=[],exact=[]) {
          if(fields.length<5)return open(us(fieldExists,g,tags[fields.length]),(h,hp)=>construct([...fields,h],[...exact,hp]));
          const decoded=app(us(imported(proofs.decoded_fields_syntax_and_trace),g,f,m,n,a,...tags,...fields),
            graph,distinct,tagged,ais(exact));
          return existentialIntro(goal,fields,decoded);
        }
        return construct();
      })
    )))
  ));

  return {proofs,formulas:{
    decoded:db(Decoded('g','t','k','d'),['g','t','k','d']),
    exact_field:db(ExactField('h','g','t'),['h','g','t']),
    field_agreement:db(Agreement('h','g','t'),['h','g','t']),
    exact_fields:db(ExactFields(['e','v','q','c','x'],'g',['t0','t1','t2','t3','t4']),
      ['g','t0','t1','t2','t3','t4','e','v','q','c','x']),
    field_agreements:db(Agreements(['e','v','q','c','x'],'g',['t0','t1','t2','t3','t4']),
      ['g','t0','t1','t2','t3','t4','e','v','q','c','x']),
    payloads:OPS.map((_,op)=>db(Payload(op,'f','k','d','n','a'),['f','k','d','n','a'])),
    distinct:tf.distinct,syntax:sf.syntax,trace:sf.trace,tagged_program:wf.tagged_program
  }};
}

export { buildInstructionDecoding };
