// ACE-03W. Partial evaluation of exact descriptions with their encoded base tuple.
// The empty-output branch and supplied omega remain explicit.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';
import { buildSyntaxDecoration } from './syntax_decoration.mjs';
import { buildSyntaxInstructionCodes, syntaxInstructionCodeFormulas } from './syntax_instruction_codes.mjs';
import { buildOmegaWellOrder } from './omega_well_order.mjs';
import { descriptionCarrierFormulas, buildDescriptionCarrier } from './description_carrier.mjs';

function language(defs) {
  let serial=0;
  const fresh=()=>`o${serial++}`;
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

function evaluationLanguage(defs) {
  const L=language(defs),{M,C,I,O,A,E,named,db,form,Empty,Succ,all,some}=L;
  const sf=buildSyntaxTraceAdequacy(defs).formulas,cf=syntaxInstructionCodeFormulas(defs),df=descriptionCarrierFormulas(defs);
  const Val=(f,k,r)=>form('val',f,k,r),Graph=(f,m)=>form('graph',f,m),Tuple=(b,n,a)=>form('tuple',b,n,a);
  const Syntax=(ps,m,n)=>named(sf.syntax,[m,n,...ps]),Trace=(ps,f,m,n,a)=>named(sf.trace,[f,m,n,a,...ps]);
  const Encodes=(g,m,ps,ts)=>named(cf.encodes,[g,m,...ps,...ts]);
  const Distinct=ts=>named(cf.distinct,ts),Members=(w,ts)=>named(cf.tag_members,[w,...ts]);
  const FirstFive=ts=>named(cf.first_five,ts),Canonical=(w,ts)=>C(C(FirstFive(ts),Members(w,ts)),Distinct(ts));
  const TripleCarrier=(i,w)=>named(cf.triple_carrier,[i,w]);
  const Description=(d,n,g,b)=>named(df.description,[d,n,g,b]),RawCarrier=(c,w,i,a)=>named(df.raw_carrier,[c,w,i,a]);
  const FiniteSeq=(g,w,a)=>named(df.finite_sequence,[g,w,a]),RawMember=(d,w,i,a)=>named(df.raw_member,[d,w,i,a]);
  const Nonempty=n=>E(x=>M(x,n)),Slice=(x,r,a,n,z,b)=>form('slice',x,r,a,n,z,b);
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const Last=(f,m,n,a,b,x)=>some(m,k=>C(Succ(k,m),E(r=>C(Val(f,k,r),some(n,z=>C(Empty(z),Slice(x,r,a,n,z,b)))))));
  const Positive=(d,x,a,w,ts)=>some(w,n=>some(w,m=>C(C(Nonempty(n),Nonempty(m)),
    E(g=>E(b=>C(C(Description(d,n,g,b),Tuple(b,n,a)),exs(5,ps=>E(f=>
      C(C(C(Syntax(ps,m,n),Encodes(g,m,ps,ts)),Trace(ps,f,m,n,a)),Last(f,m,n,a,b,x))
    ))))))));
  const Output=(a,x,w,c,ts)=>O(Empty(x),some(c,d=>Positive(d,x,a,w,ts)));
  const B=(p,q)=>C(I(p,q),I(q,p));
  const OutputSet=(a,b,w,c,ts)=>A(x=>B(M(x,b),Output(a,x,w,c,ts)));
  const EmptyCode=d=>E(z=>C(Empty(z),Description(d,z,z,z)));
  const Evaluate=(d,x,a,w,ts)=>O(C(EmptyCode(d),Empty(x)),Positive(d,x,a,w,ts));
  const Evaluated=(a,x,w,c,ts)=>some(c,d=>Evaluate(d,x,a,w,ts));
  const ts=['t0','t1','t2','t3','t4'];
  const formulas={
    last_at_base:db(Last('f','m','n','a','b','x'),['f','m','n','a','b','x']),
    positive_evaluation:db(Positive('d','x','a','w',ts),['d','x','a','w',...ts]),
    decoded_definable:db(Output('a','x','w','c',ts),['a','x','w','c',...ts]),
    decoded_Def:db(OutputSet('a','b','w','c',ts),['a','b','w','c',...ts]),
    canonical_bank:db(Canonical('w',ts),['w',...ts]),
    empty_code:db(EmptyCode('d'),['d']),
    evaluation:db(Evaluate('d','x','a','w',ts),['d','x','a','w',...ts]),
    evaluated_definable:db(Evaluated('a','x','w','c',ts),['a','x','w','c',...ts])
  };
  return {...L,Val,Graph,Tuple,Syntax,Trace,Encodes,Distinct,Members,FirstFive,Canonical,TripleCarrier,Description,RawCarrier,FiniteSeq,RawMember,Nonempty,Slice,exs,Last,Positive,Output,OutputSet,EmptyCode,Evaluate,Evaluated,B,formulas};
}

function descriptionEvaluationFormulas(defs){return evaluationLanguage(defs).formulas;}

function buildDescriptionEvaluation(defs) {
  const {M,Q,F,I,C,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,
    form,Empty,Succ,Omega,all,some,Trans,qs,compiled,Val,Graph,Tuple,Syntax,Trace,Encodes,Distinct,Members,Canonical,
    TripleCarrier,Description,RawCarrier,FiniteSeq,RawMember,Nonempty,Slice,Last,Positive,Output,EmptyCode,Evaluate,Evaluated,B,formulas}=evaluationLanguage(defs);
  const {normalized_triple_exists:tripleExists,normalized_triple_injective:tripleInj,
    normalized_graph_determines_syntax_fields:fieldsUnique}=buildSyntaxInstructionCodes(defs).proofs;
  const {foundation_no_self:_unused,value_in_domain:valueDomain}=buildF(defs,'relations');
  const predecessorUnique=buildE(defs,true).successor_predecessor_unique;
  const syntax=buildSyntaxTraceAdequacy(defs);
  const memberTransitive=buildOmegaWellOrder(defs).proofs.omega_member_transitive;
  const decorate=buildSyntaxDecoration(defs).proofs.finite_trace_has_decoded_syntax;
  const descriptionCoverage=buildDescriptionCarrier(defs).proofs.syntax_description_with_tags;
  if(!descriptionCoverage)throw Error('description coverage theorem is unavailable');
  const proofs={},save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const conj=(p,i,n)=>n===1?p:i===n-1?ar(p):conj(al(p),i,n-1);
  const inner=(p,x)=>replace(p[2],p[1],x);
  function pack(goal,xs,p){return xs.length===0?p:ei(goal,xs[0],pack(inner(goal,xs[0]),xs.slice(1),p));}
  function openMany(p,n,fn,vs=[]){return n===0?fn(vs,p):open(p,(x,xp)=>openMany(xp,n-1,fn,[...vs,x]));}
  function emptyEqual(a,b,ea,eb) {
    return app(us(ax({name:'extensionality'}),a,b),ui(x=>ai(
      ii(M(x,a),xa=>fe(app(ue(ea,x),xa),M(x,b))),
      ii(M(x,b),xb=>fe(app(ue(eb,x),xb),M(x,a))))));
  }
  function lastIntro(f,m,n,a,b,x,k,r,z,km,succ,fr,zn,ez,slice) {
    const goal=Last(f,m,n,a,b,x),rg=inner(goal,k)[2][2],zg=inner(rg,r)[2];
    return ei(goal,k,ai(km,ai(succ,ei(rg,r,ai(fr,ei(zg,z,ai(zn,ai(ez,slice))))))));
  }
  function openLast(last,fn) {
    return open(last,(k,kp)=>open(ar(ar(kp)),(r,rp)=>open(ar(rp),(z,zp)=>
      fn(k,r,z,al(kp),al(ar(kp)),al(rp),al(zp),al(ar(zp)),ar(ar(zp)))
    )));
  }
  function openPositive(p,fn) {
    return open(p,(n,np)=>open(ar(np),(m,mp)=>open(ar(ar(mp)),(g,gp)=>open(gp,(b,bp)=>
      openMany(ar(bp),5,(ps,fp)=>open(fp,(f,program)=>fn({n,m,g,b,ps,f,nw:al(np),mw:al(mp),
        nn:al(al(ar(mp))),mn:ar(al(ar(mp))),description:al(al(bp)),tuple:ar(al(bp)),
        syntax:al(al(al(program))),encoded:ar(al(al(program))),trace:ar(al(program)),last:ar(program)})))
    ))));
  }
  function positiveIntro(d,x,a,w,ts,p) {
    const goal=Positive(d,x,a,w,ts),mg=inner(goal,p.n)[2],gg=inner(mg,p.m)[2][2],bg=inner(gg,p.g),fg=inner(bg,p.b)[2];
    const program=ai(ai(ai(p.syntax,p.encoded),p.trace),p.last);
    const fields=pack(fg,[...p.ps,p.f],program);
    const body=ei(gg,p.g,ei(bg,p.b,ai(ai(p.description,p.tuple),fields)));
    return ei(goal,p.n,ai(p.nw,ei(mg,p.m,ai(p.mw,ai(ai(p.nn,p.mn),body)))));
  }

  save('omega_set_unique',qs(2,(w,v)=>ii(Omega(w),ow=>ii(Omega(v),ov=>{
    const wv=app(ue(ar(ow),v),al(ov)),vw=app(ue(ar(ov),w),al(ow));
    return app(us(ax({name:'extensionality'}),w,v),ui(x=>ai(
      ii(M(x,w),xw=>app(ue(wv,x),xw)),ii(M(x,v),xv=>app(ue(vw,x),xv))
    )));
  }))));
  save('last_at_base_is_last_slice',qs(6,(f,m,n,a,b,x)=>ii(Tuple(b,n,a),tuple=>ii(Last(f,m,n,a,b,x),last=>
    openLast(last,(k,r,z,km,succ,fr,zn,ez,slice)=>{
      const goal=form('lastSlice',f,m,n,a,x),rg=inner(goal,k)[2][2],zg=inner(rg,r)[2],bg=inner(zg,z)[2][2];
      const base=ei(bg,b,ai(tuple,slice));
      return ei(goal,k,ai(km,ai(succ,ei(rg,r,ai(fr,ei(zg,z,ai(zn,ai(ez,base))))))));
    })
  ))));
  save('last_slice_has_base_tuple',qs(5,(f,m,n,a,x)=>ii(form('lastSlice',f,m,n,a,x),last=>
    open(last,(k,kp)=>open(ar(ar(kp)),(r,rp)=>open(ar(rp),(z,zp)=>open(ar(ar(zp)),(b,bp)=>
      ei(E(y=>C(Tuple(y,n,a),Last(f,m,n,a,y,x))),b,ai(al(bp),
        lastIntro(f,m,n,a,b,x,k,r,z,al(kp),al(ar(kp)),al(rp),al(zp),al(ar(zp)),ar(bp))))
    ))))
  )));
  save('common_program_last_at_base_unique',use(imported(predecessorUnique),pred=>qs(13,(m,n,a,b,f,h,x,y,...ps)=>
    ii(Trans(m),tm=>ii(Syntax(ps,m,n),syn=>ii(Trace(ps,f,m,n,a),tf=>ii(Trace(ps,h,m,n,a),th=>
      ii(Last(f,m,n,a,b,x),lx=>ii(Last(h,m,n,a,b,y),ly=>{
        const agree=app(us(imported(syntax.proofs.common_program_slice_agreement),m,n,a,f,h,...ps),tm,syn,tf,th);
        return use(agree,sa=>openLast(lx,(k,r,z,km,sk,fr,_zn,ez,sx)=>
          openLast(ly,(l,s,u,_lm,sl,hs,_un,eu,sy)=>{
            const kl=app(us(pred,k,l,m),sk,sl),hks=eqSub(sym(kl),v=>Val(h,v,s),hs);
            const zu=emptyEqual(z,u,ez,eu),atZ=eqSub(sym(zu),v=>Slice(y,s,a,n,v,b),sy);
            return app(us(app(ue(sa,k),km),r,s,x,y,z,b),fr,hks,sx,atZ);
          })
        ));
      }))
    ))))
  )));

  save('positive_evaluation_functional',use(imported(tripleInj),inj=>use(imported(valueDomain),domain=>
    qs(10,(w,a,...vs)=>{
      const ts=vs.slice(0,5),[d,x,y]=vs.slice(5);
      return ii(Omega(w),ow=>ii(Distinct(ts),distinct=>ii(Positive(d,x,a,w,ts),px=>ii(Positive(d,y,a,w,ts),py=>
        openPositive(px,left=>openPositive(py,right=>{
          const coordinates=app(us(inj,d,left.n,left.g,left.b,right.n,right.g,right.b),left.description,right.description);
          return use(coordinates,co=>{
            const nn=al(al(co)),gg=ar(al(co)),bb=ar(co);
            const rightAtG=eqSub(sym(gg),g=>Encodes(g,right.m,right.ps,ts),right.encoded);
            const gm=al(left.encoded),gl=al(rightAtG);
            const mm=app(us(ax({name:'extensionality'}),left.m,right.m),ui(i=>ai(
              ii(M(i,left.m),im=>open(app(ue(ar(gm),i),im),(v,vp)=>app(us(domain,left.g,right.m,i,v),gl,al(vp)))),
              ii(M(i,right.m),im=>open(app(ue(ar(gl),i),im),(v,vp)=>app(us(domain,left.g,left.m,i,v),gm,al(vp))))
            )));
            return use(mm,mm=>{
              const enc=eqSub(sym(mm),m=>Encodes(left.g,m,right.ps,ts),rightAtG);
              const synN=eqSub(sym(nn),n=>Syntax(right.ps,right.m,n),right.syntax);
              const syn=eqSub(sym(mm),m=>Syntax(right.ps,m,left.n),synN);
              const fields=app(us(imported(fieldsUnique),left.g,left.m,left.n,...left.ps,...right.ps,...ts),distinct,left.syntax,syn,left.encoded,enc);
              return use(fields,fields=>{
                let trace=eqSub(sym(nn),n=>Trace(right.ps,right.f,right.m,n,a),right.trace);
                trace=eqSub(sym(mm),m=>Trace(right.ps,right.f,m,left.n,a),trace);
                const current=right.ps.slice();
                for(let i=0;i<5;i++) {
                  const previous=current.slice();
                  trace=eqSub(sym(conj(fields,i,5)),v=>Trace(previous.map((p,j)=>j===i?v:p),right.f,left.m,left.n,a),trace);
                  current[i]=left.ps[i];
                }
                let last=eqSub(sym(nn),n=>Last(right.f,right.m,n,a,right.b,y),right.last);
                last=eqSub(sym(mm),m=>Last(right.f,m,left.n,a,right.b,y),last);
                last=eqSub(sym(bb),b=>Last(right.f,left.m,left.n,a,b,y),last);
                const tm=app(us(imported(memberTransitive),w,left.m),ow,left.mw);
                return app(us(imported(proofs.common_program_last_at_base_unique),left.m,left.n,a,left.b,left.f,right.f,x,y,...left.ps),
                  tm,left.syntax,left.trace,trace,left.last,last);
              });
            });
          });
        }))
      ))));
    })
  )));
  save('positive_evaluation_is_definable',qs(9,(w,a,...vs)=>{
    const ts=vs.slice(0,5),[d,x]=vs.slice(5);
    return ii(Omega(w),ow=>ii(Positive(d,x,a,w,ts),positive=>openPositive(positive,p=>{
      const valid=app(us(imported(syntax.proofs.syntax_trace_is_valid_program),p.f,p.m,p.n,a,...p.ps),p.syntax,p.trace);
      const last=app(us(imported(proofs.last_at_base_is_last_slice),p.f,p.m,p.n,a,p.b,x),p.tuple,p.last);
      const goal=form('definable',a,x),wg=goal[2],ng=inner(wg,w)[2],mg=inner(ng,p.n)[2],fg=inner(mg,p.m)[2][2];
      const trace=ei(fg,p.f,ai(valid,last));
      const length=ei(mg,p.m,ai(p.mw,ai(ai(p.nn,p.mn),trace)));
      return or(goal[1],ei(wg,w,ai(ow,ei(ng,p.n,ai(p.nw,length)))));
    })));
  }));

  save('definable_has_positive_description',qs(10,(w,a,i,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Canonical(w,ts),bank=>ii(TripleCarrier(i,w),alphabet=>ii(RawCarrier(c,w,i,a),carrier=>
      ii(form('definable',a,x),given=>{
        const goal=Output(a,x,w,c,ts);
        return oe(given,goal,empty=>ol(empty,goal[2]),program=>open(program,(v,vp)=>{
          const vw=app(us(imported(proofs.omega_set_unique),v,w),al(vp),ow);
          return open(ar(vp),(n,np)=>open(ar(np),(m,mp)=>open(ar(ar(mp)),(f,fp)=>{
            const nw=eqSub(vw,z=>M(n,z),al(np)),mw=eqSub(vw,z=>M(m,z),al(mp));
            const decorated=app(us(imported(decorate),w,f,m,n,a),ow,mw,al(fp));
            return openMany(decorated,5,(ps,st)=>open(app(us(imported(proofs.last_slice_has_base_tuple),f,m,n,a,x),ar(fp)),(b,bp)=>{
              const covered=app(us(imported(descriptionCoverage),w,i,a,c,m,n,b,...ps,...ts),ow,nw,mw,ar(al(bank)),alphabet,carrier,al(st),al(bp));
              return open(covered,(g,gp)=>open(gp,(d,dp)=>{
                const description=ar(al(dp)),encoded=al(al(al(dp))),dc=ar(dp);
                const evaluated=positiveIntro(d,x,a,w,ts,{n,m,g,b,ps,f,nw,mw,nn:al(al(ar(mp))),mn:ar(al(ar(mp))),
                  description,tuple:al(bp),syntax:al(st),encoded,trace:ar(st),last:ar(bp)});
                return or(goal[1],ei(goal[2],d,ai(dc,evaluated)));
              }));
            }));
          })));
        }));
      })
    ))));
  }));
  save('positive_description_is_definable',qs(9,(w,a,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Output(a,x,w,c,ts),given=>{
      const goal=form('definable',a,x);
      return oe(given,goal,empty=>ol(empty,goal[2]),encoded=>open(encoded,(d,dp)=>
        app(us(imported(proofs.positive_evaluation_is_definable),w,a,...ts,d,x),ow,ar(dp))));
    }));
  }));
  save('definable_iff_positive_description',qs(10,(w,a,i,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Canonical(w,ts),bank=>ii(TripleCarrier(i,w),alphabet=>ii(RawCarrier(c,w,i,a),carrier=>ai(
      app(us(imported(proofs.definable_has_positive_description),w,a,i,c,...ts,x),ow,bank,alphabet,carrier),
      app(us(imported(proofs.positive_description_is_definable),w,a,c,...ts,x),ow)
    )))));
  }));

  function emptyTuple(z,a,empty) {
    const graph=ai(ui(p=>ii(M(p,z),pz=>fe(app(ue(empty,p),pz),some(z,i=>E(v=>form('pair',p,i,v)))))),
      ui(i=>ii(M(i,z),iz=>fe(app(ue(empty,i),iz),E(v=>C(Val(z,i,v),A(u=>I(Val(z,i,u),Q(u,v)))))))));
    const values=ui(i=>ii(M(i,z),iz=>fe(app(ue(empty,i),iz),some(a,v=>Val(z,i,v)))));
    return ai(graph,values);
  }
  save('empty_description_in_raw_carrier',use(imported(tripleExists),exists=>qs(4,(w,i,a,c)=>
    ii(Omega(w),ow=>ii(RawCarrier(c,w,i,a),carrier=>open(al(al(ow)),(z,zp)=>
      open(us(exists,z,z,z),(d,description)=>{
        const iz=ei(FiniteSeq(z,w,i),z,ai(al(zp),emptyTuple(z,i,ar(zp))));
        const az=ei(FiniteSeq(z,w,a),z,ai(al(zp),emptyTuple(z,a,ar(zp))));
        const raw=RawMember(d,w,i,a),gg=inner(raw,z)[2],bg=inner(gg,z)[2];
        const member=ei(raw,z,ai(al(zp),ei(gg,z,ai(iz,ei(bg,z,ai(az,description))))));
        const emptyCode=ei(EmptyCode(d),z,ai(ar(zp),description));
        return ei(some(c,d=>EmptyCode(d)),d,ai(into(carrier,d,member),emptyCode));
      })
    )))
  )));
  save('empty_code_excludes_positive_evaluation',use(imported(tripleInj),inj=>qs(9,(w,a,...vs)=>{
    const ts=vs.slice(0,5),[d,x]=vs.slice(5);
    return ii(EmptyCode(d),empty=>ii(Positive(d,x,a,w,ts),positive=>open(empty,(z,zp)=>openPositive(positive,p=>{
      const equal=app(us(inj,d,z,z,z,p.n,p.g,p.b),ar(zp),p.description);
      const en=eqSub(al(al(equal)),n=>Empty(n),al(zp));
      return open(p.nn,(u,un)=>app(ue(en,u),un));
    }))));
  })));
  save('evaluation_functional',qs(10,(w,a,...vs)=>{
    const ts=vs.slice(0,5),[d,x,y]=vs.slice(5);
    return ii(Omega(w),ow=>ii(Distinct(ts),distinct=>ii(Evaluate(d,x,a,w,ts),ex=>ii(Evaluate(d,y,a,w,ts),ey=>{
      const goal=Q(x,y);
      return oe(ex,goal,lx=>oe(ey,goal,ly=>emptyEqual(x,y,ar(lx),ar(ly)),py=>
        fe(app(us(imported(proofs.empty_code_excludes_positive_evaluation),w,a,...ts,d,y),al(lx),py),goal)),
      px=>oe(ey,goal,ly=>fe(app(us(imported(proofs.empty_code_excludes_positive_evaluation),w,a,...ts,d,x),al(ly),px),goal),
        py=>app(us(imported(proofs.positive_evaluation_functional),w,a,...ts,d,x,y),ow,distinct,px,py)));
    }))));
  }));
  save('definable_has_description_evaluation',qs(10,(w,a,i,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Canonical(w,ts),bank=>ii(TripleCarrier(i,w),alphabet=>ii(RawCarrier(c,w,i,a),carrier=>
      ii(form('definable',a,x),given=>{
        const output=app(us(imported(proofs.definable_has_positive_description),w,a,i,c,...ts,x),ow,bank,alphabet,carrier,given),goal=Evaluated(a,x,w,c,ts);
        return oe(output,goal,empty=>open(app(us(imported(proofs.empty_description_in_raw_carrier),w,i,a,c),ow,carrier),(d,dp)=>
          ei(goal,d,ai(al(dp),ol(ai(ar(dp),empty),Positive(d,x,a,w,ts))))),
          positive=>open(positive,(d,dp)=>ei(goal,d,ai(al(dp),or(C(EmptyCode(d),Empty(x)),ar(dp))))));
      })
    ))));
  }));
  save('description_evaluation_is_definable',qs(9,(w,a,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Evaluated(a,x,w,c,ts),evaluated=>open(evaluated,(d,dp)=>{
      const goal=form('definable',a,x);
      return oe(ar(dp),goal,empty=>ol(ar(empty),goal[2]),positive=>
        app(us(imported(proofs.positive_evaluation_is_definable),w,a,...ts,d,x),ow,positive));
    })));
  }));
  save('definable_iff_description_evaluation',qs(10,(w,a,i,c,...vs)=>{
    const ts=vs.slice(0,5),x=vs[5];
    return ii(Omega(w),ow=>ii(Canonical(w,ts),bank=>ii(TripleCarrier(i,w),alphabet=>ii(RawCarrier(c,w,i,a),carrier=>ai(
      app(us(imported(proofs.definable_has_description_evaluation),w,a,i,c,...ts,x),ow,bank,alphabet,carrier),
      app(us(imported(proofs.description_evaluation_is_definable),w,a,c,...ts,x),ow)
    )))));
  }));
  return {proofs,formulas};
}

export { descriptionEvaluationFormulas, buildDescriptionEvaluation };
