// ACE-03W. Normalized syntax instructions over one shared tag bank.
// All object proofs use the unchanged ZF kernel and pinned syntax formulas.
import { kernel } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildInstructionTags } from './instruction_tags.mjs';
import { buildSyntaxTraceAdequacy } from './syntax_trace_adequacy.mjs';
import { buildFiniteWitnessSelection } from './finite_witness_selection.mjs';
import { buildOmegaWellOrder } from './omega_well_order.mjs';

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

function instructionLanguage(defs) {
  const L=language(defs);
  const {M,Q,C,I,O,N,A,E,named,db,form,Empty,Succ,all,some}=L;
  const ands=xs=>xs.reduce(C),ors=xs=>xs.reduce(O),B=(p,q)=>C(I(p,q),I(q,p));
  const sf=buildSyntaxTraceAdequacy(defs).formulas,tf=buildInstructionTags(defs).formulas;
  const Pair=(p,x,y)=>form('pair',p,x,y),Val=(g,k,c)=>form('val',g,k,c),Graph=(g,m)=>form('graph',g,m);
  const Tuple=(g,m,a)=>form('tuple',g,m,a);
  const Triple=(c,t,i,j)=>E(d=>C(Pair(d,i,j),Pair(c,t,d)));
  const Instr=(op,ps,k,i,j)=>op===2?Val(ps[op],k,i):E(d=>C(Val(ps[op],k,d),Pair(d,i,j)));
  const Syntax=(ps,m,n)=>named(sf.syntax,[m,n,...ps]);
  const Choices=(ps,k,n)=>named(sf.choices,[k,n,...ps]);
  const Distinct=ts=>named(tf.distinct,ts);
  const Members=(w,ts)=>ands(ts.map(t=>M(t,w)));
  const FirstFive=ts=>C(Empty(ts[0]),ands(ts.slice(0,4).map((t,i)=>Succ(t,ts[i+1]))));
  const Row=(ps,ts,k,c)=>ors(Array.from({length:5},(_,op)=>op===2?
    E(i=>C(Instr(op,ps,k,i),Triple(c,ts[op],i,i))):
    E(i=>E(j=>C(Instr(op,ps,k,i,j),Triple(c,ts[op],i,j))))));
  const Encodes=(g,m,ps,ts)=>C(Graph(g,m),all(m,k=>A(c=>B(Val(g,k,c),Row(ps,ts,k,c)))));
  const Selected=(g,m,ps,ts)=>C(Graph(g,m),all(m,k=>A(c=>I(Val(g,k,c),Row(ps,ts,k,c)))));
  const Carrier=(a,w)=>A(c=>B(M(c,a),some(w,t=>some(w,i=>some(w,j=>Triple(c,t,i,j))))));
  const InstructionAgreement=(p,q,m)=>all(m,k=>ands(Array.from({length:5},(_,op)=>op===2?
    A(i=>B(Instr(op,p,k,i),Instr(op,q,k,i))):
    A(i=>A(j=>B(Instr(op,p,k,i,j),Instr(op,q,k,i,j)))))));
  const ts=['t0','t1','t2','t3','t4'],ps=['p0','p1','p2','p3','p4'];
  const formulas={
    triple:db(Triple('c','t','i','j'),['c','t','i','j']),
    triple_carrier:db(Carrier('a','w'),['a','w']),
    row:db(Row(ps,ts,'k','c'),['k','c',...ps,...ts]),
    encodes:db(Encodes('g','m',ps,ts),['g','m',...ps,...ts]),
    first_five:db(FirstFive(ts),ts),tag_members:db(Members('w',ts),['w',...ts]),
    distinct:tf.distinct
  };
  return {...L,ands,ors,B,Pair,Val,Graph,Tuple,Triple,Instr,Syntax,Choices,Distinct,Members,FirstFive,Row,Encodes,Selected,Carrier,InstructionAgreement,formulas};
}

function syntaxInstructionCodeFormulas(defs) {return instructionLanguage(defs).formulas;}

function buildSyntaxInstructionCodes(defs) {
  const {M,Q,F,I,C,N,A,E,db,replace,ui,ii,al,ar,ai,ue,us,app,ref,fe,ei,open,oe,ol,or,eqSub,sym,use,ax,from,into,imported,
    form,Empty,Succ,Omega,all,some,Trans,qs,compiled,ands,B,Pair,Val,Graph,Tuple,Triple,Instr,Syntax,Choices,Distinct,Members,FirstFive,
    Row,Encodes,Selected,Carrier,InstructionAgreement,formulas}=instructionLanguage(defs);
  const finite=buildF(defs,'relations'),earlier=buildE(defs,true),omega=buildOmegaWellOrder(defs),tags=buildInstructionTags(defs);
  const proofs={},save=(name,p)=>{proofs[name]=compiled(p);return proofs[name];};
  const ais=xs=>xs.reduce(ai),conj=(p,i,n)=>n===1?p:i===n-1?ar(p):conj(al(p),i,n-1);
  const leaf=(p,i,n)=>n===1?p:i===n-1?p[2]:leaf(p[1],i,n-1);
  const inner=(p,x)=>replace(p[2],p[1],x);
  const exs=(n,fn,vs=[])=>vs.length===n?fn(vs):E(x=>exs(n,fn,[...vs,x]));
  const pack=(goal,xs,p)=>xs.length===0?p:ei(goal,xs[0],pack(inner(goal,xs[0]),xs.slice(1),p));
  function cases(p,goal,fs){return fs.length===1?fs[0](p):oe(p,goal,q=>cases(q,goal,fs.slice(0,-1)),fs.at(-1));}
  function inject(p,i,n,q){return n===1?q:i===n-1?or(p[1],q):ol(inject(p[1],i,n-1,q),p[2]);}
  function openRow(op,p,fn){return open(p,(i,ip)=>op===2?fn(i,i,al(ip),ar(ip)):
    open(ip,(j,jp)=>fn(i,j,al(jp),ar(jp))));}
  function openChoice(op,p,fn){return open(p,(i,ip)=>op===2?fn(i,i,al(ip),al(ip),al(ar(ip)),ar(ar(ip))):
    open(ar(ip),(j,jp)=>fn(i,j,al(ip),al(jp),al(ar(jp)),ar(ar(jp)))));}
  function rowIntro(ps,ts,k,c,op,i,j,instruction,code) {
    const goal=Row(ps,ts,k,c),arm=leaf(goal,op,5);
    const body=op===2?ai(instruction,code):ei(inner(arm,i),j,ai(instruction,code));
    return inject(goal,op,5,ei(arm,i,body));
  }
  function contradiction(only,op,q,i,j,instruction) {
    const position=1+q-(q>op?1:0),rule=conj(only,position,5);
    return app(q===2?ue(rule,i):us(rule,i,j),instruction);
  }
  function rowAtChoice(ps,ts,k,c,op,i,j,only,row) {
    const goal=Triple(c,ts[op],i,j);
    return cases(row,goal,Array.from({length:5},(_,q)=>arm=>openRow(q,arm,(u,v,instruction,code)=>{
      if(q!==op)return fe(contradiction(only,op,q,u,v,instruction),goal);
      const same=app(q===2?ue(conj(only,0,5),u):us(conj(only,0,5),u,v),instruction);
      if(q===2)return eqSub(same,z=>Triple(c,ts[q],z,z),code);
      const atI=eqSub(al(same),z=>Triple(c,ts[q],z,v),code);
      return eqSub(ar(same),z=>Triple(c,ts[q],i,z),atI);
    })));
  }

  save('canonical_first_five_exist',ui(w=>ii(Omega(w),ow=>
    open(al(al(ow)),(zero,zp)=>{
      const goal=exs(5,ts=>C(C(FirstFive(ts),Members(w,ts)),Distinct(ts)));
      function next(ts,inside,steps) {
        if(ts.length===5) {
          const chain=ais(steps),distinct=app(us(imported(tags.proofs.successor_chain_tags_distinct),...ts),chain);
          return pack(goal,ts,ai(ai(ai(ar(zp),chain),ais(inside)),distinct));
        }
        const k=ts.length-1;
        return open(app(ue(ar(al(ow)),ts[k]),inside[k]),(t,tp)=>next([...ts,t],[...inside,al(tp)],[...steps,ar(tp)]));
      }
      return next([zero],[al(zp)],[]);
    })
  )));
  save('canonical_first_five_unique',use(imported(omega.proofs.successor_set_unique),unique=>qs(10,(...vs)=>{
    const ts=vs.slice(0,5),us0=vs.slice(5);
    return ii(FirstFive(ts),tp=>ii(FirstFive(us0),up=>{
      const zero=app(us(ax({name:'extensionality'}),ts[0],us0[0]),ui(x=>ai(
        ii(M(x,ts[0]),xt=>fe(app(ue(al(tp),x),xt),M(x,us0[0]))),
        ii(M(x,us0[0]),xu=>fe(app(ue(al(up),x),xu),M(x,ts[0]))))));
      function next(eqs) {
        if(eqs.length===5)return ais(eqs);
        const i=eqs.length-1,left=conj(ar(tp),i,4),right=conj(ar(up),i,4);
        const moved=eqSub(eqs[i],z=>Succ(z,ts[i+1]),left);
        return use(app(us(unique,us0[i],ts[i+1],us0[i+1]),moved,right),eq=>next([...eqs,eq]));
      }
      return use(zero,eq=>next([eq]));
    }));
  })));

  save('normalized_triple_exists',use(imported(finite.pair_exists),exists=>qs(3,(t,i,j)=>
    open(us(exists,i,j),(d,dp)=>open(us(exists,t,d),(c,cp)=>ei(E(x=>Triple(x,t,i,j)),c,
      ei(Triple(c,t,i,j),d,ai(dp,cp)))))
  )));
  save('normalized_triple_unique',use(imported(earlier.ordered_pair_unique),unique=>qs(5,(c,d,t,i,j)=>
    ii(Triple(c,t,i,j),cp=>ii(Triple(d,t,i,j),dp=>open(cp,(u,up)=>open(dp,(v,vp)=>{
      const uv=app(us(unique,i,j,u,v),al(up),al(vp));
      const dAtU=eqSub(sym(uv),z=>Pair(d,t,z),ar(vp));
      return app(us(unique,t,u,c,d),ar(up),dAtU);
    }))))
  )));
  save('normalized_triple_injective',use(imported(finite.pair_injective),inj=>qs(7,(c,t,i,j,s,u,v)=>
    ii(Triple(c,t,i,j),cp=>ii(Triple(c,s,u,v),dp=>open(cp,(a,ap)=>open(dp,(b,bp)=>{
      const outer=app(us(inj,c,t,a,s,b),ar(ap),ar(bp));
      const atB=eqSub(ar(outer),z=>Pair(z,i,j),al(ap));
      const operands=app(us(inj,b,i,j,u,v),atB,al(bp));
      return ai(ai(al(outer),al(operands)),ar(operands));
    }))))
  )));

  save('syntax_row_code_total',use(imported(proofs.normalized_triple_exists),exists=>qs(12,(m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Syntax(ps,m,n),syntax=>ui(k=>ii(M(k,m),km=>{
      const goal=E(c=>Row(ps,ts,k,c)),choice=app(ue(ar(syntax),k),km);
      return cases(choice,goal,Array.from({length:5},(_,op)=>arm=>openChoice(op,arm,(i,j,_si,_sj,instruction)=>
        open(us(exists,ts[op],i,j),(c,code)=>ei(goal,c,rowIntro(ps,ts,k,c,op,i,j,instruction,code)))
      )));
    })));
  })));
  save('syntax_row_code_functional',use(imported(proofs.normalized_triple_unique),unique=>qs(12,(m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Syntax(ps,m,n),syntax=>ui(k=>ii(M(k,m),km=>qs(2,(c,d)=>
      ii(Row(ps,ts,k,c),cr=>ii(Row(ps,ts,k,d),dr=>{
        const choice=app(ue(ar(syntax),k),km),goal=Q(c,d);
        return cases(choice,goal,Array.from({length:5},(_,op)=>arm=>openChoice(op,arm,(i,j,_si,_sj,_instruction,only)=>
          app(us(unique,c,d,ts[op],i,j),rowAtChoice(ps,ts,k,c,op,i,j,only,cr),rowAtChoice(ps,ts,k,d,op,i,j,only,dr))
        )));
      }))
    ))));
  })));

  const selected=buildFiniteWitnessSelection(defs,formulas.row,10,finite.graph_append_exists);
  for(const [name,p] of Object.entries(selected.proofs))proofs['syntax_'+name]=p;

  save('selected_syntax_rows_are_exact',qs(13,(g,m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Syntax(ps,m,n),syntax=>ii(Selected(g,m,ps,ts),selected=>{
      const functional=app(us(imported(proofs.syntax_row_code_functional),m,n,...ps,...ts),syntax);
      return use(functional,fn=>ai(al(selected),ui(k=>ii(M(k,m),km=>ui(c=>ai(
        ii(Val(g,k,c),gc=>app(ue(app(ue(ar(selected),k),km),c),gc)),
        ii(Row(ps,ts,k,c),row=>open(app(ue(ar(al(selected)),k),km),(d,dp)=>{
          const dr=app(ue(app(ue(ar(selected),k),km),d),al(dp));
          const dc=app(us(app(ue(fn,k),km),d,c),dr,row);
          return eqSub(dc,z=>Val(g,k,z),al(dp));
        }))
      ))))));
    }));
  }));
  save('finite_syntax_has_normalized_code',qs(13,(w,m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Omega(w),ow=>ii(M(m,w),mw=>ii(Syntax(ps,m,n),syntax=>{
      const total=app(us(imported(proofs.syntax_row_code_total),m,n,...ps,...ts),syntax);
      const selected=app(us(imported(proofs.syntax_finite_witness_selection),...ps,...ts,w,m),ow,mw,total);
      return open(selected,(g,gp)=>ei(E(h=>Encodes(h,m,ps,ts)),g,
        app(us(imported(proofs.selected_syntax_rows_are_exact),g,m,n,...ps,...ts),syntax,gp)));
    })));
  }));

  save('normalized_code_is_triple_tuple',qs(15,(w,a,g,m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Omega(w),ow=>ii(M(n,w),nw=>ii(M(m,w),mw=>ii(Members(w,ts),members=>
      ii(Carrier(a,w),carrier=>ii(Syntax(ps,m,n),syntax=>ii(Encodes(g,m,ps,ts),encoded=>
        use(app(ue(imported(omega.proofs.omega_transitive),w),ow),tw=>{
          const bound=(b,bw,x,xb)=>app(ue(app(ue(tw,b),bw),x),xb);
          const values=ui(k=>ii(M(k,m),km=>open(app(ue(ar(al(encoded)),k),km),(c,cp)=>{
            const row=app(al(ue(app(ue(ar(encoded),k),km),c)),al(cp));
            const choices=app(ue(ar(syntax),k),km),goal=some(a,x=>Val(g,k,x));
            return cases(choices,goal,Array.from({length:5},(_,op)=>arm=>openChoice(op,arm,(i,j,si,sj,_instruction,only)=>{
              const kw=bound(m,mw,k,km),iw=op<2?bound(n,nw,i,si):bound(k,kw,i,si);
              const jw=op===2?iw:op===3?bound(k,kw,j,sj):bound(n,nw,j,sj);
              const code=rowAtChoice(ps,ts,k,c,op,i,j,only,row),t=ts[op];
              const insideJ=ei(some(w,v=>Triple(c,t,i,v)),j,ai(jw,code));
              const insideI=ei(some(w,u=>some(w,v=>Triple(c,t,u,v))),i,ai(iw,insideJ));
              const insideT=ei(some(w,s=>some(w,u=>some(w,v=>Triple(c,s,u,v)))),t,ai(conj(members,op,5),insideI));
              const ca=into(carrier,c,insideT);
              return ei(goal,c,ai(ca,al(cp)));
            })));
          })));
          return ai(al(encoded),values);
        })
      )))
    ))));
  }));
  save('finite_syntax_code_tuple_exists',qs(14,(w,a,m,n,...vs)=>{
    const ps=vs.slice(0,5),ts=vs.slice(5);
    return ii(Omega(w),ow=>ii(M(n,w),nw=>ii(M(m,w),mw=>ii(Members(w,ts),members=>
      ii(Carrier(a,w),carrier=>ii(Syntax(ps,m,n),syntax=>
        open(app(us(imported(proofs.finite_syntax_has_normalized_code),w,m,n,...ps,...ts),ow,mw,syntax),(g,encoded)=>
          ei(E(h=>C(Encodes(h,m,ps,ts),Tuple(h,m,a))),g,ai(encoded,
            app(us(imported(proofs.normalized_code_is_triple_tuple),w,a,g,m,n,...ps,...ts),ow,nw,mw,members,carrier,syntax,encoded)))
        )
      ))
    ))));
  }));

  function distinctContradiction(distinct,op,q,equal) {
    let p=0;
    for(let i=0;i<5;i++)for(let j=i+1;j<5;j++,p++)if(i===Math.min(op,q)&&j===Math.max(op,q))
      return app(conj(distinct,p,10),op<q?equal:sym(equal));
    throw Error('same opcode in tag contradiction');
  }
  save('normalized_graph_instruction_agreement',use(imported(proofs.normalized_triple_exists),exists=>
    use(imported(proofs.normalized_triple_injective),inj=>qs(17,(g,m,...vs)=>{
      const ps=vs.slice(0,5),qs0=vs.slice(5,10),ts=vs.slice(10);
      return ii(Distinct(ts),distinct=>ii(Encodes(g,m,ps,ts),left=>ii(Encodes(g,m,qs0,ts),right=>
        ui(k=>ii(M(k,m),km=>ais(Array.from({length:5},(_,op)=>{
          function move(source,target,se,te,i,j,instruction) {
            const goal=Instr(op,target,k,i,j);
            return open(us(exists,ts[op],i,j),(c,code)=>{
              const row=rowIntro(source,ts,k,c,op,i,j,instruction,code);
              const value=app(ar(ue(app(ue(ar(se),k),km),c)),row);
              const other=app(al(ue(app(ue(ar(te),k),km),c)),value);
              return cases(other,goal,Array.from({length:5},(_,q)=>arm=>openRow(q,arm,(u,v,ins,otherCode)=>{
                const same=app(us(inj,c,ts[op],i,j,ts[q],u,v),code,otherCode);
                if(q!==op)return fe(distinctContradiction(distinct,op,q,al(al(same))),goal);
                if(op===2)return eqSub(sym(ar(al(same))),z=>Instr(op,target,k,z),ins);
                const atI=eqSub(sym(ar(al(same))),z=>Instr(op,target,k,z,v),ins);
                return eqSub(sym(ar(same)),z=>Instr(op,target,k,i,z),atI);
              })));
            });
          }
          function at(i,j){return ai(
            ii(Instr(op,ps,k,i,j),p=>move(ps,qs0,left,right,i,j,p)),
            ii(Instr(op,qs0,k,i,j),p=>move(qs0,ps,right,left,i,j,p))
          );}
          return op===2?ui(i=>at(i,i)):qs(2,at);
        }))))
      )));
    }))
  ));
  save('normalized_graph_determines_syntax_fields',use(imported(earlier.ordered_pair_unique),pairUnique=>qs(18,(g,m,n,...vs)=>{
    const ps=vs.slice(0,5),qs0=vs.slice(5,10),ts=vs.slice(10);
    return ii(Distinct(ts),distinct=>ii(Syntax(ps,m,n),sp=>ii(Syntax(qs0,m,n),sq=>
      ii(Encodes(g,m,ps,ts),ep=>ii(Encodes(g,m,qs0,ts),eq=>
        use(app(us(imported(proofs.normalized_graph_instruction_agreement),g,m,...ps,...qs0,...ts),distinct,ep,eq),agreement=>{
          function transfer(op,source,target,syntax,p,pm,reverse) {
            const shape=conj(al(syntax),op,5);
            return open(app(ue(shape,p),pm),(k,kp)=>open(ar(kp),(d,dp)=>{
              const sourceValue=ei(Val(source[op],k,d),p,ai(pm,al(dp)));
              const agree=conj(app(ue(agreement,k),al(kp)),op,5);
              function finish(value,pair) {
                return open(value,(q,qp)=>{
                  const pq=app(us(pairUnique,k,d,p,q),al(dp),pair(q,ar(qp)));
                  return eqSub(sym(pq),z=>M(z,target[op]),al(qp));
                });
              }
              if(op===2) {
                const targetValue=app((reverse?ar:al)(ue(agree,d)),sourceValue);
                return finish(targetValue,(_q,pair)=>pair);
              }
              return open(ar(dp),(i,ip)=>open(ip,(j,jp)=>{
                const sourceInstruction=ei(Instr(op,source,k,i,j),d,ai(sourceValue,al(al(jp))));
                const targetInstruction=app((reverse?ar:al)(us(agree,i,j)),sourceInstruction);
                return open(targetInstruction,(e,ep)=>{
                  const de=app(us(pairUnique,i,j,d,e),al(al(jp)),ar(ep));
                  return finish(al(ep),(q,pair)=>eqSub(sym(de),z=>Pair(q,k,z),pair));
                });
              }));
            }));
          }
          return ais(Array.from({length:5},(_,op)=>app(us(ax({name:'extensionality'}),ps[op],qs0[op]),
            ui(p=>ai(ii(M(p,ps[op]),pm=>transfer(op,ps,qs0,sp,p,pm,false)),
              ii(M(p,qs0[op]),pm=>transfer(op,qs0,ps,sq,p,pm,true)))))));
        })
      ))
    )));
  })));

  return {proofs,formulas};
}

export { syntaxInstructionCodeFormulas, buildSyntaxInstructionCodes };
