// ACE-03U: uniform deterministic evaluation for decoded instruction fields.
// Pure object proofs; the pinned Def and executable kernel are unchanged.
import { kernel } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';

function buildSyntaxTraceAdequacy(defs) {
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
  const ands=xs=>xs.reduce(C), ors=xs=>xs.reduce(O);
  const form=(name,...args)=>named(defs[name],args);
  const V=(f,k,r)=>form('val',f,k,r), G=(f,m)=>form('graph',f,m);
  const Pair=(p,x,y)=>form('pair',p,x,y);
  const trans=m=>all(m,x=>all(x,y=>M(y,m)));
  const OPS=['eq','mem','neg','and','exists'];
  const SEM=['relEq','relMem','relNeg','relAnd','relEx'];
  const proofs={};
  const save=(name,p)=>{proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];};
  const conj=(p,i,n)=>n===1?p:i===n-1?ar(p):conj(al(p),i,n-1);
  function cases(p,goal,fs){return fs.length===1?fs[0](p):oe(p,goal,q=>cases(q,goal,fs.slice(0,-1)),fs.at(-1));}
  function leaf(p,i,n){return n===1?p:i===n-1?p[2]:leaf(p[1],i,n-1);}
  function inject(p,i,n,q){return n===1?q:i===n-1?or(p[1],q):ol(inject(p[1],i,n-1,q),p[2]);}
  const inner=(p,x)=>replace(p[2],p[1],x)[2];
  const someIn=(goal,x,xs,p)=>ei(goal,x,ai(xs,p));

  // Binary instructions are encoded k -> <i,j>; negation is k -> i.
  // The fields occur in the fixed order eq, mem, neg, and, exists.
  const Instr=(op,fields,k,i,j)=>op===2?V(fields[op],k,i):
    E(c=>C(V(fields[op],k,c),Pair(c,i,j)));
  const scopes=(op,k,n)=>op<2?[n,n]:op===3?[k,k]:[k,n];
  const noInstruction=(op,fields,k)=>op===2?A(i=>N(Instr(op,fields,k,i))):
    A(i=>A(j=>N(Instr(op,fields,k,i,j))));
  function only(op,fields,k,i,j) {
    const unique=op===2?A(u=>I(Instr(op,fields,k,u),Q(u,i))):
      A(u=>A(v=>I(Instr(op,fields,k,u,v),C(Q(u,i),Q(v,j)))));
    return ands([unique,...OPS.map((_,q)=>q).filter(q=>q!==op).map(q=>noInstruction(q,fields,k))]);
  }
  function choice(op,fields,k,n) {
    if(op===2)return some(k,i=>C(Instr(op,fields,k,i),only(op,fields,k,i)));
    const [s,t]=scopes(op,k,n);
    return some(s,i=>some(t,j=>C(Instr(op,fields,k,i,j),only(op,fields,k,i,j))));
  }
  const Choices=(fields,k,n)=>ors(OPS.map((_,op)=>choice(op,fields,k,n)));
  function fieldShape(op,fields,m,n) {
    return all(fields[op],p=>some(m,k=>E(data=>C(Pair(p,k,data),
      op===2?M(data,k):E(i=>E(j=>{
        const [s,t]=scopes(op,k,n);
        return C(C(Pair(data,i,j),M(i,s)),M(j,t));
      }))))));
  }
  const Syntax=(fields,m,n)=>C(ands(OPS.map((_,op)=>fieldShape(op,fields,m,n))),
    all(m,k=>Choices(fields,k,n)));
  function semanticRule(op,fields,f,k,r,n,a) {
    if(op<2)return A(i=>A(j=>I(Instr(op,fields,k,i,j),form(SEM[op],r,n,a,i,j))));
    if(op===2)return A(i=>I(Instr(op,fields,k,i),E(p=>C(V(f,i,p),form('relNeg',r,p,n,a)))));
    if(op===3)return A(i=>A(j=>I(Instr(op,fields,k,i,j),
      E(p=>E(q=>C(C(V(f,i,p),V(f,j,q)),form('relAnd',r,p,q)))))));
    return A(i=>A(j=>I(Instr(op,fields,k,i,j),E(p=>C(V(f,i,p),form('relEx',r,p,n,a,j))))));
  }
  const Rules=(fields,f,k,r,n,a)=>ands(OPS.map((_,op)=>semanticRule(op,fields,f,k,r,n,a)));
  const Trace=(fields,f,m,n,a)=>C(G(f,m),all(m,k=>A(r=>I(V(f,k,r),Rules(fields,f,k,r,n,a)))));
  const AgreeAt=(f,g,k)=>A(r=>A(s=>I(V(f,k,r),I(V(g,k,s),Q(r,s)))));
  const ValuesAgree=(f,g,m)=>all(m,k=>AgreeAt(f,g,k));
  function getRules(tr,k,km,r,fr){return app(ue(app(ue(ar(tr),k),km),r),fr);}
  function getChoices(syn,k,km){return app(ue(ar(syn),k),km);}
  function openChoice(op,p,fn) {
    return open(p,(i,ip)=>op===2?fn(i,null,al(ip),null,al(ar(ip))):
      open(ar(ip),(j,jp)=>fn(i,j,al(ip),al(jp),al(ar(jp)))));
  }
  function sameExtension(r,s,rp,sp) {
    return app(us(ax({name:'extensionality'}),r,s),ui(x=>ai(
      ii(M(x,r),xr=>into(sp,x,from(rp,x,xr))),
      ii(M(x,s),xs=>into(rp,x,from(sp,x,xs))))));
  }

  for(const [op,arity] of [[0,5],[1,5],[2,4],[3,3],[4,5]]) {
    save(OPS[op]+'_relation_unique',qs(arity+1,(r,s,...args)=>
      ii(form(SEM[op],r,...args),rp=>ii(form(SEM[op],s,...args),sp=>sameExtension(r,s,rp,sp)))));
  }
  save('slice_unique',qs(7,(x,y,r,a,n,z,b)=>
    ii(form('slice',x,r,a,n,z,b),xp=>ii(form('slice',y,r,a,n,z,b),yp=>sameExtension(x,y,xp,yp)))));

  // The actual five-way syntax/execution interface entails the exact
  // entry disjunction used by the unchanged pinned Def predicate.
  save('instruction_execution_entry',qs(10,(f,k,r,n,a,...fields)=>
    ii(Choices(fields,k,n),choices=>ii(Rules(fields,f,k,r,n,a),rules=>{
      const target=form('entry',f,k,r,n,a);
      return cases(choices,target,OPS.map((_,op)=>p=>openChoice(op,p,(i,j,si,sj,instruction)=>{
        const rule=conj(rules,op,5),sem=app(op===2?ue(rule,i):us(rule,i,j),instruction);
        const arm=leaf(target,op,5);
        const body=op===2?sem:someIn(inner(arm,i),j,sj,sem);
        return inject(target,op,5,someIn(arm,i,si,body));
      })));
    }))));

  save('syntax_trace_is_valid_program',qs(9,(f,m,n,a,...fields)=>
    ii(Syntax(fields,m,n),syntax=>ii(Trace(fields,f,m,n,a),trace=>{
      const entry=imported(proofs.instruction_execution_entry);
      const steps=ui(k=>ii(M(k,m),km=>open(app(ue(ar(al(trace)),k),km),(r,rp)=>{
        const goal=E(s=>C(V(f,k,s),form('entry',f,k,s,n,a)));
        const rules=getRules(trace,k,km,r,al(rp)),choices=getChoices(syntax,k,km);
        const en=app(us(entry,f,k,r,n,a,...fields),choices,rules);
        return ei(goal,r,ai(al(rp),en));
      })));
      return ai(al(trace),steps);
    }))));

  // Uniform induction over an arbitrary transitive set, instantiated with
  // equality of all paired trace values. Foundation selects a minimal bad row.
  function boundedInduction(property,paramCount) {
    function quantify(ps) {
      if(ps.length<paramCount)return ui(p=>quantify([...ps,p]));
      const PAt=x=>named(property,[x,...ps]);
      const step=m=>A(k=>I(M(k,m),I(A(i=>I(M(i,k),PAt(i))),PAt(k))));
      return ui(m=>ii(trans(m),tm=>ii(step(m),st=>ui(k=>ii(M(k,m),km=>{
        const sep=separation(m,ps,x=>N(PAt(x)));
        return P(PAt(k),(e,h)=>['dne',ii(N(PAt(k)),badK=>
          open(sep,(bad,sp)=>{
            const kb=into(sp,k,ai(km,badK));
            const ne=E(x=>M(x,bad));
            return open(app(ue(ax({name:'foundation'}),bad),ei(ne,k,kb)),(y,yp)=>{
              const info=from(sp,y,al(yp)),ym=al(info),ny=ar(info);
              const ih=ui(i=>ii(M(i,y),iy=>{
                const im=app(ue(app(ue(tm,y),ym),i),iy);
                const neg=ii(N(PAt(i)),ni=>app(app(ue(ar(yp),i),iy),into(sp,i,ai(im,ni))));
                return P(PAt(i),(ee,hh)=>['dne',neg.emit(ee,hh)]);
              }));
              return app(ny,app(app(ue(st,y),ym),ih));
            });
          })).emit(e,h)]);
      })))));
    }
    return quantify([]);
  }
  const inductionProperty=db(AgreeAt('f','g','k'),['k','f','g']);
  save('trace_value_induction',boundedInduction(inductionProperty,2));

  save('common_program_trace_values_unique',qs(10,(m,n,a,f,g,...fields)=>
    ii(trans(m),tm=>ii(Syntax(fields,m,n),syntax=>
    ii(Trace(fields,f,m,n,a),tf=>ii(Trace(fields,g,m,n,a),tg=>{
      const step=ui(k=>ii(M(k,m),km=>ii(A(i=>I(M(i,k),AgreeAt(f,g,i))),ih=>
        ui(r=>ui(s=>ii(V(f,k,r),fr=>ii(V(g,k,s),gs=>{
          const choices=getChoices(syntax,k,km),rf=getRules(tf,k,km,r,fr),rg=getRules(tg,k,km,s,gs);
          const goal=Q(r,s);
          const prev=(i,ik,p,q,fp,gq)=>app(us(app(ue(ih,i),ik),p,q),fp,gq);
          return cases(choices,goal,OPS.map((_,op)=>ch=>openChoice(op,ch,(i,j,ik,jk,instruction)=>{
            const pf=app(op===2?ue(conj(rf,op,5),i):us(conj(rf,op,5),i,j),instruction);
            const pg=app(op===2?ue(conj(rg,op,5),i):us(conj(rg,op,5),i,j),instruction);
            const unique=imported(proofs[OPS[op]+'_relation_unique']);
            if(op<2)return app(us(unique,r,s,n,a,i,j),pf,pg);
            if(op===2||op===4)return open(pf,(p,fp)=>open(pg,(q,gq)=>{
              const eq=prev(i,ik,p,q,al(fp),al(gq));
              const rhs=eqSub(sym(eq),z=>op===2?form('relNeg',s,z,n,a):form('relEx',s,z,n,a,j),ar(gq));
              return app(us(unique,r,s,p,n,a,...(op===4?[j]:[])),ar(fp),rhs);
            }));
            return open(pf,(p,pp)=>open(pp,(q,pq)=>open(pg,(u,up)=>open(up,(v,uv)=>{
              const ep=prev(i,ik,p,u,al(al(pq)),al(al(uv)));
              const eq=prev(j,jk,q,v,ar(al(pq)),ar(al(uv)));
              const pFixed=eqSub(sym(ep),z=>form('relAnd',s,z,v),ar(uv));
              const fixed=eqSub(sym(eq),z=>form('relAnd',s,p,z),pFixed);
              return app(us(unique,r,s,p,q),ar(pq),fixed);
            }))));
          })));
        })))))));
      return app(us(imported(proofs.trace_value_induction),f,g,m),tm,step);
    }))))));

  const graphExt=buildE(defs,true).graph_extensionality;
  proofs.exact_graph_extensionality=graphExt;
  save('common_program_trace_graphs_equal',qs(10,(m,n,a,f,g,...fields)=>
    ii(trans(m),tm=>ii(Syntax(fields,m,n),syntax=>
    ii(Trace(fields,f,m,n,a),tf=>ii(Trace(fields,g,m,n,a),tg=>{
      const agree=app(us(imported(proofs.common_program_trace_values_unique),m,n,a,f,g,...fields),tm,syntax,tf,tg);
      return use(agree,av=>{
        const equiv=ui(k=>ii(M(k,m),km=>ui(r=>{
          const sameAt=app(ue(av,k),km);
          const forward=ii(V(f,k,r),fr=>open(app(ue(ar(al(tg)),k),km),(s,gs)=>{
            const rs=app(us(sameAt,r,s),fr,al(gs));
            return eqSub(sym(rs),x=>V(g,k,x),al(gs));
          }));
          const reverse=ii(V(g,k,r),gr=>open(app(ue(ar(al(tf)),k),km),(s,fs)=>{
            const sr=app(us(sameAt,s,r),al(fs),gr);
            return eqSub(sr,x=>V(f,k,x),al(fs));
          }));
          return ai(forward,reverse);
        })));
        return app(us(imported(graphExt),f,g,m),al(tf),al(tg),equiv);
      });
    }))))));

  save('common_program_slice_agreement',qs(10,(m,n,a,f,g,...fields)=>
    ii(trans(m),tm=>ii(Syntax(fields,m,n),syntax=>
    ii(Trace(fields,f,m,n,a),tf=>ii(Trace(fields,g,m,n,a),tg=>{
      const agree=app(us(imported(proofs.common_program_trace_values_unique),m,n,a,f,g,...fields),tm,syntax,tf,tg);
      return use(agree,av=>ui(k=>ii(M(k,m),km=>qs(6,(r,s,x,y,z,b)=>
        ii(V(f,k,r),fr=>ii(V(g,k,s),gs=>ii(form('slice',x,r,a,n,z,b),sx=>
          ii(form('slice',y,s,a,n,z,b),sy=>{
            const rs=app(us(app(ue(av,k),km),r,s),fr,gs);
            const syR=eqSub(sym(rs),q=>form('slice',y,q,a,n,z,b),sy);
            return app(us(imported(proofs.slice_unique),x,y,r,a,n,z,b),sx,syR);
          }))))))));
    }))))));

  return {proofs,formulas:{
    syntax:db(Syntax(['e','v','q','c','x'],'m','n'),['m','n','e','v','q','c','x']),
    trace:db(Trace(['e','v','q','c','x'],'f','m','n','a'),['f','m','n','a','e','v','q','c','x']),
    choices:db(Choices(['e','v','q','c','x'],'k','n'),['k','n','e','v','q','c','x']),
    rules:db(Rules(['e','v','q','c','x'],'f','k','r','n','a'),['f','k','r','n','a','e','v','q','c','x']),
    values_agree:db(ValuesAgree('f','g','m'),['f','g','m'])
  }};
}

export { buildSyntaxTraceAdequacy };
