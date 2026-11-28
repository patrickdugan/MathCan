// ACE-03V. Exact tagged witnesses for the five pinned entry clauses.
import { kernel, same, scoped } from './zf_interface.mjs';
import { buildF } from './finite_witnesses.mjs';
import { buildFiniteWitnessSelection } from './finite_witness_selection.mjs';

function instructionWitnessFormulas(defs) {
  let serial=0;
  const fresh=()=>`iw${serial++}`;
  const M=(a,b)=>['M',a,b],C=(p,q)=>['&',p,q],I=(p,q)=>['>',p,q];
  const bind=(op,fn)=>{const x=fresh();return [op,x,fn(x)];};
  const A=fn=>bind('A',fn),E=fn=>bind('E',fn),some=(s,fn)=>E(x=>C(M(x,s),fn(x)));
  function named(p,env) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='M'||op==='=')return [op,env[a],env[b]];
    if(op==='A'||op==='E'){const x=fresh();return [op,x,named(a,[x,...env])];}
    return [op,named(a,env),named(b,env)];
  }
  function db(p,env) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='M'||op==='='){
      const i=env.indexOf(a),j=env.indexOf(b);
      if(i<0||j<0)throw Error('instruction interface free variable');
      return [op,i,j];
    }
    if(op==='A'||op==='E')return [op,db(b,[a,...env])];
    return [op,db(a,env),db(b,env)];
  }
  const form=(name,...args)=>named(defs[name],args);
  const Val=(f,k,r)=>form('val',f,k,r),Pair=(p,x,y)=>form('pair',p,x,y);
  const binary=(c,tag,i,j)=>E(d=>C(Pair(d,i,j),Pair(c,tag,d)));
  const witness=(c,f,k,r,n,a,tags)=>[
    some(n,i=>some(n,j=>C(binary(c,tags[0],i,j),form('relEq',r,n,a,i,j)))),
    some(n,i=>some(n,j=>C(binary(c,tags[1],i,j),form('relMem',r,n,a,i,j)))),
    some(k,i=>C(Pair(c,tags[2],i),E(p=>C(Val(f,i,p),form('relNeg',r,p,n,a))))),
    some(k,i=>some(k,j=>C(binary(c,tags[3],i,j),E(p=>E(q=>C(C(Val(f,i,p),Val(f,j,q)),form('relAnd',r,p,q))))))),
    some(k,i=>some(n,j=>C(binary(c,tags[4],i,j),E(p=>C(Val(f,i,p),form('relEx',r,p,n,a,j))))))
  ].reduce((p,q)=>['|',p,q]);
  const candidate=(k,c,f,n,a,tags)=>E(r=>C(Val(f,k,r),witness(c,f,k,r,n,a,tags)));
  const tagged=(g,f,m,n,a,tags)=>C(form('graph',g,m),A(k=>I(M(k,m),A(c=>I(Val(g,k,c),candidate(k,c,f,n,a,tags))))));
  const tags=['t0','t1','t2','t3','t4'];
  return {
    binary_code:db(binary('c','tag','i','j'),['c','tag','i','j']),
    instruction_witness:db(witness('c','f','k','r','n','a',tags),['c','f','k','r','n','a',...tags]),
    candidate:db(candidate('k','c','f','n','a',tags),['k','c','f','n','a',...tags]),
    tagged_program:db(tagged('g','f','m','n','a',tags),['g','f','m','n','a',...tags])
  };
}

export { instructionWitnessFormulas };

function buildInstructionWitnesses(defs) {
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

  const forms=instructionWitnessFormulas(defs),form=(name,...args)=>named(defs[name],args);
  const Pair=(p,x,y)=>form('pair',p,x,y),Val=(f,k,r)=>form('val',f,k,r);
  const Entry=(f,k,r,n,a)=>form('entry',f,k,r,n,a),Valid=(f,m,n,a)=>form('validProgram',f,m,n,a);
  const Binary=(c,tag,i,j)=>named(forms.binary_code,[c,tag,i,j]);
  const Witness=(c,f,k,r,n,a,tags)=>named(forms.instruction_witness,[c,f,k,r,n,a,...tags]);
  const Candidate=(k,c,f,n,a,tags)=>named(forms.candidate,[k,c,f,n,a,...tags]);
  const Tagged=(g,f,m,n,a,tags)=>named(forms.tagged_program,[g,f,m,n,a,...tags]);
  const Omega=w=>form('omega',w);
  const quant=(n,fn,xs=[])=>xs.length===n?fn(...xs):ui(x=>quant(n,fn,[...xs,x]));
  const leaf=(p,i,n)=>n===1?p:i===n-1?p[2]:leaf(p[1],i,n-1);
  const inject=(p,i,n,q)=>n===1?q:i===n-1?or(p[1],q):ol(inject(p[1],i,n-1,q),p[2]);
  function cases(p,goal,fs){return fs.length===1?fs[0](p):oe(p,goal,q=>cases(q,goal,fs.slice(0,-1)),fs.at(-1));}
  const inner=(p,x)=>replace(p[2],p[1],x)[2];
  const someIn=(goal,x,xs,p)=>ei(goal,x,ai(xs,p));
  function openEntry(op,p,fn){return open(p,(i,ip)=>op===2?fn(i,null,al(ip),null,ar(ip)):
    open(ar(ip),(j,jp)=>fn(i,j,al(ip),al(jp),ar(jp))));}
  const finite=buildF(defs),proofs={};
  function save(name,p){proofs[name]={goal:db(p.goal),proof:p.emit([],[])};return proofs[name];}

  save('binary_instruction_code_exists',quant(3,(tag,i,j)=>
    use(imported(finite.pair_exists),pairExists=>open(us(pairExists,i,j),(d,dij)=>
      open(us(pairExists,tag,d),(c,ctd)=>ei(E(c=>Binary(c,tag,i,j)),c,ei(Binary(c,tag,i,j),d,ai(dij,ctd))))
    ))
  ));

  save('entry_has_tagged_instruction',quant(10,(f,k,r,n,a,...tags)=>ii(Entry(f,k,r,n,a),entry=>{
    const goal=E(c=>Witness(c,f,k,r,n,a,tags));
    return cases(entry,goal,Array.from({length:5},(_,op)=>p=>openEntry(op,p,(i,j,si,sj,semantic)=>{
      const codeExists=op===2?us(imported(finite.pair_exists),tags[op],i):
        us(imported(proofs.binary_instruction_code_exists),tags[op],i,j);
      return open(codeExists,(c,code)=>{
        const witness=Witness(c,f,k,r,n,a,tags),arm=leaf(witness,op,5);
        const content=ai(code,semantic);
        const afterFirst=op===2?content:someIn(inner(arm,i),j,sj,content);
        const packed=someIn(arm,i,si,afterFirst);
        return ei(goal,c,inject(witness,op,5,packed));
      });
    })));
  })));

  save('tagged_instruction_has_entry',quant(11,(c,f,k,r,n,a,...tags)=>ii(Witness(c,f,k,r,n,a,tags),witness=>{
    const goal=Entry(f,k,r,n,a);
    return cases(witness,goal,Array.from({length:5},(_,op)=>p=>openEntry(op,p,(i,j,si,sj,coded)=>{
      const arm=leaf(goal,op,5),semantic=ar(coded);
      const afterFirst=op===2?semantic:someIn(inner(arm,i),j,sj,semantic);
      return inject(goal,op,5,someIn(arm,i,si,afterFirst));
    })));
  })));

  save('valid_program_candidate_total',quant(9,(f,m,n,a,...tags)=>ii(Valid(f,m,n,a),valid=>
    ui(k=>ii(M(k,m),km=>{
      const goal=E(c=>Candidate(k,c,f,n,a,tags));
      return open(app(ue(ar(valid),k),km),(r,rp)=>
        open(app(us(imported(proofs.entry_has_tagged_instruction),f,k,r,n,a,...tags),ar(rp)),(c,cp)=>{
          const candidate=Candidate(k,c,f,n,a,tags);
          return ei(goal,c,ei(candidate,r,ai(al(rp),cp)));
        })
      );
    }))
  )));

  const selection=buildFiniteWitnessSelection(defs,forms.candidate,8);
  for(const [name,p] of Object.entries(selection.proofs))proofs['instruction_'+name]=p;

  save('finite_valid_program_tagged_graph',quant(10,(w,f,m,n,a,...tags)=>ii(Omega(w),ow=>ii(M(m,w),mw=>ii(Valid(f,m,n,a),valid=>{
    const total=app(us(imported(proofs.valid_program_candidate_total),f,m,n,a,...tags),valid);
    const selected=app(us(imported(selection.proofs.finite_witness_selection),f,n,a,...tags,w,m),ow,mw,total);
    const expected=E(g=>Tagged(g,f,m,n,a,tags));
    if(!same(db(selected.goal,[...tags.slice().reverse(),a,n,m,f,w]),db(expected,[...tags.slice().reverse(),a,n,m,f,w])))
      throw Error('tagged finite selection interface mismatch');
    return selected;
  })))));

  return {proofs,formulas:forms};
}

export { buildInstructionWitnesses };
