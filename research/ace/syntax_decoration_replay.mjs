import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { definition } from './constructible_definition.mjs';
import { buildSyntaxDecoration } from './syntax_decoration.mjs';
import { expectedSyntaxTraceAdequacy } from './syntax_trace_adequacy_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

// Independent de Bruijn construction uses the independently reconstructed
// ACE-03U syntax formulas and the unchanged pinned Def skeleton.
function expectedSyntaxDecoration(defs) {
  const atom=(op,x,y)=>d=>[op,x(d),y(d)];
  const mem=(x,y)=>atom('M',x,y),bin=(op,p,q)=>d=>[op,p(d),q(d)];
  const imp=(p,q)=>bin('>',p,q),and=(p,q)=>bin('&',p,q),or=(p,q)=>bin('|',p,q);
  const iff=(p,q)=>and(imp(p,q),imp(q,p));
  const all=fn=>d=>['A',fn(e=>e-d-1)(d+1)],ex=fn=>d=>['E',fn(e=>e-d-1)(d+1)];
  const forall=(n,fn,vs=[])=>vs.length===n?fn(...vs):all(x=>forall(n,fn,[...vs,x]));
  const exists=(n,fn,vs=[])=>vs.length===n?fn(vs):ex(x=>exists(n,fn,[...vs,x]));
  const some=(s,fn)=>ex(x=>and(mem(x,s),fn(x))),free=i=>d=>d+i;
  function embed(p,indices,d=0) {
    const [op,a,b]=p;
    if(op==='F')return p;
    if(op==='A'||op==='E')return [op,embed(a,indices,d+1)];
    if(op==='M'||op==='='){const v=i=>i<d?i:indices[i-d]+d;return [op,v(a),v(b)];}
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const apply=(p,...args)=>d=>embed(p,args.map(t=>t(d))),term=(name,...args)=>apply(defs[name],...args);
  const previous=expectedSyntaxTraceAdequacy(defs).formulas;
  const decorated=(f,m,n,a)=>exists(5,ps=>and(
    apply(previous.syntax,m,n,...ps),apply(previous.trace,f,m,n,a,...ps)));
  const nonempty=x=>ex(y=>mem(y,x));
  function scheme(a,x,withSyntax) {
    return or(term('empty',x),ex(w=>and(term('omega',w),
      some(w,n=>some(w,m=>and(and(nonempty(n),nonempty(m)),
        ex(f=>and(withSyntax?decorated(f,m,n,a):term('validProgram',f,m,n,a),term('lastSlice',f,m,n,a,x)))))))));
  }
  const decoded=(a,x)=>scheme(a,x,true),decodedSet=(a,b)=>all(x=>iff(mem(x,b),decoded(a,x)));
  const decorateStatement=forall(5,(w,f,m,n,a)=>imp(term('omega',w),imp(mem(m,w),
    imp(term('validProgram',f,m,n,a),decorated(f,m,n,a)))))(0);
  return {proofs:{
    finite_trace_has_decoded_syntax:decorateStatement,
    finite_valid_program_iff_decoded_syntax:forall(5,(w,f,m,n,a)=>imp(term('omega',w),imp(mem(m,w),
      iff(term('validProgram',f,m,n,a),decorated(f,m,n,a)))))(0),
    pinned_definable_has_decoded_syntax:forall(2,(a,x)=>imp(term('definable',a,x),decoded(a,x)))(0),
    decoded_syntax_is_pinned_definable:forall(2,(a,x)=>imp(decoded(a,x),term('definable',a,x)))(0),
    definable_iff_decoded_syntax:forall(2,(a,x)=>iff(term('definable',a,x),decoded(a,x)))(0),
    def_set_iff_decoded_syntax:forall(2,(a,b)=>iff(term('Def',a,b),decodedSet(a,b)))(0)
  },formulas:{
    decorated:decorated(free(0),free(1),free(2),free(3))(0),
    decoded_definable:decoded(free(0),free(1))(0),
    decoded_Def:decodedSet(free(0),free(1))(0)
  },pinned_def_skeleton:scheme(free(0),free(1),false)(0)};
}

function runSyntaxDecoration() {
  const defs=definition('v',true),actual=buildSyntaxDecoration(defs),expected=expectedSyntaxDecoration(defs);
  if(!same(defs.L,JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'))))throw Error('pinned L changed');
  if(!same(expected.pinned_def_skeleton,defs.definable))throw Error('pinned Def outer skeleton changed');
  if(!same(actual.formulas,expected.formulas))throw Error('independent decoration interfaces');
  if(!same(Object.keys(actual.proofs),Object.keys(expected.proofs)))throw Error('decoration theorem coverage');
  const checks=[],controls=[],axioms=new Map();let logicOnly=0;
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn){if(!rejects(fn))throw Error('negative control accepted: '+name);controls.push(name);}
  function exact(proof,want){const got=kernel(0,[],proof,false,'ZF');if(!same(got.goal,want))throw Error('wrong exact target');}
  for(const [id,p] of Object.entries(actual.proofs)) {
    const want=expected.proofs[id];
    if(!scoped(p.goal,0,false)||!same(p.goal,want))throw Error('decoration exact interface '+id);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(!same(got.goal,want))throw Error('decoration kernel goal '+id);
    const used=new Set();
    walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);axioms.set(JSON.stringify(n[1]),n[1]);}});
    if([...used].some(a=>!['pairing','union','power','separation','foundation','extensionality'].includes(a)))throw Error('unexpected decoration axiom');
    checks.push({id,nodes:got.visits,goal_bytes:JSON.stringify(got.goal).length,ambient_axioms:[...used].sort()});
    reject(id+':changed_outer_binder',()=>exact(p.proof,['E',want[1]]));
    reject(id+':free_instantiation',()=>kernel(0,[],['uE',p.proof,0],false,'ZF'));
    if(used.size)reject(id+':forbid_set_axioms',()=>kernel(0,[],p.proof,false,'CL'));
    else {if(!same(kernel(0,[],p.proof,false,'CL').goal,want))throw Error('pure-logic goal');logicOnly++;}
  }
  for(const [name,index] of [['omega',0],['finite_domain',1],['valid_program',2]]) {
    const altered=structuredClone(expected.proofs.finite_trace_has_decoded_syntax);
    let body=altered;for(let i=0;i<5;i++)body=body[1];for(let i=0;i<index;i++)body=body[2];
    body.splice(0,body.length,...body[2]);
    reject('decoration:omit_'+name,()=>exact(actual.proofs.finite_trace_has_decoded_syntax.proof,altered));
  }
  // The existential field values must stay inside their binder scopes.
  const escaped=structuredClone(expected.formulas.decorated);
  let changed=false;
  function escape(p,depth=0) {
    if(changed||!Array.isArray(p))return;
    if(p[0]==='M'||p[0]==='='){p[1]=depth+4;changed=true;return;}
    if(p[0]==='A'||p[0]==='E')escape(p[1],depth+1);
    else {escape(p[1],depth);escape(p[2],depth);}
  }
  escape(escaped);
  reject('decoration:escaping_field_variable',()=>{if(!scoped(escaped,4,false))throw Error('out of scope');});
  reject('choice_axiom_forbidden',()=>kernel(0,[],['axiom',{name:'choice'}],false,'ZF'));
  return {experiment:'ACE-03V',part:'finite_decoration_and_exact_Def_equivalence',checks,
    checked_modules:checks.length,new_statement_checks:checks.length,reused_helper_checks:0,
    kernel_visits:checks.reduce((n,c)=>n+c.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:3,pinned_def_skeleton_checks:1,logic_only_checks:logicOnly,
    negative_controls:controls.length,controls,
    ambient_axiom_instances:[...axioms.values()].map(s=>({name:s.name,...(s.body?{params:s.params,body_bytes:JSON.stringify(s.body).length}:{})})),
    pinned_L_unchanged:true,
    scope:'uniform finite reverse decoration, exact validProgram equivalence under its omega and finite-domain premises, and both directions of pinned definable and Def equivalence to decoded syntax',
    open_obligations:['total semantic execution existence for arbitrary supplied syntax','single-natural-number coding adequacy',
      'canonical transfinite well-order history','internal constructibility of canonical orders','exact relativized Choice import','formal checker soundness']};
}

export { expectedSyntaxDecoration, runSyntaxDecoration };
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href)
  console.log(JSON.stringify(runSyntaxDecoration(),null,2));
