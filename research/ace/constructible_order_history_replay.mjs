// ACE-03X. Independent canonical-history formulas and closed endpoint replay.
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { definition } from './constructible_definition.mjs';
import { buildConstructibleOrderHistory } from './constructible_order_history.mjs';
import { canonicalStageExpectedLanguage } from './canonical_stage_order_replay.mjs';
import { expectedCanonicalLimitOrder } from './canonical_limit_order_replay.mjs';
import { kernel, same, scoped, rejects } from './zf_interface.mjs';

function constructibleHistoryExpectedLanguage(defs){
  const L=canonicalStageExpectedLanguage(defs),{M,Q,I,C,O,N,A,E,every,quant,apply,free,Val,iff,Good,Next,Embed}=L;
  const limits=expectedCanonicalLimitOrder(defs).formulas;
  const Graph=(f,d)=>apply(defs.graph,f,d),Ord=d=>apply(defs.ordinal,d),Succ=(i,d)=>apply(defs.successor,i,d);
  const Value=(h,r)=>apply(limits.value,h,r);
  const Range=(f,d,h)=>A(p=>iff(M(p,h),E(i=>C(M(i,d),Val(f,i,p)))));
  const Eq=(f,g,d)=>every(d,i=>A(r=>iff(Val(f,i,r),Val(g,i,r))));
  const Pred=d=>E(i=>C(M(i,d),Succ(i,d)));
  const Prior=(f,d,r)=>every(d,i=>A(p=>I(Val(f,i,p),Embed(p,r))));
  const SuccCase=(f,d,r)=>E(i=>C(M(i,d),C(Succ(i,d),E(p=>C(Val(f,i,p),Next(p,r))))));
  const LimitCase=(f,d,r)=>C(N(Pred(d)),E(h=>C(Range(f,d,h),Value(h,r))));
  const Step=(f,d,r)=>C(Good(r),C(Prior(f,d,r),O(SuccCase(f,d,r),LimitCase(f,d,r))));
  const Hist=(f,d)=>C(Graph(f,d),every(d,i=>E(r=>C(Val(f,i,r),Step(f,i,r)))));
  const Pointwise=(f,d)=>every(d,i=>A(p=>I(Val(f,i,p),Good(p))));
  const Forward=(f,d)=>every(d,i=>every(d,j=>I(M(i,j),quant(2,(p,q)=>I(Val(f,i,p),I(Val(f,j,q),Embed(p,q)))))));
  const Total=quant(2,(f,d)=>I(Ord(d),I(Hist(f,d),E(r=>Step(f,d,r)))));
  const Functional=quant(4,(f,d,r,s)=>I(Hist(f,d),I(Step(f,d,r),I(Step(f,d,s),Q(r,s)))));
  const Local=quant(4,(f,g,d,r)=>I(Eq(f,g,d),I(Step(f,d,r),Step(g,d,r))));
  return {...L,Graph,Ord,Succ,Value,Range,Eq,Pred,Prior,SuccCase,LimitCase,Step,Hist,Pointwise,Forward,Total,Functional,Local};
}

function expectedConstructibleOrderHistory(defs){
  const L=constructibleHistoryExpectedLanguage(defs),{M,Q,I,C,N,A,E,quant,free,Val,Graph,Ord,Range,Eq,Pred,Prior,SuccCase,LimitCase,Step,Hist,
    Pointwise,Forward,Total,Functional,Local,premises}=L;
  const f=(n,fn)=>fn(...Array.from({length:n},(_,i)=>free(i)))(0),g=(n,fn)=>quant(n,fn)(0);
  const UniqueHistory=d=>E(h=>C(Hist(h,d),A(k=>I(Hist(k,d),Q(k,h)))));
  const Agreement=(f,g,d,e,result)=>A(i=>I(M(i,d),I(M(i,e),A(r=>I(Val(f,i,r),A(s=>I(Val(g,i,s),result(r,s))))))));
  return {formulas:{
    range:f(3,Range),prior:f(3,Prior),pointwise:f(2,Pointwise),forward:f(2,Forward),predecessor:f(1,Pred),
    successor_case:f(3,SuccCase),limit_case:f(3,LimitCase),step:f(3,Step),history:f(2,Hist),value_agreement:f(3,Eq),
    total:Total(0),functional:Functional(0),local:Local(0)
  },proofs:{
    prefix_range_exists:g(2,(f,d)=>I(Graph(f,d),E(h=>Range(f,d,h)))),
    prefix_range_unique:g(4,(f,d,h,k)=>premises([Range(f,d,h),Range(f,d,k)],Q(h,k))),
    prefix_range_transport:g(4,(f,g,d,h)=>premises([Eq(f,g,d),Range(f,d,h)],Range(g,d,h))),
    history_value_step:g(4,(f,d,i,p)=>premises([Hist(f,d),M(i,d),Val(f,i,p)],Step(f,i,p))),
    history_pointwise:g(2,(f,d)=>I(Hist(f,d),Pointwise(f,d))),
    history_forward_embeddings:g(2,(f,d)=>I(Hist(f,d),Forward(f,d))),
    step_prefix_local:Local(0),step_functional:Functional(0),step_total:Total(0),
    ordinal_order_history_exists_unique:g(1,d=>I(Ord(d),UniqueHistory(d))),
    ordinal_order_history_coherence:g(4,(f,g,d,e)=>premises([Ord(d),Ord(e),Hist(f,d),Hist(g,e)],Agreement(f,g,d,e,Q)))
  },changed_contracts:{
    unguarded_history:g(1,d=>UniqueHistory(d)),
    successor_only_total:g(2,(f,d)=>premises([Ord(d),Hist(f,d)],E(r=>SuccCase(f,d,r)))),
    reversed_coherence:g(4,(f,g,d,e)=>premises([Ord(d),Ord(e),Hist(f,d),Hist(g,e)],Agreement(f,g,d,e,(r,s)=>N(Q(r,s)))))
  }};
}

const partIds={
  range:['prefix_range_exists','prefix_range_unique','prefix_range_transport'],
  structure:['history_value_step','history_pointwise','history_forward_embeddings','step_prefix_local'],
  functional:['step_functional'],total:['step_total'],existence:['ordinal_order_history_exists_unique'],
  coherence:['ordinal_order_history_coherence']
};

function runConstructibleOrderHistory(part='structure'){
  if(part!=='all'&&!Object.hasOwn(partIds,part))throw Error('canonical history replay part');
  const defs=definition('v',true),pinned=JSON.parse(readFileSync(new URL('./L_formula.json',import.meta.url),'utf8'));
  if(!same(defs.L,pinned))throw Error('pinned L changed');
  const progress=process.env.ACE_HISTORY_DIAGNOSTICS?label=>{const m=process.memoryUsage();console.error(label,JSON.stringify({rss:m.rss,heapUsed:m.heapUsed,heapTotal:m.heapTotal}));}:undefined;
  const built=buildConstructibleOrderHistory(defs,part,{onProgress:progress}),expected=expectedConstructibleOrderHistory(defs);
  if(typeof globalThis.gc==='function')globalThis.gc();
  if(progress)progress('after_independent_goals');
  for(const [name,want] of Object.entries(expected.formulas))
    if(!same(built.formulas[name],want))throw Error('independent canonical history formula: '+name);
  const ids=part==='all'?Object.keys(expected.proofs):partIds[part];
  const checks=[],controls=[],usedAxioms=new Set();let kernelControls=0,contractControls=0,logicOnly=0;
  const hash=p=>createHash('sha256').update(JSON.stringify(p)).digest('hex');
  function walk(p,fn){if(!Array.isArray(p))return;fn(p);for(const x of p)if(Array.isArray(x))walk(x,fn);}
  function reject(name,fn,kind='contract'){
    if(!rejects(fn))throw Error('canonical history control accepted: '+name);
    controls.push(name);if(kind==='kernel')kernelControls++;else contractControls++;
  }
  for(const name of ids){
    const p=built.proofs[name],want=expected.proofs[name];
    if(!p||!scoped(p.goal,0,false)||!same(p.goal,want))throw Error('exact canonical history goal: '+name);
    if(progress)progress('checking_'+name);
    const got=kernel(0,[],p.proof,false,'ZF');
    if(progress)progress('checked_'+name);
    if(!same(got.goal,want))throw Error('kernel canonical history conclusion: '+name);
    const used=new Set();walk(p.proof,n=>{if(n[0]==='axiom'){used.add(n[1].name);usedAxioms.add(n[1].name);}});
    if([...used].some(x=>!['extensionality','empty','pairing','union','power','infinity','separation','replacement','foundation'].includes(x)))
      throw Error('unexpected history axiom: '+name);
    if(!used.size){kernel(0,[],p.proof,false,'CL');logicOnly++;}
    checks.push({id:name,nodes:got.visits,goal_bytes:JSON.stringify(want).length,goal_sha256:hash(want),ambient_axioms:[...used].sort()});
    reject(name+':unbound_dependency',()=>kernel(0,[],['iE',['h',0],p.proof],false,'ZF'),'kernel');
    reject(name+':false_conclusion',()=>{if(!same(got.goal,['F']))throw Error('false conclusion');});
    reject(name+':drop_outer_quantifier',()=>{if(!same(got.goal,want[1]))throw Error('dropped outer quantifier');});
    const changed=name==='ordinal_order_history_exists_unique'?expected.changed_contracts.unguarded_history:
      name==='step_total'?expected.changed_contracts.successor_only_total:
      name==='ordinal_order_history_coherence'?expected.changed_contracts.reversed_coherence:null;
    if(changed)reject(name+':changed_mathematical_contract',()=>{if(!same(got.goal,changed))throw Error('changed contract');});
  }
  return {experiment:'ACE-03X',part:'constructible_order_history_'+part,checks,checked_modules:checks.length,
    kernel_visits:checks.reduce((n,x)=>n+x.nodes,0),independent_exact_goals:checks.length,
    independent_formula_interfaces:Object.keys(expected.formulas).length,negative_controls:controls.length,
    kernel_rejections:kernelControls,contract_rejections:contractControls,logic_only_checks:logicOnly,controls,
    ambient_axioms:[...usedAxioms].sort(),pinned_L_unchanged:true,
    scope:'canonical packed constructible-stage histories using the actual least-description successor order and exact limit union; every recursive value carries a transitive well-ordered carrier and embeds all earlier values',
    open_obligations:['internal constructibility of the canonical order','relativized Choice import','formal checker soundness']};
}

export {constructibleHistoryExpectedLanguage,expectedConstructibleOrderHistory,runConstructibleOrderHistory};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
  const part=process.argv.find(x=>x.startsWith('--part='))?.slice(7)||'structure';
  console.log(JSON.stringify(runConstructibleOrderHistory(part),null,2));
}
