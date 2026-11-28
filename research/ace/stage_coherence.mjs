import { definition } from './constructible_definition.mjs';
import { kernel, same, rejects } from './zf_interface.mjs';
import { buildE } from './hierarchy_closure.mjs';
import { buildF } from './finite_witnesses.mjs';

function runH(){
  const defs=definition("v",true),p=buildE(defs,true),fw=buildF(defs),out={};
  const names=["no_two_cycle","successor_predecessor_unique","bounded_induction_coherence","stage_graph_coherence","bounded_induction_monotonicity","stage_graph_monotonicity_conditional","stage_graph_restriction","ordered_pair_unique","graph_extensionality","stage_graph_unique","cross_graph_monotonicity_conditional"];
  function check(name,goal,proof){
    const r=kernel(0,[],proof,false,"ZF");
    if(!same(r.goal,goal))throw Error("goal mismatch "+name);
    out[name]={nodes:r.visits,proof_bytes:JSON.stringify(proof).length};
  }
  for(const name of names)check(name,p[name].goal,p[name].proof);
  for(const n of ["stage_graph_monotonicity","cross_graph_monotonicity"]){
    const q=p[n+"_conditional"];
    if(!same(q.goal[1],fw.def_inflation.goal))throw Error("inflation mismatch");
    check(n,q.goal[2],["iE",q.proof,fw.def_inflation.proof]);
  }
  function embed(p,indices,d=0){
    const [op,a,b]=p;
    if(op==="F")return p;
    if(op==="A"||op==="E")return [op,embed(a,indices,d+1)];
    if(op==="M"||op==="="){
      const f=i=>i<d?i:indices[i-d]+d;
      return [op,f(a),f(b)];
    }
    return [op,embed(a,indices,d),embed(b,indices,d)];
  }
  const A=p=>["A",p],E=p=>["E",p],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b];
  const sub=(a,b)=>A(I(M(0,a+1),M(0,b+1)));
  const trans=a=>A(I(M(0,a+1),sub(0,a+1)));
  const SG=(f,d)=>embed(defs.stageGraph,[f,d]),V=(f,i,r)=>embed(defs.val,[f,i,r]);
  const all=(n,p)=>{for(let i=0;i<n;i++)p=A(p);return p;};
  const imp=(...ps)=>ps.reduceRight((a,b)=>I(b,a));
  const unique=all(3,imp(trans(0),SG(2,0),SG(1,0),Q(2,1)));
  const eqStage=A(I(V(5,1,0),A(I(V(5,2,0),Q(1,0)))));
  const eqIndex=A(imp(M(0,2),M(0,1),eqStage));
  const coherence=all(4,imp(trans(1),trans(0),SG(3,1),SG(2,0),eqIndex));
  const eqv=A(I(M(0,2),A(C(I(V(2,1,0),V(5,1,0)),I(V(5,1,0),V(2,1,0))))));
  const restriction=all(3,imp(trans(0),sub(0,1),SG(2,1),E(C(SG(0,1),eqv))));
  const goals=[["stage_graph_unique",unique],["stage_graph_coherence",coherence],["stage_graph_restriction",restriction]];
  for(const [name,goal] of goals)if(!same(p[name].goal,goal))throw Error("independent exact goal mismatch "+name);
  const tests=[
    ()=>kernel(0,[],p.stage_graph_coherence.proof,false,"CL"),
    ()=>kernel(0,[],p.stage_graph_restriction.proof,false,"CL"),
    ()=>kernel(0,[],p.stage_graph_unique.proof,false,"CL"),
    ()=>kernel(0,[],["iE",p.stage_graph_monotonicity_conditional.proof,fw.omega_exists.proof],false,"ZF"),
    ()=>kernel(0,[],["iE",p.cross_graph_monotonicity_conditional.proof,fw.pair_exists.proof],false,"ZF")
  ];
  for(const t of tests)if(!rejects(t))throw Error("negative control accepted");
  return {experiment:"ACE-03H",scope:"coherence, restriction, uniqueness and monotonicity of existing exact stage graphs; no general existence",proofs:out,independent_goal_checks:goals.length,negative_controls:tests.length,remaining:"general stage graph existence and extension, remaining L axioms, uniform adequacy, checker soundness"};
}

console.log(JSON.stringify(runH(),null,2));
