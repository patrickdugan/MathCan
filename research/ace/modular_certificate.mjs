// ACE-03Q: checked closed proof DAGs and modular source translation.
// The kernel is unchanged. Each node is a sequent with previously
// established closed theorems as assumptions, justified by cut.
import { kernel, same, scoped, compile } from "./zf_interface.mjs";

function fail(msg){throw Error(msg);}
function keys(o,ks){return o!==null&&typeof o==="object"&&!Array.isArray(o)&&same(Object.keys(o).sort(),ks.slice().sort());}
function rel(p){
  const [op,a,b]=p;
  if(op==="A")return ["A",[">",["G",0],rel(a)]];
  if(op==="E")return ["E",["&",["G",0],rel(a)]];
  if(["&","|",">"].includes(op))return [op,rel(a),rel(b)];
  return p;
}
const validId=id=>typeof id==="string"&&/^[A-Za-z0-9_.:-]{1,128}$/.test(id);
function policy(targetTheory,classDef){
  if(!["logic","CL","ZF"].includes(targetTheory))fail("target policy");
  if(classDef!==null&&!scoped(classDef,1,false))fail("invalid class definition");
}
function verifyGraph(nodes,{targetTheory="ZF",classDef=null}={}){
  policy(targetTheory,classDef);
  if(!nodes||typeof nodes[Symbol.iterator]!=="function")fail("graph iterable");
  const checked=new Map(),receipts=[];
  for(const n of nodes){
    if(!keys(n,["id","deps","goal","proof","guarded"])||!validId(n.id)||typeof n.guarded!=="boolean"||!Array.isArray(n.deps))fail("node descriptor");
    if(checked.has(n.id))fail("duplicate node id");
    if(!scoped(n.goal,0,n.guarded))fail("node goal not closed");
    if(new Set(n.deps).size!==n.deps.length)fail("duplicate dependency");
    const ctx=n.deps.map(id=>{
      if(!validId(id)||!checked.has(id))fail("unknown or forward dependency");
      const g=checked.get(id);
      if(!scoped(g,0,n.guarded))fail("guarded dependency in pure node");
      return g;
    });
    const r=kernel(0,ctx,n.proof,n.guarded,targetTheory,n.guarded?classDef:null);
    if(!same(r.goal,n.goal))fail("node goal mismatch: "+n.id);
    // Own a copy of the checked conclusion: a producer may reuse or
    // modify its own objects after yielding a node.
    checked.set(n.id,JSON.parse(JSON.stringify(r.goal)));
    receipts.push({id:n.id,dependencies:n.deps.length,nodes:r.visits,guarded:n.guarded});
  }
  return {goals:checked,receipts};
}
function rewriteAxioms(p,base,axioms,sourceTheory){
  // Original proof is already checked by kernel. Match each axiom
  // by its exact source formula; do not walk inside formula ASTs.
  const shift=i=>i<base?i:i+axioms.length;
  function walk(n){
    const [op,a,b,c]=n;
    switch(op){
      case "axiom":{
        const goal=kernel(0,[],n,false,sourceTheory).goal;
        const i=axioms.findIndex(x=>same(x,goal));
        if(i<0)fail("missing modular axiom certificate");
        return ["h",base+i];
      }
      case "h":return ["h",shift(a)];
      case "refl":return n;
      case "iI":return [op,a,walk(b)];
      case "iE":case "aI":return [op,walk(a),walk(b)];
      case "aL":case "aR":case "uI":case "dne":return [op,walk(a)];
      case "oL":case "fE":case "uE":return [op,walk(a),b];
      case "oR":return [op,a,walk(b)];
      case "oE":return [op,walk(a),walk(b),walk(c)];
      case "eI":return [op,a,b,walk(c)];
      case "eE":return [op,walk(a),b,walk(c)];
      case "eqS":return [op,a,walk(b),walk(c)];
      default:fail("unsupported source rule");
    }
  }
  return walk(p);
}
function compileModular(k,ctx,p,{sourceTheory="ZFC",targetTheory="ZF",classDef=null,nodes=[],certificates=[]}={}){
  policy(targetTheory,classDef);
  if(!Array.isArray(certificates))fail("certificate list");
  const source=kernel(k,ctx,p,false,sourceTheory);
  const verified=verifyGraph(nodes,{targetTheory,classDef});
  const certs=[];
  for(const c of certificates){
    if(!keys(c,["spec","node"])||!validId(c.node)||!verified.goals.has(c.node))fail("certificate descriptor");
    const sourceGoal=kernel(0,[],["axiom",c.spec],false,sourceTheory).goal;
    const want=rel(sourceGoal);
    if(!same(verified.goals.get(c.node),want))fail("certificate goal mismatch");
    if(certs.some(x=>same(x.sourceGoal,sourceGoal)))fail("duplicate certificate");
    certs.push({node:c.node,sourceGoal,want});
  }
  const axioms=certs.map(c=>c.sourceGoal),targets=certs.map(c=>c.want);
  const rewritten=rewriteAxioms(p,ctx.length,axioms,sourceTheory);
  const rewrittenCheck=kernel(k,[...ctx,...axioms],rewritten,false,sourceTheory);
  if(!same(source.goal,rewrittenCheck.goal))fail("rewritten source mismatch");
  // Original compiler with ordinary source hypotheses and zero axiom imports.
  const translated=compile(k,[...ctx,...axioms],rewritten,{sourceTheory,targetTheory,classDef,certificates:[]});
  const external=[...Array.from({length:k},(_,i)=>["G",i]),...ctx.map(rel)];
  const want=rel(source.goal),full=[...external,...targets];
  if(!same(translated.targetCtx,full)||!same(translated.target.goal,want))fail("translation mismatch");
  // Check a deduction-theorem wrapper in the external target context.
  const conditional=targets.reduceRight((q,a)=>["iI",a,q],translated.proof);
  const conditionalGoal=targets.reduceRight((q,a)=>[">",a,q],want);
  const ccheck=kernel(k,external,conditional,true,targetTheory,classDef);
  if(!same(ccheck.goal,conditionalGoal))fail("conditional target mismatch");
  // Independently check elimination of each closed certificate.
  // The conditional theorem is supplied as a hypothesis of this cut.
  const cut=targets.reduce((q,_,i)=>["iE",q,["h",external.length+i]],["h",full.length]);
  const cutCheck=kernel(k,[...full,conditionalGoal],cut,true,targetTheory,classDef);
  if(!same(cutCheck.goal,want))fail("cut target mismatch");
  // The returned sequent has only the external assumptions by
  // admissibility of cut: graph goals were checked from prior closed
  // dependencies, and the conditional theorem from external alone.
  // This is a modular certificate, not an expanded kernel proof tree.
  return {source,target:{goal:want,context:external},rewritten,translated:translated.proof,conditional,conditionalGoal,cut,certificateNodes:certs.map(c=>c.node),receipts:verified.receipts,stats:{graph_nodes:verified.receipts.length,graph_kernel_visits:verified.receipts.reduce((s,r)=>s+r.nodes,0),rewritten_source_nodes:rewrittenCheck.visits,translated_nodes:translated.target.visits,conditional_nodes:ccheck.visits,cut_nodes:cutCheck.visits}};
}
export { verifyGraph, compileModular };
