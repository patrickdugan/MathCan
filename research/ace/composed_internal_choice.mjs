// ACE-03Y-03: compose the exact conditional Choice endpoint.
import { readFileSync } from "node:fs";
import { kernel, same, scoped, compile, expandClass, rejects, inst, classProofs } from "./zf_interface.mjs";
import { definition } from "./constructible_definition.mjs";
import { buildE } from "./hierarchy_closure.mjs";
import { buildF } from "./finite_witnesses.mjs";
import { buildI } from "./stage_recursion.mjs";
import { buildWellOrder } from "./constructible_well_order.mjs";
import { runInternalChoiceBridge } from "./internal_choice_bridge.mjs";
import { runBoundedChoice } from "./bounded_choice_transport.mjs";
function runComposition({kernel,same,scoped,compile,expandClass,rejects,inst,classProofs,definition,buildWellOrder,buildE,buildF,buildI,runInternalChoiceBridge,runBoundedChoice,pinned,prior1,prior2}){
  const require=(p,m)=>{if(!p)throw Error(m);};
  const defs=definition("v",true),G=i=>["G",i],M=(a,b)=>["M",a,b],I=(a,b)=>[">",a,b],C=(a,b)=>["&",a,b],A=p=>["A",p],E=p=>["E",p];
  require(same(defs.L,pinned),"pinned L mismatch");
  const common={kernel,same,scoped,compile,expandClass,rejects,definition,buildWellOrder,pinned};
  const b=runInternalChoiceBridge(common,true),s=runBoundedChoice({...common,prior:prior1},true);
  require(same(b.receipt,prior1)&&same(s.receipt,prior2),"upstream receipt mismatch");
  const prior=buildE(defs,true),finite=buildF(defs,"relations"),stages=buildI(defs,prior,finite,true);
  const tr=prior.L_transitivity_conditional,inf=finite.def_inflation;
  require(same(tr.goal[1],inf.goal),"transitivity source interface");
  const lP=["iE",tr.proof,inf.proof],rawT=kernel(0,[],lP,false,"ZF");
  const tx=["conv",inst(defs.L,1),["aL",["h",0]]];
  const sx=["iE",["uE",["closed",lP],1],tx],sy=["iE",["uE",sx,0],["aR",["h",0]]];
  const T=A(A(I(C(G(1),M(0,1)),G(0))));
  const tg=["uI",["uI",["iI",C(G(1),M(0,1)),["conv",G(0),sy]]]];
  const tc=kernel(0,[],tg,true,"ZF",defs.L);require(same(tc.goal,T),"class transitivity interface");
  const c=classProofs(),ax=c.generic.find(x=>x.name==="union"),closure=ax.premises[1],pure=stages.constructible_union_closure;
  require(same(pure.goal,expandClass(closure,defs.L)),"Union closure interface");
  const rawU=kernel(0,[],pure.proof,false,"ZF");
  require(same(rawU.goal,pure.goal),"Union closure check");
  const unionProof=["iE",["iE",ax.proof,tg],["conv",closure,["closed",pure.proof]]];
  const unionCheck=kernel(0,[],unionProof,true,"ZF",defs.L);
  function guard(p){const [o,a,b]=p;if(o==="A")return A(I(G(0),guard(a)));if(o==="E")return E(C(G(0),guard(a)));if(["&","|",">"].includes(o))return [o,guard(a),guard(b)];return p;}
  const union=guard(kernel(0,[],["axiom",{name:"union"}],false,"ZF").goal);
  const choice=guard(kernel(0,[],["axiom",{name:"choice"}],false,"ZFC").goal);
  const sepBound=guard(kernel(0,[],["axiom",prior2.bounded_selector_schema],false,"ZF").goal);
  const sepRaw=guard(kernel(0,[],["axiom",prior1.selector_schema],false,"ZF").goal);
  require(same(unionCheck.goal,union),"exact Union axiom");
  const w=buildWellOrder(defs),wo=w.formulas.well_order;
  // Embed the two free WO arguments [A,R] at de Bruijn slots [1,0].
  function emb(p,indices,d=0){const [o,a,b]=p;if(o==="F")return p;if(o==="A"||o==="E")return [o,emb(a,indices,d+1)];if(o==="M"||o==="="){const f=i=>i<d?i:indices[i-d]+d;return [o,f(a),f(b)];}return [o,emb(a,indices,d),emb(b,indices,d)];}
  const external=A(I(G(0),E(C(G(0),emb(wo,[1,0])))));
  const internal=guard(A(E(emb(wo,[1,0]))));
  require(same(s.sepLink.goal,I(sepBound,sepRaw)),"bounded Separation link interface");
  require(same(s.allProof.goal,I(T,I(external,internal))),"order link interface");
  require(same(b.bridge.goal,I(sepRaw,I(union,I(internal,choice)))),"Choice link interface");
  const closed=p=>["closed",p];
  const deriveSep=["iE",closed(s.sepLink.proof),["h",0]];
  const deriveWO=["iE",["iE",closed(s.allProof.proof),closed(tg)],["h",1]];
  const endpoint=["iE",["iE",["iE",closed(b.bridge.proof),deriveSep],closed(unionProof)],deriveWO];
  const proof=["iI",sepBound,["iI",external,endpoint]];
  const goal=I(sepBound,I(external,choice)),out=kernel(0,[],proof,true,"ZF",defs.L);
  require(same(out.goal,goal),"conditional endpoint");
  const expanded=expandClass(goal,defs.L),full=["conv",expanded,proof],fullCheck=kernel(0,[],full,true,"ZF",defs.L);
  require(same(fullCheck.goal,expanded)&&scoped(expanded,0,false),"expanded endpoint");
  // Independently check the actual compiler lowering resource demand.
  // The carrier is a third parameter in the formula supplied to buildF.
  const body=["&",M(0,3),prior2.bounded_selector_schema.body];
  let width=4,ins=0;const ops={};
  function emit(op){ins++;ops[op]=(ops[op]||0)+1;}
  function lower(p,d=0){const [o,a,b]=p;width=Math.max(width,4+d);
    if(o==="F"){emit("eq");emit("neg");}
    else if(o==="M"||o==="=")emit(o==="M"?"mem":"eq");
    else if(o==="A"||o==="E"){lower(a,d+1);if(o==="A")emit("neg");emit("exists");if(o==="A")emit("neg");}
    else{lower(a,d);lower(b,d);if(o==="&")emit("and");else if(o==="|"){emit("neg");emit("neg");emit("and");emit("neg");}else{emit("neg");emit("and");emit("neg");}}
  }
  require(scoped(body,4,false),"compiler input scope");lower(body);
  require(width===10&&ins===74,"compiler resource count changed");
  const controls=[
    ()=>kernel(0,[],["iI",sepBound,endpoint],true,"ZF",defs.L),
    ()=>kernel(0,[],["iI",external,["iI",sepBound,endpoint]],true,"ZF",defs.L),
    ()=>kernel(0,[],full,true,"ZF",["=",0,0]),
    ()=>kernel(0,[],proof,true,"CL",defs.L),
    ()=>kernel(0,[],["axiom",{name:"choice"}],true,"ZF",defs.L)
  ];
  for(const f of controls)require(rejects(f),"negative control accepted");
  return {experiment:"ACE-03Y-03",scope:"closed conditional exact L-Choice with two remaining explicit antecedents",pinned_L_unchanged:true,prior_receipts_reproduced:2,checks:{ambient_transitivity:rawT.visits,class_transitivity:tc.visits,ambient_union_closure:rawU.visits,relativized_union:unionCheck.visits,composed_conditional:out.visits,expanded_conditional:fullCheck.visits},remaining_antecedents:["bounded_selector_separation","constructible_ambient_order_witnesses"],compiler_resources:{width,instructions:ins,opcodes:ops,prior_width_cap:6,prior_instruction_cap:20},negative_controls:controls.length,choice_imports:0,target_theory:"ZF"};
}
const read=n=>JSON.parse(readFileSync(new URL(n,import.meta.url),"utf8"));
console.log(JSON.stringify(runComposition({kernel,same,scoped,compile,expandClass,rejects,inst,classProofs,definition,buildWellOrder,buildE,buildF,buildI,runInternalChoiceBridge,runBoundedChoice,pinned:read("./L_formula.json"),prior1:read("./internal_choice_bridge_receipt.json"),prior2:read("./bounded_choice_transport_receipt.json")}),null,2));
