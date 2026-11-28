// ACE-03Y-01: exact conditional Choice bridge; the original kernel is unchanged.
import { readFileSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { kernel, same, scoped, compile, expandClass, rejects } from "./zf_interface.mjs";
import { definition } from "./constructible_definition.mjs";
import { buildWellOrder } from "./constructible_well_order.mjs";

function runInternalChoiceBridge({kernel,same,scoped,compile,expandClass,rejects,definition,buildWellOrder,pinned}, emitProofs=false) {
  const defs=definition("v",true);
  const require=(p,m)=>{if(!p)throw Error(m);};
  require(same(defs.L,pinned),"pinned L mismatch");
  const specChoice={name:"choice"},specUnion={name:"union"};
  const choice=kernel(0,[],["axiom",specChoice],false,"ZFC").goal;
  const union=kernel(0,[],["axiom",specUnion],false,"ZF").goal;
  const w=buildWellOrder(defs);
  const original=w.proofs.choice_from_carrier_well_order;
  const originalCheck=kernel(0,[],original.proof,false,"ZF");
  require(same(originalCheck.goal,original.goal),"prior choice interface");
  // Traverse proof children only. Formula arrays and axiom descriptors are data.
  const children={h:[],refl:[],dne:[1],eqS:[2,3],axiom:[],iI:[2],iE:[1,2],aI:[1,2],aL:[1],aR:[1],oL:[1],oR:[2],oE:[1,2,3],fE:[1],uI:[1],uE:[1],eI:[3],eE:[1,3]};
  const specs=new Map();
  function walk(n,fn){
    require(Array.isArray(n)&&Object.hasOwn(children,n[0]),"unsupported proof rule");
    const out=fn(n); if(out!==null)return out;
    const r=n.slice(); for(const j of children[n[0]])r[j]=walk(n[j],fn);return r;
  }
  let axiomLeaves=0;
  walk(original.proof,n=>{if(n[0]==="axiom"){axiomLeaves++;specs.set(JSON.stringify(n[1]),n[1]);}return null;});
  require(specs.size===1,"unexpected prior axiom set");
  const sepSpec=[...specs.values()][0];
  require(sepSpec.name==="separation"&&sepSpec.params===2,"selector schema changed");
  const sep=kernel(0,[],["axiom",sepSpec],false,"ZF").goal;
  const abstraction=walk(original.proof,n=>{
    if(n[0]==="axiom"){require(same(n[1],sepSpec),"unmatched axiom");return ["h",0];}
    if(n[0]==="h")return ["h",n[1]+1];return null;
  });
  const axiomFreeLemma=["iI",sep,abstraction];
  const lemma=kernel(0,[],axiomFreeLemma,false,"CL");
  require(same(lemma.goal,[">",sep,original.goal]),"abstracted choice lemma mismatch");
  let serial=0;
  const fresh=()=>`y${serial++}`,F=["F"];
  const M=(a,b)=>["M",a,b],Q=(a,b)=>["=",a,b],I=(p,q)=>[">",p,q],C=(p,q)=>["&",p,q],N=p=>I(p,F);
  const A=fn=>{const x=fresh();return ["A",x,fn(x)];},E=fn=>{const x=fresh();return ["E",x,fn(x)];};
  function named(p,env){
    const [o,a,b]=p;if(o==="F")return F;
    if(o==="M"||o==="=")return [o,env[a],env[b]];
    if(o==="A"||o==="E"){const x=fresh();return [o,x,named(a,[x,...env])];}
    return [o,named(a,env),named(b,env)];
  }
  function db(p,env=[]){
    const [o,a,b]=p;if(o==="F")return F;
    if(o==="M"||o==="="){const x=env.indexOf(a),y=env.indexOf(b);require(x>=0&&y>=0,"unbound");return [o,x,y];}
    if(o==="A"||o==="E")return [o,db(b,[a,...env])];
    return [o,db(a,env),db(b,env)];
  }
  function replace(p,x,y){
    const [o,a,b]=p;if(o==="F")return F;
    if(o==="M"||o==="=")return [o,a===x?y:a,b===x?y:b];
    if(o==="A"||o==="E"){
      if(a===x)return p;
      if(a===y){const z=fresh();return [o,z,replace(replace(b,a,z),x,y)];}
      return [o,a,replace(b,x,y)];
    }
    return [o,replace(a,x,y),replace(b,x,y)];
  }
  const P=(goal,emit)=>({goal,emit});
  function assume(goal){const id=fresh();return {id,p:P(goal,(_,h)=>{const j=h.indexOf(id);require(j>=0,"unbound hypothesis");return ["h",j];})};}
  function ii(g,fn){const a=assume(g),p=fn(a.p);return P(I(g,p.goal),(e,h)=>["iI",db(g,e),p.emit(e,[...h,a.id])]);}
  function ui(fn){const x=fresh(),p=fn(x);return P(["A",x,p.goal],(e,h)=>["uI",p.emit([x,...e],h)]);}
  const al=p=>P(p.goal[1],(e,h)=>["aL",p.emit(e,h)]),ar=p=>P(p.goal[2],(e,h)=>["aR",p.emit(e,h)]);
  const ai=(p,q)=>P(C(p.goal,q.goal),(e,h)=>["aI",p.emit(e,h),q.emit(e,h)]);
  const ie=(p,q)=>P(p.goal[2],(e,h)=>["iE",p.emit(e,h),q.emit(e,h)]);
  const ue=(p,x)=>P(replace(p.goal[2],p.goal[1],x),(e,h)=>["uE",p.emit(e,h),e.indexOf(x)]);
  const us=(p,...xs)=>xs.reduce(ue,p),app=(p,...qs)=>qs.reduce(ie,p);
  function ei(g,x,p){return P(g,(e,h)=>["eI",db(g[2],[g[1],...e]),e.indexOf(x),p.emit(e,h)]);}
  function open(p,fn){
    require(p.goal[0]==="E","expected existential");
    const x=fresh(),a=assume(replace(p.goal[2],p.goal[1],x)),q=fn(x,a.p);
    return P(q.goal,(e,h)=>["eE",p.emit(e,h),db(q.goal,e),q.emit([x,...e],[...h,a.id])]);
  }
  const imported=P(named(lemma.goal,[]),(_,h)=>walk(axiomFreeLemma,n=>n[0]==="h"?["h",n[1]+h.length]:null));
  const Val=(r,x,y)=>named(defs.val,[r,x,y]);
  const phi=(y,a,r)=>E(x=>C(M(x,a),C(M(y,x),A(z=>I(M(z,x),N(Val(r,z,y)))))));
  require(same(db(phi("y","a","r"),["y","a","r"]),sepSpec.body),"independent selector formula mismatch");
  const WO=(a,r)=>named(w.formulas.well_order,[a,r]);
  const allWO=A(u=>E(r=>WO(u,r)));
  const family=a=>named(w.formulas.choice_antecedent,[a]);
  const selected=a=>named(w.formulas.selected_set,[a]);
  require(same(db(A(a=>I(family(a),selected(a)))),choice),"independent exact Choice body mismatch");
  const bridge=ii(named(sep,[]),hs=>ii(named(union,[]),hu=>ii(allWO,hw=>ui(a=>ii(family(a),hf=>{
    return open(ue(hu,a),(u,un)=>{
      const covers=ui(x=>ii(M(x,a),xa=>ui(y=>ii(M(y,x),yx=>{
        const witness=E(x=>C(M(x,a),M(y,x)));
        return app(ar(ue(un,y)),ei(witness,x,ai(xa,yx)));
      }))));
      return open(ue(hw,u),(r,order)=>app(us(app(imported,hs),a,u,r),order,covers,hf));
    });
  })))));
  const sourceProof=bridge.emit([],[]),sourceGoal=db(bridge.goal);
  const expected=[">",sep,[">",union,[">",db(allWO),choice]]];
  const source=kernel(0,[],sourceProof,false,"CL");
  require(same(source.goal,expected)&&same(sourceGoal,expected),"source bridge goal mismatch");
  // This proof is a closed logical implication. It carries explicit axiom
  // formulas as hypotheses and therefore uses no import certificates.
  const opts={sourceTheory:"CL",targetTheory:"CL",classDef:defs.L,certificates:[]};
  const compiled=compile(0,[],sourceProof,opts);
  function guard(p){
    const [o,a,b]=p;if(o==="A")return ["A",[">",["G",0],guard(a)]];
    if(o==="E")return ["E",["&",["G",0],guard(a)]];
    if(["&","|",">"].includes(o))return [o,guard(a),guard(b)];return p;
  }
  const target=guard(expected),targetChoice=guard(choice),targetSep=guard(sep),targetUnion=guard(union),targetWO=guard(db(allWO));
  require(same(compiled.target.goal,target)&&compiled.targetCtx.length===0,"guarded conclusion mismatch");
  require(same(target,[">",targetSep,[">",targetUnion,[">",targetWO,targetChoice]]]),"independent target contract mismatch");
  const cut=["iE",["iE",["iE",["h",0],["h",1]],["h",2]],["h",3]];
  const cutCtx=[target,targetSep,targetUnion,targetWO],checkedCut=kernel(0,cutCtx,cut,true,"CL",defs.L);
  require(same(checkedCut.goal,targetChoice),"exact Choice cut mismatch");
  // A separate conversion confirms the fully expanded pinned L endpoint.
  const expanded=expandClass(targetChoice,defs.L),converted=kernel(0,[targetChoice],["conv",expanded,["h",0]],true,"CL",defs.L);
  require(same(converted.goal,expanded),"expanded Choice mismatch");
  const controls=[
    ()=>kernel(0,[],original.proof,false,"CL"),
    ()=>kernel(0,[],["axiom",specChoice],false,"ZF"),
    ()=>kernel(0,cutCtx.slice(0,3),cut,true,"CL",defs.L),
    ()=>kernel(0,[target,targetUnion,targetSep,targetWO],cut,true,"CL",defs.L),
    ()=>kernel(0,[target,targetSep,targetUnion,db(allWO)],cut,true,"CL",defs.L),
    ()=>kernel(0,[targetChoice],["conv",expanded,["h",0]],true,"CL",["=",0,0]),
    ()=>compile(0,[],["axiom",specChoice],{sourceTheory:"ZFC",targetTheory:"ZF",classDef:defs.L,certificates:[]})
  ];
  for(const f of controls)require(rejects(f),"negative control accepted");
  require(scoped(target,0,true)&&scoped(expanded,0,false),"endpoint scope");
  const receipt={experiment:"ACE-03Y-01",scope:"conditional exact relativized disjoint-family Choice; selector Separation, Union and internal well-orderability remain explicit premises",pinned_L_unchanged:true,source_axiom_leaves:axiomLeaves,distinct_source_axioms:specs.size,selector_schema:sepSpec,checks:{prior_ambient_choice:originalCheck.visits,axiom_abstracted_choice:lemma.visits,source_bridge:source.visits,relativized_bridge:compiled.target.visits,exact_choice_cut:checkedCut.visits,expanded_choice_conversion:converted.visits},negative_controls:controls.length,source_theory:"CL",target_theory:"CL",external_context_count_for_conditional:compiled.targetCtx.length,choice_imports:0};  return emitProofs ? {receipt, bridge:{goal:target,proof:compiled.proof}} : receipt;
}

export { runInternalChoiceBridge };

const pinned=JSON.parse(readFileSync(new URL("./L_formula.json",import.meta.url),"utf8"));
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(runInternalChoiceBridge({kernel,same,scoped,compile,expandClass,rejects,definition,buildWellOrder,pinned}),null,2));
