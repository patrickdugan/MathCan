// MM-GYM-01: fixed-prefix, uncompressed Metamath proof replay and masked-step tasks.
// This is deliberately a restricted training oracle, not a complete Metamath parser.
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
function makeEngine(variables, floating, assertions, activeDV=[]) {
  const labels = [...Object.keys(floating), ...Object.keys(assertions)];
  const varSet = new Set(variables);
  const pairKey = (x,y) => [x,y].sort().join(" ");
  const dvSet = new Set(activeDV.map(([x,y])=>pairKey(x,y)));
  const same = (x,y) => x.length===y.length && x.every((v,i)=>v===y[i]);
  function execute(proof,target) {
    const stack=[];
    let maxStack=0;
    const fail=(reason,step)=>({ok:false,reason,step,maxStack});
    if(!Array.isArray(proof)||!Array.isArray(target)) return fail("bad input",-1);
    for(let i=0;i<proof.length;i++){
      const label=proof[i];
      if(typeof label!=="string") return fail("non-string action",i);
      if(Object.hasOwn(floating,label)){
        stack.push(floating[label]);
      } else if(Object.hasOwn(assertions,label)){
        const rule=assertions[label], n=rule.f.length+rule.e.length;
        if(stack.length<n) return fail("underflow",i);
        const entries=stack.splice(stack.length-n,n);
        const subst=new Map();
        for(let j=0;j<rule.f.length;j++){
          const [type,v]=rule.f[j], entry=entries[j];
          if(entry[0]!==type||entry.length<2) return fail("floating type",i);
          subst.set(v,entry.slice(1));
        }
        const instantiate=expr=>expr.flatMap(t=>subst.has(t)?subst.get(t):[t]);
        for(let j=0;j<rule.e.length;j++){
          if(!same(entries[rule.f.length+j],instantiate(rule.e[j]))) return fail("essential hypothesis",i);
        }
        for(const [x,y] of rule.d){
          for(const a of subst.get(x).filter(t=>varSet.has(t))){
            for(const b of subst.get(y).filter(t=>varSet.has(t))){
              if(a===b||!dvSet.has(pairKey(a,b))) return fail("distinct variables",i);
            }
          }
        }
        stack.push(instantiate(rule.c));
      } else {
        return fail("unknown or untrusted label",i);
      }
      maxStack=Math.max(maxStack,stack.length);
    }
    if(stack.length!==1) return fail("final stack size",proof.length);
    if(!same(stack[0],target)) return fail("wrong statement",proof.length);
    return {ok:true,maxStack};
  }
  return {labels,execute};
}
function makeGym() {
  const I=(a,b)=>[a,b];
  const tokens=f=>typeof f==="string"?[f]:["(",...tokens(f[0]),"->",...tokens(f[1]),")"];
  const w=f=>["wff",...tokens(f)];
  const th=f=>["|-",...tokens(f)];
  const fl={wph:w("ph"),wps:w("ps"),wch:w("ch")};
  const rule=(vars,e,c)=>({f:vars.map(v=>["wff",v]),e,c,d:[]});
  const rules={
    wi:rule(["ph","ps"],[],w(I("ph","ps"))),
    "ax-1":rule(["ph","ps"],[],th(I("ph",I("ps","ph")))),
    "ax-2":rule(["ph","ps","ch"],[],th(I(I("ph",I("ps","ch")),I(I("ph","ps"),I("ph","ch"))))),
    "ax-mp":rule(["ph","ps"],[th("ph"),th(I("ph","ps"))],th("ps"))
  };
  const engine=makeEngine(["ph","ps","ch"],fl,rules);
  const syntax=f=>typeof f==="string"?[{ph:"wph",ps:"wps",ch:"wch"}[f]]:[...syntax(f[0]),...syntax(f[1]),"wi"];
  const ax1=(a,b)=>[...syntax(a),...syntax(b),"ax-1"];
  const ax2=(a,b,c)=>[...syntax(a),...syntax(b),...syntax(c),"ax-2"];
  const mp=(a,b,pa,pab)=>[...syntax(a),...syntax(b),...pa,...pab,"ax-mp"];
  function identity(f) {
    const ff=I(f,f), A=I(f,ff), B=I(f,I(ff,f)), C=I(A,ff);
    return {target:th(ff),proof:mp(A,ff,ax1(f,f),mp(B,C,ax1(f,ff),ax2(f,ff,f)))};
  }
  const prefix=[
    "$c wff |- ( -> ) $.",
    "$v ph ps ch $.",
    "wph $f wff ph $.",
    "wps $f wff ps $.",
    "wch $f wff ch $.",
    "wi $a wff ( ph -> ps ) $.",
    "ax-1 $a |- ( ph -> ( ps -> ph ) ) $.",
    "ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.",
    "${",
    "  mp.1 $e |- ph $.",
    "  mp.2 $e |- ( ph -> ps ) $.",
    "  ax-mp $a |- ps $.",
    "$}"
  ].join("\n")+"\n";
  const declaration=(label,target,proof)=>`${label} $p ${target.join(" ")} $= ${proof.join(" ")} $.\n`;
  return {...engine,identity,prefix,declaration};
}
function pilot() {
  const g=makeGym();
  const ensure=(b,s)=>{if(!b)throw new Error(s);};
  const formulas=[["ph","ps"]];
  for(let n=1;n<=3;n++){
    const out=[];
    for(let i=0;i<n;i++)for(const a of formulas[i])for(const b of formulas[n-1-i])out.push([a,b]);
    formulas.push(out);
  }
  const inputs=[],oracle=[],negatives=[];
  let validDB=g.prefix, checked=0, accepted=0, rejected=0, alternative=0, maxStack=0, steps=0;
  const counts={train:0,dev:0,depth_challenge:0};
  for(let n=0;n<formulas.length;n++){
    for(const f of formulas[n]){
      const {target,proof}=g.identity(f);
      const res=g.execute(proof,target);
      ensure(res.ok,"constructed proof failed");
      maxStack=Math.max(maxStack,res.maxStack);
      steps+=proof.length;
      const id="mm"+String(inputs.length).padStart(3,"0");
      const split=n<2?"train":n===2?"dev":"depth_challenge";
      counts[split]++;
      const mask=(inputs.length*17+n*7)%proof.length;
      const prefix=proof.slice(0,mask),suffix=proof.slice(mask+1);
      const answers=[];
      for(const label of g.labels){
        const filled=[...prefix,label,...suffix];
        if(g.execute(filled,target).ok){
          answers.push(label);
          validDB+=g.declaration(id+"-"+answers.length,target,filled);
        }else{
          negatives.push({id:id+"-"+label,source:g.prefix+g.declaration("candidate",target,filled)});
        }
      }
      ensure(answers.includes(proof[mask]),"gold label rejected");
      inputs.push({id,split,implication_nodes:n,target,prefix,suffix,actions:g.labels});
      oracle.push({id,accepted_actions:answers,reference_action:proof[mask],reference_steps:proof.length});
      for(let j=0;j<proof.length;j++){
        for(const label of g.labels){
          if(label===proof[j])continue;
          const mutant=proof.slice();mutant[j]=label;
          checked++;
          if(g.execute(mutant,target).ok){accepted++;alternative++;}else rejected++;
        }
      }
    }
  }
  const one=g.identity("ph"),other=g.identity("ps");
  ensure(!g.execute([],one.target).ok,"empty proof");
  ensure(!g.execute(one.proof,other.target).ok,"statement mismatch");
  ensure(!g.execute([...one.proof,"wph"],one.target).ok,"extra stack");
  ensure(!g.execute(["?"],one.target).ok,"incomplete proof");
  ensure(!g.execute(["mp.1"],one.target).ok,"escaped hypothesis");
  ensure(!g.execute(["constructor"],one.target).ok,"prototype label");
  ensure(!g.execute([null],one.target).ok,"non-string action");
  const fl={vx:["setvar","x"],vy:["setvar","y"]};
  const rules={pair:{f:[["setvar","x"],["setvar","y"]],e:[],d:[["x","y"]],c:["pairtype","x","y"]}};
  const dv=makeEngine(["x","y"],fl,rules,[["x","y"]]);
  ensure(dv.execute(["vx","vy","pair"],["pairtype","x","y"]).ok,"valid DV");
  ensure(dv.execute(["vx","vx","pair"],["pairtype","x","x"]).reason==="distinct variables","DV self clash");
  ensure(makeEngine(["x","y"],fl,rules).execute(["vx","vy","pair"],["pairtype","x","y"]).reason==="distinct variables","missing DV");
  const dvPrefix="$c setvar pairtype $.\n$v x y $.\nvx $f setvar x $.\nvy $f setvar y $.\n${\n$d x y $.\npair $a pairtype x y $.\n$}\n";
  const dvValid=dvPrefix+"${\n$d x y $.\ndvok $p pairtype x y $= vx vy pair $.\n$}\n";
  const dvInvalid=[{id:"dv-self",source:dvPrefix+"dvbad $p pairtype x x $= vx vx pair $.\n"},{id:"dv-missing",source:dvPrefix+"dvbad $p pairtype x y $= vx vy pair $.\n"}];
  negatives.push(...dvInvalid);
  const receipt={schema:"mm-gym-01-v1",cases:inputs.length,split_counts:counts,reference_steps:steps,max_stack:maxStack,mutation_checks:checked,mutations_accepted:accepted,mutations_rejected:rejected,alternative_single_step_proofs:alternative,masked_valid_candidates:oracle.reduce((s,r)=>s+r.accepted_actions.length,0),masked_invalid_candidates:negatives.length-dvInvalid.length,negative_dv_cases:dvInvalid.length,local_assertions:10,scope:"fixed uncompressed implicational fixture plus separate synthetic DV controls; no set.mm or external verifier run"};
  ensure(checked===accepted+rejected,"mutation accounting");
  return {inputs,oracle,negatives,validDB,dvValid,receipt};
}
const out=process.argv[2];
const r=pilot();
if(out){
  mkdirSync(join(out,"invalid"),{recursive:true});
  const write=(name,data)=>writeFileSync(join(out,name),data);
  write("inputs.jsonl",r.inputs.map(x=>JSON.stringify(x)).join("\n")+"\n");
  write("oracle.jsonl",r.oracle.map(x=>JSON.stringify(x)).join("\n")+"\n");
  write("valid.mm",r.validDB);
  write("dv-valid.mm",r.dvValid);
  for(const x of r.negatives)write(join("invalid",x.id+".mm"),x.source);
  write("receipt.json",JSON.stringify(r.receipt,null,2)+"\n");
}
console.log(JSON.stringify(r.receipt,null,2));
export {makeEngine,makeGym,pilot};
