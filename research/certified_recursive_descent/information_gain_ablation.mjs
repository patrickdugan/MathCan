// CRD-11B: preregistered fresh-root feature ablation.
import {readFileSync} from "node:fs";
import {rng} from "./search.mjs";
import {F,ok,sum,zeros,fixture,Problem,Engine,teacher,modelKinds,init,grad,predict,forwardWorld,bootstrap} from "./information_gain.mjs";
const MASK=new Set([9,10,12,18]);
class CheapProblem extends Problem {
 features(s,a,b){
  this.featureEvals++;
  const i=a.i,l=this.local[i],v=l.at(s[i]),remain=l.L-v.stage,reveal=a.t===0;
  const other=s.map((id,j)=>({id,j})).filter(o=>o.j!==i&&o.id>=0);
  const otherProbe=Math.max(0,...other.map(({id,j})=>this.local[j].at(id).stage===this.local[j].L?this.local[j].at(id).max:0));
  const next=reveal?l.nextBest(s[i]):0,ev=a.evict;
  const x=[Number(reveal),b/8,remain/3,reveal?0:v.p[a.t-1],v.max,v.mass,v.top2,next,reveal?next-v.max:0,0,0,otherProbe,0,sum(other.map(({id,j})=>this.local[j].at(id).mass))/3,this.active(s).length/3,this.cap/3,Number(ev>=0),this.evictMass(s,a),0,this.sensor(s,a)];
  ok(x.length===F&&x.every(Number.isFinite),"cheap features");return x;
 }
}
function validateCheap(roots,kind,w){
 let v=0,calls=0;
 for(let i=0;i<roots.length;i++){
  const P=new CheapProblem(roots[i],1+i%2),E=new Engine(P,kind,w),z=E.rec(P.initial(),3+i%3);v+=z.v;calls+=z.calls;
  ok(P.local.every(l=>l.stats.states===0&&l.stats.transitions===0&&l.stats.queries===0),"validation local DP");
 }
 return {value:v/roots.length,calls:calls/roots.length};
}
function trainCheap(data,val){
 const choices={},history=[];
 const states=data.states.map(rows=>rows.map(row=>({x:row.x.map((v,i)=>MASK.has(i)?0:v),y:row.y})));
 for(const kind of modelKinds){
  const w=init(kind),r=rng(711);let best=null;
  for(let ep=1;ep<=16;ep++){
   for(let b=0;b<64;b++){
    const g=zeros(w.length);
    for(let j=0;j<32;j++){const state=states[Math.floor(r()*states.length)],row=state[Math.floor(r()*state.length)];grad(kind,w,row.x,row.y,g)}
    for(let j=0;j<w.length;j++)w[j]-=.08*g[j]/32;
   }
   if([1,4,8,16].includes(ep)){
    const m=validateCheap(val,kind,w),loss=sum(states.map(rows=>sum(rows.map(row=>(predict(kind,w,row.x)-row.y)**2))/rows.length))/states.length;
    const c={kind,epoch:ep,...m,trainMSE:loss,weights:w.slice()};history.push({kind,epoch:ep,...m,trainMSE:loss});
    if(!best||m.value>best.value+1e-14||(Math.abs(m.value-best.value)<=1e-14&&m.calls<best.calls-1e-14))best=c;
   }
  }choices[kind]=best;
 }return {choices,history};
}
function ablate11(frozen){
 const start=Date.now(),data=teacher(),val=Array.from({length:96},(_,i)=>fixture(1750001+i,2,2)),trained=trainCheap(data,val);
 const roots=Array.from({length:192},(_,i)=>fixture(1780001+i,3,3));
 const kinds=["optimal","sensor","marginal","local","rollout",...modelKinds.map(k=>"full_"+k),...modelKinds.map(k=>"cheap_"+k)];
 const rows=[],paired=[],all=Object.fromEntries([4,6].map(b=>[b,Object.fromEntries(kinds.map(k=>[k,[]]))]));
 const costs=Object.fromEntries(kinds.map(k=>[k,{states:0,transitions:0,actions:0,scoreEvals:0,features:0,localStates:0,localTransitions:0,localQueries:0,rolloutStates:0,rolloutTransitions:0,rolloutLookaheadTransitions:0}]));
 let independentChecks=0,worlds=0,maxError=0,policyRootBudgets=0,featureChecks=0;
 for(let i=0;i<roots.length;i++){
  const root=roots[i];let opt=[];
  for(const k of kinds){
   const cheap=k.startsWith("cheap_"),full=k.startsWith("full_"),kind=cheap||full?k.split("_")[1]:k;
   const P=cheap?new CheapProblem(root,2):new Problem(root,2),w=cheap?trained.choices[kind].weights:full?frozen.training.choices[kind].weights:null,E=new Engine(P,kind,w);
   for(let j=0;j<2;j++){
    const b=[4,6][j],v=E.rec(P.initial(),b);
    if(k==="optimal")opt.push(v.v);else ok(v.v<=opt[j]+1e-10,"optimal dominates");
    all[b][k].push({v:v.v,calls:v.calls,sensors:v.sensors,probes:v.probes,evictions:v.evictions,peak:v.peak,regret:opt[j]-v.v});policyRootBudgets++;
    if(j===1&&i<4&&["optimal","full_recurrent","cheap_recurrent"].includes(k)){
     const check=forwardWorld(root,E,b),err=Math.abs(check.value-v.v);ok(err<1e-10,"world replay");independentChecks++;worlds+=check.worlds;maxError=Math.max(maxError,err);
    }
   }
   const c=costs[k];for(const x of ["states","transitions","actions"])c[x]+=E.stats[x];
   c.scoreEvals+=P.scoreEvals;c.features+=P.featureEvals;
   for(const l of P.local){c.localStates+=l.stats.states;c.localTransitions+=l.stats.transitions;c.localQueries+=l.stats.queries}
   if(P.rollout){c.rolloutStates+=P.rollout.stats.states;c.rolloutTransitions+=P.rollout.stats.transitions;c.rolloutLookaheadTransitions+=P.rollout.stats.lookaheadTransitions}
   if(cheap){ok(P.local.every(l=>l.stats.states===0&&l.stats.transitions===0&&l.stats.queries===0),"local DP gate");featureChecks++}
  }
 }
 for(const b of [4,6]){
  for(const k of kinds){const a=all[b][k],mean=x=>sum(a.map(v=>v[x]))/a.length;rows.push({budget:b,kind:k,roots:a.length,expectedSuccess:mean("v"),meanRegret:mean("regret"),expectedCalls:mean("calls"),expectedSensors:mean("sensors"),expectedProbes:mean("probes"),expectedEvictions:mean("evictions"),peakActive:Math.max(...a.map(v=>v.peak))})}
  for(const ref of kinds.filter(x=>x!=="cheap_recurrent")){
   const a=all[b].cheap_recurrent,other=all[b][ref],diff=a.map((v,i)=>v.v-other[i].v);
   paired.push({budget:b,kind:"cheap_recurrent",ref,...bootstrap(diff,(0xCE110000+b*100+kinds.indexOf(ref))>>>0)});
  }
 }
 return {status:"PASS",scope:"local-DP feature ablation; zero local Bellman calls in cheap heads, not a physical performance measurement",mask:[...MASK],teacher:data.stat,training:trained,rows,paired,costsAcrossBudgets:costs,audit:{policyRootBudgets,independentChecks,worlds,maxError,zeroLocalDPChecks:featureChecks},elapsedMs:Date.now()-start};
}
const frozen=JSON.parse(readFileSync(new URL("./information_gain_receipt.json",import.meta.url),"utf8"));
console.log(JSON.stringify(ablate11(frozen),null,2));
