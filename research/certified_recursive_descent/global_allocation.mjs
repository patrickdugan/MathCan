// CRD-14A: static product allocation and receding static-utility lookahead.
import {readFileSync} from "node:fs";
import {ok,sum,fixture,Problem,Engine,forwardWorld,bootstrap} from "./information_gain.mjs";
const top14=(p,k)=>sum(p.slice().sort((a,b)=>b-a).slice(0,Math.max(0,k)));
const pred14=(j,x)=>j===0?x%2:j===1?Number(x<3):Number(x%3===0);
const quant14=x=>Math.round(x*1e12)/1e12;
function local14(l,id,b,stat){
 if(id<0||b<=0)return 0;
 const s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
 if(k<=0)return 0;
 if(k>=3)return s.mass;
 if(m===0)return top14(s.p.slice(0,3),k);
 stat.nontrivial++;
 let v=0;
 for(let u=0;u<(1<<m);u++){
  const w=s.p.slice(0,3);
  for(let t=0;t<m;t++){
   const j=s.stage+t,a=l.spec.sensors[j]/100,bit=(u>>t)&1;
   for(let x=0;x<3;x++)w[x]*=pred14(j,x)===bit?a:1-a;
  }
  stat.patterns++;stat.likelihoodProducts+=3*m;v+=top14(w,k);
 }
 return v;
}
const newStats14=()=>({localCalls:0,localHits:0,nontrivial:0,patterns:0,likelihoodProducts:0,allocCalls:0,allocHits:0,allocCells:0,allocCombinations:0,h1Calls:0,h1Hits:0,h1Actions:0,h1Outcomes:0,h2Actions:0,h2Outcomes:0,dominanceChecks:0,minSlack:Infinity});
class AllocationProblem extends Problem{
 constructor(root,cap){super(root,cap);this.values=this.local.map(()=>new Map());this.allocCache=new Map();this.h1Cache=new Map();this.work=newStats14()}
 val(i,id,b){
  const key=id+":"+b,cache=this.values[i];
  if(cache.has(key)){this.work.localHits++;return cache.get(key)}
  this.work.localCalls++;const v=local14(this.local[i],id,b,this.work);
  ok(v>=-1e-12&&v<=1+1e-12,"local value range");cache.set(key,v);return v;
 }
 alloc(s,b){
  const key=b+":"+s.join(",");
  if(this.allocCache.has(key)){this.work.allocHits++;return this.allocCache.get(key)}
  this.work.allocCalls++;
  const n=s.length,dp=Array.from({length:n+1},()=>Array(b+1).fill(null));
  for(let r=0;r<=b;r++)dp[n][r]={failure:1,plan:[]};
  for(let i=n-1;i>=0;i--)for(let r=0;r<=b;r++){
   let best=null;this.work.allocCells++;
   for(let t=0;t<=r;t++){
    const tail=dp[i+1][r-t],failure=(1-this.val(i,s[i],t))*tail.failure;
    this.work.allocCombinations++;
    // First lexicographic allocation on near ties, no effect on legality.
    if(!best||failure<best.failure-1e-15)best={failure,plan:[t,...tail.plan]};
   }
   dp[i][r]=best;
  }
  const z=dp[0][b],out={v:1-z.failure,plan:z.plan};
  ok(sum(out.plan)<=b,"static allocation budget");this.allocCache.set(key,out);return out;
 }
 h1(s,b){
  if(b<=0)return {v:0,a:null};
  const key=b+":"+s.join(",");
  if(this.h1Cache.has(key)){this.work.h1Hits++;return this.h1Cache.get(key)}
  this.work.h1Calls++;
  const actions=this.legal(s,b);let best={v:0,a:null};
  for(const a of actions){
   const os=this.outcomes(s,a);this.work.h1Actions++;this.work.h1Outcomes+=os.length;this.scoreEvals++;
   const v=sum(os.map(o=>o.p*(o.hit?1:this.alloc(o.s,b-1).v)));
   if(!best.a||quant14(v)>quant14(best.v)||(quant14(v)===quant14(best.v)&&a.id>best.a.id))best={v,a};
  }
  const f=this.alloc(s,b).v,slack=best.v-f;
  this.work.dominanceChecks++;this.work.minSlack=Math.min(this.work.minSlack,slack);
  ok(slack>=-1e-10,"one-step static dominance "+JSON.stringify({s,b,slack,cap:this.cap}));
  this.h1Cache.set(key,best);return best;
 }
 choose(s,b,kind,w){
  if(kind==="receding1")return this.h1(s,b).a;
  if(kind!=="receding2")return super.choose(s,b,kind,w);
  let best={v:0,a:null};
  for(const a of this.legal(s,b)){
   const os=this.outcomes(s,a);this.work.h2Actions++;this.work.h2Outcomes+=os.length;this.scoreEvals++;
   const v=sum(os.map(o=>o.p*(o.hit?1:this.h1(o.s,b-1).v)));
   if(!best.a||quant14(v)>quant14(best.v)||(quant14(v)===quant14(best.v)&&a.id>best.a.id))best={v,a};
  }
  // A lower-bound lookahead is not itself the expected value of its closed-loop policy.
  return best.a;
 }
}
function staticWitness(P,b,plan){
 const memo=new Map();let decisions=0,transitions=0;
 function rec(s,left,b){
  left=left.slice();
  // The root witness uses index order. Once a branch's reserved actions are
  // exhausted or no local action is feasible, its residual allocation is lost.
  for(let i=0;i<s.length;i++)if(!P.local[i].actions(s[i],left[i]).length)left[i]=0;
  const key=b+":"+s.join(",")+":"+left.join(",");
  if(memo.has(key))return memo.get(key);
  const i=left.findIndex(t=>t>0);
  if(i<0||b<=0)return {v:0,calls:0,sensors:0,probes:0,evictions:0,peak:P.active(s).length,action:null};
  const l=P.local[i],la=l.actions(s[i],left[i]);
  const t=la.slice().sort((a,b)=>a===0||b===0?b-a:l.at(s[i]).p[b-1]-l.at(s[i]).p[a-1]||b-a)[0];
  const a=P.legal(s,b).filter(a=>a.i===i&&a.t===t&&(a.evict<0||left[a.evict]===0)).sort((a,b)=>b.id-a.id)[0];
  ok(a,"static witness legal action");
  left[i]--;const os=P.outcomes(s,a);
  decisions++;transitions+=os.length;
  const out={v:0,calls:1,sensors:Number(a.t===0),probes:Number(a.t!==0),evictions:Number(a.evict>=0),peak:P.active(s).length,action:a};
  for(const o of os){
   if(o.hit){out.v+=o.p;continue}
   const q=rec(o.s,left,b-1);
   for(const k of ["v","calls","sensors","probes","evictions"])out[k]+=o.p*q[k];
   out.peak=Math.max(out.peak,q.peak);
  }
  ok(out.calls<=b+1e-10&&out.peak<=P.cap,"static witness bounds");
  memo.set(key,out);return out;
 }
 const r=rec(P.initial(),plan,b);return {...r,decisions,transitions};
}
function brute14(P,s,b){
 let best=0,count=0;
 function rec(i,r,fail){
  if(i===s.length){best=Math.max(best,1-fail);count++;return}
  for(let t=0;t<=r;t++)rec(i+1,r-t,fail*(1-P.val(i,s[i],t)));
 }rec(0,b,1);return {best,count};
}
function costs14(){return {...newStats14(),states:0,transitions:0,actions:0,scores:0,localDPStates:0,localDPTransitions:0,localDPQueries:0,rolloutStates:0,rolloutTransitions:0,rolloutLookaheadTransitions:0}}
function accumulate14(cost,P,E){
 if(E){cost.states+=E.stats.states;cost.transitions+=E.stats.transitions;cost.actions+=E.stats.actions}
 cost.scores+=P.scoreEvals;
 for(const l of P.local){cost.localDPStates+=l.stats.states;cost.localDPTransitions+=l.stats.transitions;cost.localDPQueries+=l.stats.queries}
 if(P.rollout){cost.rolloutStates+=P.rollout.stats.states;cost.rolloutTransitions+=P.rollout.stats.transitions;cost.rolloutLookaheadTransitions+=P.rollout.stats.lookaheadTransitions}
 if(P.work)for(const k of Object.keys(P.work)){if(k==="minSlack")cost[k]=Math.min(cost[k],P.work[k]);else cost[k]+=P.work[k]}
}
function finite14(frozen){
 const start=Date.now(),roots=Array.from({length:192},(_,i)=>fixture(2040001+i,3,3)),budgets=[4,6],
 kinds=["optimal","static","receding1","receding2","depth","marginal","sensor","local","rollout","recurrent"];
 const rows=[],paired=[],costs=[],audit={witnessChecks:0,bruteChecks:0,bruteCombinations:0,monotonicChecks:0,worldChecks:0,worlds:0,maxWorldError:0,policyRootBudgets:0,staticDominanceChecks:0,minRecedingSlack:Infinity};
 for(const cap of [1,2]){
  const all=Object.fromEntries(budgets.map(b=>[b,Object.fromEntries(kinds.map(k=>[k,[]]))]));
  const C=Object.fromEntries(kinds.map(k=>[k,costs14()]));
  for(let i=0;i<roots.length;i++){
   const root=roots[i],opt=[],staticValues=[];
   for(const kind of kinds){
    const isAllocation=["static","receding1","receding2"].includes(kind),P=isAllocation?new AllocationProblem(root,cap):new Problem(root,cap);
    const E=kind==="static"?null:new Engine(P,kind,kind==="recurrent"?frozen.training.choices.recurrent.weights:null);
    const values=[];
    for(let j=0;j<budgets.length;j++){
     const b=budgets[j];let v;
     if(kind==="static"){
      const z=P.alloc(P.initial(),b);v=staticWitness(P,b,z.plan);staticValues.push(z.v);
      ok(Math.abs(z.v-v.v)<1e-10,"static witness value");audit.witnessChecks++;
      C[kind].states+=v.decisions;C[kind].transitions+=v.transitions;
      if(i<16){const brute=brute14(P,P.initial(),b);ok(Math.abs(brute.best-z.v)<1e-10,"brute allocation");audit.bruteChecks++;audit.bruteCombinations+=brute.count}
      // Monotonicity audit uses a separate allocation object below.
     }else v=E.rec(P.initial(),b);
     if(kind==="optimal")opt.push(v);
     else ok(v.v<=opt[j].v+1e-10,"oracle domination");
     if(kind==="receding1"){
      const slack=v.v-staticValues[j];ok(slack>=-1e-10,"receding policy dominance");
      audit.staticDominanceChecks++;audit.minRecedingSlack=Math.min(audit.minRecedingSlack,slack);
     }
     values.push(v);audit.policyRootBudgets++;
     all[b][kind].push({v:v.v,regret:opt[j].v-v.v,calls:v.calls,sensors:v.sensors,probes:v.probes,evictions:v.evictions,peak:v.peak,firstDifferent:Number(v.action?.id!==opt[j].action?.id)});
    }
    if(kind==="static"){
     const A=new AllocationProblem(root,cap);let prev=0;
     for(let b=0;b<=6;b++){const v=A.alloc(A.initial(),b).v;ok(v>=prev-1e-12,"static monotonicity");prev=v;audit.monotonicChecks++}
    }
    if(i<4&&["receding1","receding2"].includes(kind)){
     const f=forwardWorld(root,E,6),err=Math.abs(f.value-values[1].v);
     ok(err<1e-10,"independent world replay");audit.worldChecks++;audit.worlds+=f.worlds;audit.maxWorldError=Math.max(audit.maxWorldError,err);
    }
    accumulate14(C[kind],P,E);
   }
  }
  for(const b of budgets){
   for(const kind of kinds){const a=all[b][kind],mean=k=>sum(a.map(x=>x[k]))/a.length;rows.push({cap,budget:b,kind,roots:a.length,expectedSuccess:mean("v"),meanRegret:mean("regret"),expectedCalls:mean("calls"),expectedSensors:mean("sensors"),expectedProbes:mean("probes"),expectedEvictions:mean("evictions"),peakActive:Math.max(...a.map(x=>x.peak)),firstDifferent:sum(a.map(x=>x.firstDifferent))})}
   for(const kind of ["receding1","receding2"])for(const ref of kinds.filter(x=>x!==kind)){
    const a=all[b][kind],other=all[b][ref],diff=a.map((x,i)=>x.v-other[i].v);
    paired.push({cap,budget:b,kind,ref,...bootstrap(diff,(0xCE140000+cap*1000+b*100+kinds.indexOf(ref)+10*kinds.indexOf(kind))>>>0)});
   }
  }
  for(const c of Object.values(C))if(!Number.isFinite(c.minSlack))c.minSlack=null;
  costs.push({cap,acrossBudgets:C});
 }
 return {status:"PASS",scope:"independent finite decision model; static witness and receding lower-bound control",rows,paired,costs,audit,elapsedMs:Date.now()-start};
}
const frozen14=JSON.parse(readFileSync(new URL("./information_gain_receipt.json",import.meta.url),"utf8"));
console.log(JSON.stringify(finite14(frozen14),null,2));
