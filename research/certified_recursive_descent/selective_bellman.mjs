import {pathToFileURL} from "node:url";
// CRD-15: selective interval Bellman refinement on the frozen finite model.
import {readFileSync} from "node:fs";
import {ok,sum,fixture,Problem,Engine,forwardWorld,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
const EPS15=1e-10,quant15=x=>Math.round(x*1e12)/1e12;
const key15=(s,b)=>b+":"+s.join(",");
const clip15=x=>Math.max(0,Math.min(1,x));
function fresh15(){return {decisions:0,certified:0,uncertified:0,nodeCreated:0,nodeExpanded:0,outcomes:0,actions:0,reverseLinks:0,backups:0,propagations:0,leafSelections:0,zeroAffordable:0,oneAffordable:0,allReady:0,peakDAG:0,peakActionEdges:0,maxGap:0,sumGap:0}}
class Planner15{
 constructor(P,limit){
  this.P=P;this.limit=limit;this.cache=new Map();this.work=fresh15();
 }
 node(s,b){
  const key=key15(s,b);
  if(this.cache.has(key))return this.cache.get(key);
  const P=this.P,aff=s.map((id,i)=>{
   if(id<0||b<=0)return null;
   const l=P.local[i],v=l.at(id),m=l.L-v.stage;
   return v.mass>0&&m+1<=b?{i,id,m,mass:v.mass}:null;
  }).filter(Boolean);
  let L=0,U=0;
  if(!aff.length)this.work.zeroAffordable++;
  else if(aff.length===1){
   this.work.oneAffordable++;L=U=P.val(aff[0].i,aff[0].id,b);
  }else{
   L=P.alloc(s,b).v;
   if(aff.every(x=>x.m===0)){this.work.allReady++;U=L}
   else U=1-aff.reduce((p,x)=>p*(1-x.mass),1);
  }
  ok(L<=U+EPS15&&L>=-EPS15&&U<=1+EPS15,"initial envelope");
  L=clip15(L);U=clip15(Math.max(L,U));
  const n={s:s.slice(),b,key,L,U,actions:null,parents:new Set()};
  this.cache.set(key,n);this.work.nodeCreated++;
  this.work.peakDAG=Math.max(this.work.peakDAG,this.cache.size);
  return n;
 }
 range(a){
  let L=0,U=0;
  for(const o of a.os){L+=o.p*(o.hit?1:o.n.L);U+=o.p*(o.hit?1:o.n.U)}
  return {L:clip15(L),U:clip15(U)};
 }
 backup(n){
  if(n.actions===null)return false;
  this.work.backups++;
  const lo=Math.max(0,...n.actions.map(a=>this.range(a).L)),hi=Math.max(0,...n.actions.map(a=>this.range(a).U));
  const L=Math.max(n.L,lo),U=Math.min(n.U,hi);
  ok(L<=U+EPS15,"nonempty backed envelope "+JSON.stringify({key:n.key,L,U,lo,hi}));
  const newL=clip15(L),newU=clip15(Math.max(L,U)),changed=newL!==n.L||newU!==n.U;
  n.L=newL;n.U=newU;return changed;
 }
 propagate(start){
  const ancestors=new Set([start]),stack=[start];
  while(stack.length){const n=stack.pop();for(const p of n.parents)if(!ancestors.has(p)){ancestors.add(p);stack.push(p)}}
  // Children have strictly smaller budgets; each affected node needs one backup.
  const ordered=[...ancestors].sort((a,b)=>a.b-b.b||a.key.localeCompare(b.key));
  for(const n of ordered){if(n!==start)this.work.propagations++;this.backup(n)}
 }
 expand(n){
  ok(n.actions===null&&this.work.nodeExpanded<this.limit,"planning node ceiling");
  n.actions=this.P.legal(n.s,n.b).map(a=>{
   const os=this.P.outcomes(n.s,a).map(o=>{
    this.work.outcomes++;
    if(o.hit)return {p:o.p,hit:true,n:null};
    const ch=this.node(o.s,n.b-1);
    if(!ch.parents.has(n)){ch.parents.add(n);this.work.reverseLinks++}
    return {p:o.p,hit:false,n:ch};
   });
   this.work.actions++;return {a,os};
  });
  this.work.nodeExpanded++;
  this.work.peakActionEdges=Math.max(this.work.peakActionEdges,this.work.outcomes);
  this.propagate(n);
 }
 choices(n){
  return n.actions.map(a=>({...a,...this.range(a)})).sort((a,b)=>quant15(b.L)-quant15(a.L)||b.a.id-a.a.id);
 }
 leaf(n,root=false){
  if(!root&&n.U-n.L<=EPS15/10)return null;
  if(n.actions===null)return n;
  const as=this.choices(n),best=as[0]?.L??0;
  const ranked=as.filter(a=>a.U>best+EPS15/10).sort((a,b)=>quant15(b.U)-quant15(a.U)||b.a.id-a.a.id);
  for(const a of ranked){
   const children=a.os.filter(o=>!o.hit&&o.n.U-o.n.L>EPS15/10).sort((a,b)=>b.p*(b.n.U-b.n.L)-a.p*(a.n.U-a.n.L)||a.n.key.localeCompare(b.n.key));
   for(const o of children){const q=this.leaf(o.n);if(q)return q}
  }return null;
 }
 solve(s,b){
  const root=this.node(s,b);this.expand(root);
  if(!root.actions.length)return {action:null,L:root.L,U:root.U,gap:0,certified:true,ranges:[],work:this.work};
  this.work.decisions++;
  let selected,gap,ranges;
  for(;;){
   const as=this.choices(root);
   selected=as[0];gap=Math.max(0,...as.map(a=>a.U-selected.L));
   ranges=as.map(a=>({id:a.a.id,L:a.L,U:a.U}));
   if(gap<=EPS15||this.work.nodeExpanded>=this.limit)break;
   const next=this.leaf(root,true);ok(next,"unresolved DAG without refinable leaf "+JSON.stringify({s,b,gap,rootL:root.L,rootU:root.U}));
   this.work.leafSelections++;this.expand(next);
  }
  const certified=gap<=EPS15;
  if(certified)this.work.certified++;else this.work.uncertified++;
  this.work.maxGap=gap;this.work.sumGap=gap;
  if(this.limit===Infinity)ok(certified,"unlimited certification");
  return {action:selected.a,L:root.L,U:root.U,gap,certified,ranges,work:this.work};
 }
}
function mergeWork15(a,b){
 for(const k of Object.keys(a)){
  if(k==="peakDAG"||k==="peakActionEdges"||k==="maxGap")a[k]=Math.max(a[k],b[k]);
  else a[k]+=b[k];
 }
}
class Selective15 extends AllocationProblem{
 constructor(root,cap,limit){super(root,cap);this.limit=limit;this.planning=fresh15();this.decisions=new Map()}
 choose(s,b,kind,w){
  if(kind!=="selective")return super.choose(s,b,kind,w);
  if(!this.legal(s,b).length)return null;
  const P=new Planner15(this,this.limit),r=P.solve(s,b);
  ok(r.action&&P.work.nodeExpanded<=this.limit,"selected action / limit");
  mergeWork15(this.planning,r.work);
  this.decisions.set(key15(s,b),{s:s.slice(),b,L:r.L,U:r.U,gap:r.gap,certified:r.certified,action:r.action.id,ranges:r.ranges});
  return r.action;
 }
}
function audit15(P,oracle){
 let states=0,actions=0,certified=0,maxRegret=0,maxViolation=0,maxStateWidth=0,sumRegret=0;
 for(const r of P.decisions.values()){
  const aligned=r.s.map((id,i)=>id<0?id:oracle.P.local[i].intern(P.local[i].at(id).stage,P.local[i].at(id).w));
  const v=oracle.rec(aligned,r.b);
  ok(v.action&&v.qs.length===r.ranges.length,"oracle legal actions");
  maxViolation=Math.max(maxViolation,r.L-v.v,v.v-r.U);
  ok(r.L<=v.v+1e-9&&v.v<=r.U+1e-9,"state enclosure");
  maxStateWidth=Math.max(maxStateWidth,r.U-r.L);
  const map=new Map(v.qs.map(q=>[q.a.id,q.q]));
  for(const a of r.ranges){
   const q=map.get(a.id);ok(q!==undefined,"action alignment");
   maxViolation=Math.max(maxViolation,a.L-q,q-a.U);
   ok(a.L<=q+1e-9&&q<=a.U+1e-9,"action enclosure");actions++;
  }
  const regret=v.v-map.get(r.action);
  ok(regret<=r.gap+1e-9&&regret>=-1e-9,"action regret enclosure");
  if(r.certified){certified++;ok(regret<=EPS15+1e-9,"certified regret")}
  maxRegret=Math.max(maxRegret,regret);sumRegret+=regret;states++;
 }
 return {states,actions,certified,maxRegret,maxViolation,maxStateWidth,sumRegret};
}
function blankCost15(){return {evalStates:0,evalTransitions:0,evalActions:0,scores:0,localDPStates:0,localDPTransitions:0,localDPQueries:0,localCalls:0,localHits:0,patterns:0,likelihoodProducts:0,allocCalls:0,allocHits:0,allocCells:0,allocCombinations:0,h1Calls:0,h1Hits:0,h1Outcomes:0,h2Outcomes:0,planning:fresh15()}}
function cost15(c,P,E){
 c.evalStates+=E.stats.states;c.evalTransitions+=E.stats.transitions;c.evalActions+=E.stats.actions;c.scores+=P.scoreEvals;
 for(const l of P.local){c.localDPStates+=l.stats.states;c.localDPTransitions+=l.stats.transitions;c.localDPQueries+=l.stats.queries}
 if(P.work)for(const k of ["localCalls","localHits","patterns","likelihoodProducts","allocCalls","allocHits","allocCells","allocCombinations","h1Calls","h1Hits","h1Outcomes","h2Outcomes"])c[k]+=P.work[k];
 if(P.planning)mergeWork15(c.planning,P.planning);
}
function experiment15(frozen,regime){
 const begin=Date.now(),standard=regime==="standard",n=standard?128:64,b=standard?6:8,caps=standard?[1,2]:[2];
 const roots=Array.from({length:n},(_,i)=>fixture((standard?2120001:2130001)+i,3,standard?3:4));
 const kinds=["optimal","receding1","receding2","sensor","local","recurrent","selective4","selective16","selective64","unlimited"],limits={selective4:4,selective16:16,selective64:64,unlimited:Infinity};
 const rows=[],paired=[],costs=[],audits=[],globalAudit={policyRootBudgets:0,worldChecks:0,worlds:0,maxWorldError:0};
 for(const cap of caps){
  const all=Object.fromEntries(kinds.map(k=>[k,[]])),C=Object.fromEntries(kinds.map(k=>[k,blankCost15()]));
  const A=Object.fromEntries(Object.keys(limits).map(k=>[k,{states:0,actions:0,certified:0,maxRegret:0,maxViolation:0,maxStateWidth:0,sumRegret:0}]));
  for(let i=0;i<n;i++){
   const root=roots[i];let oracle=null,opt=null;
   for(const kind of kinds){
    const selective=kind in limits,allocation=kind.startsWith("receding"),
     P=selective?new Selective15(root,cap,limits[kind]):allocation?new AllocationProblem(root,cap):new Problem(root,cap);
    const E=new Engine(P,selective?"selective":kind,kind==="recurrent"?frozen.training.choices.recurrent.weights:null);
    const v=E.rec(P.initial(),b);
    if(kind==="optimal"){oracle=E;opt=v}
    else ok(v.v<=opt.v+1e-9,"oracle domination");
    all[kind].push({v:v.v,regret:opt.v-v.v,calls:v.calls,evictions:v.evictions,peak:v.peak,firstDifferent:Number(v.action?.id!==opt.action?.id)});
    globalAudit.policyRootBudgets++;
    cost15(C[kind],P,E);
    if(selective){
     const audit=audit15(P,oracle),a=A[kind];
     for(const k of Object.keys(a)){if(k.startsWith("max"))a[k]=Math.max(a[k],audit[k]);else a[k]+=audit[k]}
     ok(audit.states===P.planning.decisions,"reached decision audit count");
     if(kind==="unlimited")ok(Math.abs(v.v-opt.v)<1e-8&&audit.certified===audit.states,"unlimited policy optimum");
     if(standard&&i<4&&["selective16","unlimited"].includes(kind)){
      const q=forwardWorld(root,E,b),err=Math.abs(q.value-v.v);ok(err<1e-10,"world replay");
      globalAudit.worldChecks++;globalAudit.worlds+=q.worlds;globalAudit.maxWorldError=Math.max(globalAudit.maxWorldError,err);
     }
    }
   }
  }
  for(const kind of kinds){
   const a=all[kind],mean=k=>sum(a.map(x=>x[k]))/a.length;
   rows.push({regime,cap,budget:b,kind,roots:n,expectedSuccess:mean("v"),meanRegret:mean("regret"),expectedCalls:mean("calls"),expectedEvictions:mean("evictions"),peakActive:Math.max(...a.map(x=>x.peak)),firstDifferent:sum(a.map(x=>x.firstDifferent))});
  }
  for(const kind of Object.keys(limits))for(const ref of ["optimal","receding2","selective4","selective16","selective64"].filter(x=>x!==kind)){
   const d=all[kind].map((v,i)=>v.v-all[ref][i].v);
   paired.push({regime,cap,budget:b,kind,ref,...bootstrap(d,(0xCF150000+(standard?0:10000)+cap*1000+kinds.indexOf(kind)*20+kinds.indexOf(ref))>>>0)});
  }
  costs.push({regime,cap,budget:b,byPolicy:C});audits.push({regime,cap,budget:b,byPolicy:A});
 }
 return {status:"PASS",scope:"finite independent synthetic decision model; floating conditional expectation and numerical enclosures",regime,rows,paired,costs,audits,globalAudit,elapsedMs:Date.now()-begin};
}
export {Planner15,EPS15,quant15,key15,fresh15,experiment15};
if(process.argv[1]&&import.meta.url===pathToFileURL(process.argv[1]).href){
 const frozen15=JSON.parse(readFileSync(new URL("./information_gain_receipt.json",import.meta.url),"utf8"));
 const regime15=process.argv.includes("--stress")?"stress":"standard";
 console.log(JSON.stringify(experiment15(frozen15,regime15),null,2));
}
