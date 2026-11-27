// CRD-18: metered persistent planning; finite synthetic independent branches.
import {rng} from "./search.mjs";
import {ok,sum,fixture,Problem,Engine,bootstrap} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {canon16,desc16,align16} from "./persistent_symmetry.mjs";
const EPS=1e-10,quant=x=>Math.round(x*1e12)/1e12,clip=x=>Math.max(0,Math.min(1,x));
const key=(s,b)=>b+":"+s.join(","),STOP={work:true};
const charges=["lookup","nodeInit","localMiss","likelihood","option","allocation","boundCall","sortItem","boundCombination","actionEnum","outcomeGen","leafVisit","rangeEval","rangeOutcome","backup","traverseNode","traverseEdge","copyNode","copyEdge"];
const events=["decisions","certified","fallback","aborted","expansions","warmCalls","warmOutcomes","reusedOutcomes","deadlineTightens","strictTightens","copyAborts","gapSum","actualGapSum"];
const blank=()=>Object.fromEntries([...charges,...events].map(k=>[k,0]));
class Meter{
 constructor(limit){this.limit=limit;this.used=0;this.c=blank()}
 take(k,n=1){ok(Number.isInteger(n)&&n>=0&&k in this.c,"charge");if(this.used+n>this.limit)throw STOP;this.used+=n;this.c[k]+=n}
 event(k,n=1){this.c[k]+=n}
}
const top=(p,k)=>sum(p.slice().sort((a,b)=>b-a).slice(0,k));
const pred=(j,x)=>j===0?x%2:j===1?Number(x<3):Number(x%3===0);
function setup(P){let states=0,edges=0;for(const l of P.local){for(let id=0;id<l.states.length;id++)for(const a of l.actions(id,12))edges+=l.outcomes(id,a).length;states+=l.states.length}return {states,edges}}
function affordable(P,s,b){return s.flatMap((id,i)=>{if(id<0||b<=0)return [];const l=P.local[i],v=l.at(id),m=l.L-v.stage;return m+1<=b&&v.mass>0?[{i,id,m,mass:v.mass,p:v.p.slice(0,3)}]:[]})}
function prophet(P,s,b){return 1-affordable(P,s,b).reduce((a,x)=>a*(1-x.mass),1)}
function deadlineList(d,b,meter=null){
 if(b<=0)return 0;
 const screens=d.filter(x=>x.m>0),ready=d.filter(x=>x.m===0);
 if(meter){meter.take("boundCall");meter.take("sortItem",screens.length)}
 screens.sort((a,c)=>c.m-a.m||a.i-c.i);
 let dp=Array(b+1).fill(Infinity);dp[0]=1;
 for(const x of screens){const next=dp.slice();for(let t=0;t<b;t++)if(Number.isFinite(dp[t])&&t+1<=b-x.m){if(meter)meter.take("boundCombination");next[t+1]=Math.min(next[t+1],dp[t]*(1-x.mass))}dp=next}
 for(const x of ready){const next=Array(b+1).fill(Infinity),p=x.p.slice().sort((a,c)=>c-a);
  for(let t=0;t<=b;t++)if(Number.isFinite(dp[t])){let mass=0;for(let k=0;k<=3&&t+k<=b;k++){if(meter)meter.take("boundCombination");if(k)mass+=p[k-1];next[t+k]=Math.min(next[t+k],dp[t]*Math.max(0,1-mass))}}
  dp=next;
 }return clip(1-Math.min(...dp));
}
function deadline(P,s,b,meter=null){return deadlineList(affordable(P,s,b),b,meter)}
function capOne(P,s,b){
 const d=affordable(P,s,b),active=P.active(s);
 ok(active.length<=1,"cap one");
 if(!active.length)return deadlineList(d,b);
 const i=active[0],x=d.find(v=>v.i===i),other=d.filter(v=>v.i!==i);
 let v=deadlineList(other,b);
 if(!x)return v;
 if(x.m>0)return Math.max(v,x.mass+(1-x.mass)*deadlineList(other,b-1));
 for(let k=1;k<=3&&k<=b;k++){const p=top(x.p,k);v=Math.max(v,p+(1-p)*deadlineList(other,b-k))}
 return clip(v);
}
// Independent cap-one relaxed recursion: each screen either succeeds or removes
// that branch; opening another branch abandons the prior active branch.
function capReference(P,s,b){
 const d=affordable(P,s,b),active=P.active(s)[0]??-1,memo=new Map();let states=0;
 function rec(left,alive,mask,act){
  if(left<=0)return 0;const k=[left,alive,mask,act].join(":");if(memo.has(k))return memo.get(k);states++;let v=0;
  for(let j=0;j<d.length;j++){
   if(!(alive&(1<<j)))continue;
   const x=d[j],old=d.findIndex(y=>y.i===act),abandon=old>=0&&old!==j?alive&~(1<<old):alive;
   if(x.m>0){
    if(x.m+1>left)continue;
    v=Math.max(v,x.mass+(1-x.mass)*rec(left-1,abandon&~(1<<j),mask,-1));
   }else{
    ok(x.i===act,"only active branch can be ready");
    let z=1;for(let q=0;q<3;q++)if(!(mask&(1<<q)))z-=x.p[q];if(z<=1e-15)continue;
    for(let q=0;q<3;q++)if((mask&(1<<q))&&x.p[q]>0){const p=x.p[q]/z;v=Math.max(v,p+(1-p)*rec(left-1,alive,mask&~(1<<q),act))}
   }
  }
  memo.set(k,v);return v;
 }
 return {v:rec(b,(1<<d.length)-1,7,active),states};
}
function auditCap(P,s,b,v){
 const u=capOne(P,s,b),r=capReference(P,s,b),d=deadline(P,s,b),err=Math.abs(u-r.v);
 ok(err<1e-10&&v<=u+1e-10&&u<=d+1e-10,"cap-one bound");
 return {u,d,err,states:r.states,strict:Number(d-u>EPS)};
}
function hand(){
 // One ready active branch with two competing unopened screens. Also audit
 // exact all-unopened and active-unready continuations via reference recursion.
 const P=new Problem({seed:0,branches:[{prior:[1,1,1,1,1,1],sensors:[60]},{prior:[1,1,1,1,1,1],sensors:[60,60]},{prior:[1,1,1,1,1,1],sensors:[60,60]}]},1);
 setup(P);let s=P.initial();auditCap(P,s,3,0);
 s[0]=P.local[0].intern(1,[1,1,1,1,1,1]);const a=auditCap(P,s,3,0);ok(Math.abs(a.u-.5)<1e-10&&a.strict===1,"ready active deadline competition");
 s=P.initial();s[1]=P.local[1].intern(1,[1,1,1,1,1,1]);auditCap(P,s,3,0);
 return 3;
}
class Planner{
 constructor(P,meter,mode,retained){
  this.P=P;this.M=meter;this.mode=mode;this.cache=retained??new Map();this.lv=new Map();this.av=new Map();this.dv=new Map();
  this.peakNodes=this.cache.size;this.peakEdges=0;this.edges=0;
  // The retained copy's edge count is computed during charged copying.
  for(const n of this.cache.values())this.edges+=n.actions?.reduce((s,a)=>s+a.os.length,0)??n.prepared?.reduce((s,a)=>s+a.os.length,0)??0;
  this.peakEdges=this.edges;
 }
 val(i,id,b){
  const k=desc16(this.P,i,id)+":"+b;this.M.take("lookup");if(this.lv.has(k))return this.lv.get(k);
  this.M.take("localMiss");let v=0;
  if(id>=0&&b>0){
   const l=this.P.local[i],s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
   if(k>=3)v=s.mass;else if(k>0&&m===0)v=top(s.p.slice(0,3),k);
   else if(k>0)for(let u=0;u<2**m;u++){
    this.M.take("likelihood",3*m);
    const w=s.p.slice(0,3);
    for(let t=0;t<m;t++){const j=s.stage+t,a=l.spec.sensors[j]/100,bit=(u>>t)&1;for(let x=0;x<3;x++)w[x]*=pred(j,x)===bit?a:1-a}
    v+=top(w,k);
   }
  }
  this.lv.set(k,v);return v;
 }
 alloc(s,b){
  const c=canon16(this.P,s,b);this.M.take("lookup");if(this.av.has(c.key))return this.av.get(c.key);
  let dp=Array(b+1).fill(1);
  for(const {i} of c.entries){
   const id=s[i],opts=[{t:0,v:0}];this.M.take("option");
   if(id>=0){
    const l=this.P.local[i],m=l.L-l.at(id).stage;let last=0;
    for(let j=1;j<=3&&m+j<=b;j++){this.M.take("option");const v=this.val(i,id,m+j);if(v>last+1e-15){opts.push({t:m+j,v});last=v}}
   }
   const next=[];
   for(let r=0;r<=b;r++){let best=1;for(const o of opts){if(o.t>r)break;this.M.take("allocation");best=Math.min(best,(1-o.v)*dp[r-o.t])}next.push(best)}
   dp=next;
  }
  const v=1-dp[b];this.av.set(c.key,v);return v;
 }
 dl(s,b){
  const k=canon16(this.P,s,b).key;this.M.take("lookup");if(this.dv.has(k))return this.dv.get(k);
  const v=deadline(this.P,s,b,this.M);this.dv.set(k,v);return v;
 }
 tighten(n,U){const old=n.U;n.U=Math.min(old,U);ok(n.U>=n.L-EPS,"tight bound below lower");n.U=Math.max(n.L,n.U);if(old-n.U>EPS)this.M.event("strictTightens")}
 tightenDL(n){const u=this.dl(n.s,n.b);this.tighten(n,u);n.tier=Math.max(n.tier,1);this.M.event("deadlineTightens")}
 raw(n,warm){
  const out=[];
  for(const a of this.P.legal(n.s,n.b)){
   this.M.take("actionEnum");const os=[];
   for(const o of this.P.outcomes(n.s,a)){this.M.take("outcomeGen");if(warm)this.M.event("warmOutcomes");os.push(o.hit?{p:o.p,hit:true,s:null}:{p:o.p,hit:false,s:o.s.slice()})}
   out.push({a,os});
  }
  return out;
 }
 warm(n,reuse){
  this.M.event("warmCalls");
  const raw=this.raw(n,true);let v=0;
  for(const a of raw){this.M.take("rangeEval");let q=0;for(const o of a.os){this.M.take("rangeOutcome");q+=o.p*(o.hit?1:this.dl(o.s,n.b-1))}v=Math.max(v,q)}
  this.tighten(n,v);n.tier=2;
  if(reuse){n.prepared=raw;this.edges+=raw.reduce((s,a)=>s+a.os.length,0);this.peakEdges=Math.max(this.peakEdges,this.edges)}
 }
 node(s,b){
  const k=key(s,b);this.M.take("lookup");if(this.cache.has(k))return this.cache.get(k);
  this.M.take("nodeInit");const aff=affordable(this.P,s,b);let L=0,U=0;
  if(aff.length===1)L=U=this.val(aff[0].i,aff[0].id,b);
  else if(aff.length>1){L=this.alloc(s,b);U=aff.every(x=>x.m===0)?L:1-aff.reduce((v,x)=>v*(1-x.mass),1)}
  ok(L<=U+EPS,"initial bound");const n={s:s.slice(),b,key:k,L:clip(L),U:clip(Math.max(L,U)),tier:0,actions:null,prepared:null};
  // Insert only complete initial interval; subsequent tightening stages atomic.
  this.cache.set(k,n);this.peakNodes=Math.max(this.peakNodes,this.cache.size);
  if(n.U-n.L>EPS&&this.mode!=="prophet"&&this.mode!=="lazy"){
   this.tightenDL(n);
   if(n.U-n.L>EPS&&(this.mode==="backed"||this.mode==="reuse"))this.warm(n,this.mode==="reuse");
  }
  return n;
 }
 expand(n){
  ok(n.actions===null,"expand once");
  const was=n.prepared,raw=was??this.raw(n,false),out=[];
  for(const a of raw){
   if(was)this.M.take("traverseNode");
   const os=[];
   for(const o of a.os){if(was){this.M.take("traverseEdge");this.M.event("reusedOutcomes")}
    os.push(o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:this.node(o.s,n.b-1)});
   }
   out.push({a:a.a,os});
  }
  n.actions=out;n.prepared=null;
  if(!was)this.edges+=out.reduce((s,a)=>s+a.os.length,0);
  this.peakEdges=Math.max(this.peakEdges,this.edges);this.M.event("expansions");
 }
 range(a){
  this.M.take("rangeEval");let L=0,U=0;
  for(const o of a.os){this.M.take("rangeOutcome");L+=o.p*(o.hit?1:o.n.L);U+=o.p*(o.hit?1:o.n.U)}
  return {a:a.a,os:a.os,L:clip(L),U:clip(U)};
 }
 choices(n){return n.actions.map(a=>this.range(a)).sort((a,b)=>quant(b.L)-quant(a.L)||b.a.id-a.a.id)}
 refresh(root){
  const seen=new Set();
  const rec=n=>{
   this.M.take("traverseNode");if(seen.has(n.key))return;seen.add(n.key);
   if(!n.actions)return;
   for(const a of n.actions)for(const o of a.os){this.M.take("traverseEdge");if(!o.hit)rec(o.n)}
   this.M.take("backup");const rs=this.choices(n),L=Math.max(n.L,0,...rs.map(a=>a.L)),U=Math.min(n.U,Math.max(0,...rs.map(a=>a.U)));
   ok(L<=U+EPS,"backup interval");n.L=clip(L);n.U=clip(Math.max(L,U));
  };rec(root);
 }
 leaf(n,root=false){
  this.M.take("leafVisit");if(!root&&n.U-n.L<=EPS/10)return null;if(n.actions===null)return n;
  const as=this.choices(n),best=as[0]?.L??0;
  const ranked=as.filter(a=>a.U>best+EPS/10).sort((a,b)=>quant(b.U)-quant(a.U)||b.a.id-a.a.id);
  for(const a of ranked){
   const children=a.os.filter(o=>!o.hit&&o.n.U-o.n.L>EPS/10).sort((a,b)=>b.p*(b.n.U-b.n.L)-a.p*(a.n.U-a.n.L)||a.n.key.localeCompare(b.n.key));
   for(const o of children){const x=this.leaf(o.n);if(x)return x}
  }return null;
 }
 solve(s,b,fallback){
  this.M.event("decisions");let snap=null;
  try{
   const root=this.node(s,b);if(!root.actions)this.expand(root);
   for(;;){
    this.refresh(root);const as=this.choices(root);ok(as.length,"root actions");
    const a=as[0],gap=Math.max(0,...as.map(x=>x.U-a.L));
    snap={a:a.a,os:a.os,L:root.L,U:root.U,gap,ranges:as.map(x=>({id:x.a.id,L:x.L,U:x.U})),certified:gap<=EPS};
    if(snap.certified)break;
    const n=this.leaf(root,true);if(!n)break;
    if(this.mode==="lazy"&&n.tier===0)this.tightenDL(n);
    else if(this.mode==="lazy"&&n.tier===1)this.warm(n,true);
    else this.expand(n);
   }
  }catch(e){if(e!==STOP)throw e;this.M.event("aborted")}
  if(!snap){this.M.event("fallback");return {a:fallback,os:null,L:0,U:1,gap:1,ranges:null,certified:false}}
  if(snap.certified)this.M.event("certified");
  return snap;
 }
}
function copyGraph(root,meter){
 const cache=new Map();
 function rec(n){
  if(cache.has(n.key))return cache.get(n.key);
  meter.take("copyNode");const c={s:n.s.slice(),b:n.b,key:n.key,L:n.L,U:n.U,tier:n.tier,actions:null,prepared:null};cache.set(c.key,c);
  if(n.actions)c.actions=n.actions.map(a=>({a:{...a.a},os:a.os.map(o=>{meter.take("copyEdge");return o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:rec(o.n)}})}));
  else if(n.prepared)c.prepared=n.prepared.map(a=>({a:{...a.a},os:a.os.map(o=>{meter.take("copyEdge");return {p:o.p,hit:o.hit,s:o.s?.slice()??null}})}));
  return c;
 }
 try{rec(root);return cache}catch(e){if(e!==STOP)throw e;meter.event("copyAborts");return null}
}
function addWork(a,b,p=1){for(const k of Object.keys(a))a[k]+=p*b[k]}
function policy(root,cap,budget,total,mode,oracle){
 const P=new Problem(root,cap),pre=setup(P),audit={visits:0,rangeChecks:0,certified:0,maxViolation:0,maxGapViolation:0,peakNodes:0,peakEdges:0,maxUsed:0};
 function rec(s,b,left,retained){
  const as=P.legal(s,b);if(!as.length)return {v:0,calls:0,work:blank(),maxUsed:0,used:0};
  const probes=as.filter(a=>a.t>0),fallback=(probes.length?probes:as).slice().sort((a,b)=>b.id-a.id)[0];
  const meter=new Meter(Math.min(left,Math.ceil(2*left/b))),planner=new Planner(P,meter,mode,retained),r=planner.solve(s,b,fallback);
  const z=oracle.rec(align16(P,s,oracle.P),b),qm=new Map(z.qs.map(x=>[x.a.id,x.q]));
  let violation=Math.max(0,r.L-z.v,z.v-r.U);
  if(r.ranges){ok(r.ranges.length===qm.size,"range roster");for(const x of r.ranges){const q=qm.get(x.id);ok(Number.isFinite(q),"action alignment");violation=Math.max(violation,x.L-q,q-x.U);audit.rangeChecks++}}
  const regret=z.v-qm.get(r.a.id);ok(Number.isFinite(regret)&&violation<1e-9&&regret<=r.gap+1e-9,"oracle regret interval");
  if(r.certified)ok(regret<=EPS+1e-9,"certified regret");
  audit.visits++;audit.certified+=Number(r.certified);audit.maxViolation=Math.max(audit.maxViolation,violation);audit.maxGapViolation=Math.max(audit.maxGapViolation,regret-r.gap);audit.peakNodes=Math.max(audit.peakNodes,planner.peakNodes);audit.peakEdges=Math.max(audit.peakEdges,planner.peakEdges);
  const work={...meter.c};work.gapSum=r.gap;work.actualGapSum=regret;
  let value=0,calls=1,used=meter.used,maxUsed=meter.used;
  const os=r.os??P.outcomes(s,r.a).map(o=>o.hit?{p:o.p,hit:true,n:null}:{p:o.p,hit:false,n:{s:o.s,b:b-1}});
  for(const o of os){
   if(o.hit){value+=o.p;continue}
   const cm=new Meter(left-meter.used);let keep=null;
   if(r.os&&o.n.b>0&&P.legal(o.n.s,o.n.b).length)keep=copyGraph(o.n,cm);
   addWork(work,cm.c,o.p);
   const q=rec(o.n.s,o.n.b,left-meter.used-cm.used,keep);
   value+=o.p*q.v;calls+=o.p*q.calls;used+=o.p*(cm.used+q.used);maxUsed=Math.max(maxUsed,meter.used+cm.used+q.maxUsed);
   addWork(work,q.work,o.p);
  }
  ok(maxUsed<=left&&calls<=b+EPS,"trajectory work/call ceiling");
  ok(Math.abs(used-sum(charges.map(k=>work[k])))<1e-7,"weighted ledger identity");
  return {v:value,calls,work,maxUsed,used};
 }
 const r=rec(P.initial(),budget,total,null),regret=oracle.rec(oracle.P.initial(),budget).v-r.v;
 ok(Math.abs(regret-r.work.actualGapSum)<1e-9&&regret<=r.work.gapSum+1e-9,"trajectory regret");
 audit.maxUsed=r.maxUsed;return {...r,regret,audit,pre};
}
function cohort(name){
 if(name==="standard")return {n:48,seed:2420001,cap:2,b:6,stages:3};
 if(name==="deep")return {n:24,seed:2430001,cap:2,b:8,stages:4};
 return {n:32,seed:2440001,cap:1,b:5,stages:4};
}
function rootFor(name,seed,stages){
 if(name!=="tight")return fixture(seed,3,stages);
 const r=rng(seed),branches=[];
 for(let i=0;i<3;i++){const prior=Array.from({length:6},()=>1+Math.floor(r()*12)),L=3+Math.floor(r()*2),sensors=Array.from({length:L},()=>[60,80,100][Math.floor(r()*3)]);branches.push({prior,sensors})}
 return {seed,branches};
}
function experiment18(name){
 const start=Date.now(),{n,seed,cap,b,stages}=cohort(name),modes=["prophet","deadline","backed","reuse","lazy"],limits=[2000,8000],keys=limits.flatMap(t=>modes.map(m=>m+t)),all=Object.fromEntries(keys.map(k=>[k,[]])),ref={optimal:[],receding2:[]};
 const check={hand:hand(),rootChecks:0,stateChecks:0,refStates:0,strict:0,maxError:0,sumTightening:0};
 function checkOne(P,s,b,v,root){const a=auditCap(P,s,b,v);check[root?"rootChecks":"stateChecks"]++;check.refStates+=a.states;check.strict+=a.strict;check.maxError=Math.max(check.maxError,a.err);check.sumTightening+=a.d-a.u}
 for(let i=0;i<n;i++){
  const root=rootFor(name,seed+i,stages),P=new Problem(root,cap);setup(P);const oracle=new Engine(P,"optimal",null),opt=oracle.rec(P.initial(),b);
  ref.optimal.push(opt.v);const R=new AllocationProblem(root,cap);setup(R);ref.receding2.push(new Engine(R,"receding2",null).rec(R.initial(),b).v);
  if(cap===1){
   for(let t=0;t<=b;t++)checkOne(P,P.initial(),t,oracle.rec(P.initial(),t).v,true);
   if(i<4)for(const x of [...oracle.memo.values()].filter(x=>x.s&&x.action).slice(0,128))checkOne(P,x.s,x.b,x.v,false);
  }
  for(const total of limits)for(const mode of modes)all[mode+total].push(policy(root,cap,b,total,mode,oracle));
 }
 const mean=a=>sum(a)/a.length,rows=[],paired=[];
 for(const k of keys){
  const a=all[k],work=Object.fromEntries(Object.keys(blank()).map(k=>[k,mean(a.map(x=>x.work[k]))])),max=k=>Math.max(...a.map(x=>x.audit[k]));
  rows.push({kind:k,roots:n,expectedSuccess:mean(a.map(x=>x.v)),meanRegret:mean(a.map(x=>x.regret)),expectedCalls:mean(a.map(x=>x.calls)),expectedWork:mean(a.map(x=>x.used)),maxUsed:Math.max(...a.map(x=>x.maxUsed)),certificateRate:work.certified/work.decisions,fallbackRate:work.fallback/work.decisions,work,setupStates:sum(a.map(x=>x.pre.states)),setupEdges:sum(a.map(x=>x.pre.edges)),audit:{visits:sum(a.map(x=>x.audit.visits)),rangeChecks:sum(a.map(x=>x.audit.rangeChecks)),certified:sum(a.map(x=>x.audit.certified)),maxViolation:max("maxViolation"),maxGapViolation:max("maxGapViolation"),peakNodes:max("peakNodes"),peakEdges:max("peakEdges")}});
 }
 for(const t of limits)for(const k of ["lazy","reuse"])for(const r of [...modes.filter(m=>m!==k).map(m=>m+t),"receding2","optimal"]){
  const other=ref[r]??all[r].map(x=>x.v),d=all[k+t].map((x,i)=>x.v-other[i]);
  paired.push({kind:k+t,ref:r,...bootstrap(d,(0xC0180000+seed+t*100+keys.indexOf(k+t)*20+keys.indexOf(r))>>>0)});
 }
 return {status:"PASS",scope:"metered synthetic policy expectation; declared proxy, not measured FLOPs/CPU/RSS",name,roots:n,cap,budget:b,check,baselines:{optimal:mean(ref.optimal),receding2:mean(ref.receding2)},rows,paired,elapsedMs:Date.now()-start};
}
const cohortName=process.argv.includes("--deep")?"deep":process.argv.includes("--tight")?"tight":"standard";
console.log(JSON.stringify(experiment18(cohortName),null,2));
