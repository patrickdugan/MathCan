// CRD-12: analytic local value, distilled local surrogate, interval fallback.
import {readFileSync} from "node:fs";
import {rng} from "./search.mjs";
import {ok,sum,zeros,fixture,Problem,Engine,predict,bootstrap} from "./information_gain.mjs";
const F12=15,H12=16;
const dot12=(a,b)=>sum(a.map((v,i)=>v*b[i]));
const pred12=(j,x)=>j===0?x%2:j===1?Number(x<3):Number(x%3===0);
const top12=(p,k)=>sum(p.slice().sort((a,b)=>b-a).slice(0,Math.max(0,k)));
function exact12(l,id,b,stat){
 if(id<0||b<=0)return 0;
 const s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
 if(k<=0)return 0;
 if(k>=3)return s.mass;
 if(m===0)return top12(s.p.slice(0,3),k);
 if(stat)stat.nontrivial++;
 let v=0;
 for(let u=0;u<(1<<m);u++){
  const weights=s.p.slice(0,3);
  for(let t=0;t<m;t++){
   const j=s.stage+t,acc=l.spec.sensors[j]/100,bit=(u>>t)&1;
   for(let x=0;x<3;x++)weights[x]*=pred12(j,x)===bit?acc:1-acc;
  }
  v+=top12(weights,k);
  if(stat){stat.patterns++;stat.likelihoodProducts+=3*m}
 }return v;
}
function bounds12(l,id,b){
 if(id<0||b<=0)return [0,0];
 const s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
 if(k<=0)return [0,0];
 if(k>=3)return [s.mass,s.mass];
 const low=top12(s.p.slice(0,3),k);
 return m===0?[low,low]:[low,s.mass];
}
function qProbe12(l,id,a,b){
 ok(a>=1&&a<=3&&b>0,"probe");
 const p=l.at(id).p.slice(0,3),x=p.splice(a-1,1)[0];
 return x+top12(p,Math.min(2,b-1));
}
function x12(l,id,b){
 const s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m);
 const x=[...s.p,...Array.from({length:3},(_,j)=>j>=s.stage&&j<l.L?l.spec.sensors[j]/100:0),k/3,m/3,s.mass,s.max,s.top2,l.nextBest(id)];
 ok(x.length===F12&&x.every(Number.isFinite),"local features");return x;
}
function sigmoid12(z){return 1/(1+Math.exp(-z))}
function init12(){
 const r=rng(502);return Array.from({length:273},()=>.2*r()-.1);
}
function forward12(w,x){
 const h=Array.from({length:H12},(_,i)=>Math.tanh(w[240+i]+dot12(w.slice(F12*i,F12*i+F12),x)));
 return {h,p:sigmoid12(w[272]+dot12(w.slice(256,272),h))};
}
function grad12(w,x,y,g){
 const {p,h}=forward12(w,x),d=(p-y)*p*(1-p);g[272]+=d;
 for(let i=0;i<H12;i++){g[256+i]+=d*h[i];const z=d*w[256+i]*(1-h[i]**2);g[240+i]+=z;for(let j=0;j<F12;j++)g[i*F12+j]+=z*x[j]}
}
function gradient12(){
 const w=init12(),x=Array.from({length:F12},(_,i)=>(i%7)/7),y=.4,g=zeros(w.length);grad12(w,x,y,g);let err=0;
 for(let i=0;i<w.length;i++){const z=w[i],e=1e-5;w[i]=z+e;const a=.5*(forward12(w,x).p-y)**2;w[i]=z-e;const b=.5*(forward12(w,x).p-y)**2;w[i]=z;err=Math.max(err,Math.abs(g[i]-(a-b)/(2*e)))}
 ok(err<1e-7,"gradient");return err;
}
function localRows12(start,n){
 const rows=[],stat={roots:n,localBeliefStates:0,valueChecks:0,actionChecks:0,maxFormulaError:0,nontrivial:0,patterns:0,likelihoodProducts:0,coverage:{}};
 for(let i=0;i<n;i++){
  const l=new Problem(fixture(start+i,1,3),1).local[0];
  // Intern all reachable positive-feasible states, irrespective of budget.
  for(let id=0;id<l.states.length;id++){
   for(const a of l.actions(id,8))l.outcomes(id,a);
  }
  stat.localBeliefStates+=l.states.length;
  for(let id=0;id<l.states.length;id++)for(let b=1;b<=6;b++){
   const s=l.at(id),m=l.L-s.stage,k=Math.min(3,b-m),y=l.value(id,b),formula=exact12(l,id,b,stat),err=Math.abs(y-formula);
   ok(err<1e-12,"local V formula mismatch");stat.valueChecks++;stat.maxFormulaError=Math.max(stat.maxFormulaError,err);
   for(const a of l.actions(id,b)){
    const q=l.q(id,a,b),f=a===0?formula:qProbe12(l,id,a,b),e=Math.abs(q-f);ok(e<1e-12,"local Q formula mismatch");stat.actionChecks++;stat.maxFormulaError=Math.max(stat.maxFormulaError,e);
   }
   if(m>0&&k>0&&k<3){
    const [lo,hi]=bounds12(l,id,b);ok(lo<=y+1e-12&&y<=hi+1e-12,"local interval");
    rows.push({x:x12(l,id,b),y,lo,hi,m,k});const key=m+":"+k;stat.coverage[key]=(stat.coverage[key]||0)+1;
   }
  }
 }
 return {rows,stat};
}
const clip12=(v,l,u)=>Math.max(l,Math.min(u,v));
function metrics12(rows,w){
 const errors=rows.map(r=>Math.abs(clip12(forward12(w,r.x).p,r.lo,r.hi)-r.y)),sorted=errors.slice().sort((a,b)=>a-b),n=errors.length;
 return {rows:n,mae:sum(errors)/n,mse:sum(errors.map(x=>x*x))/n,max:sorted[n-1],p50:sorted[Math.floor((n-1)*.5)],p90:sorted[Math.floor((n-1)*.9)],p99:sorted[Math.floor((n-1)*.99)]};
}
function train12(train,val){
 const w=init12(),r=rng(711),history=[];let best=null;
 for(let epoch=1;epoch<=16;epoch++){
  for(let batch=0;batch<64;batch++){const g=zeros(w.length);for(let j=0;j<32;j++){const row=train[Math.floor(r()*train.length)];grad12(w,row.x,row.y,g)}for(let j=0;j<w.length;j++)w[j]-=.08*g[j]/32}
  if([1,4,8,16].includes(epoch)){const m=metrics12(val,w),c={epoch,...m,weights:w.slice()};history.push({epoch,...m});if(!best||m.mae<best.mae)best=c}
 }return {best,history};
}
function affineInterval12(weights,intervals,bias){
 let lo=bias,hi=bias;
 for(let i=0;i<weights.length;i++){const w=weights[i],[a,b]=intervals[i];lo+=w>=0?w*a:w*b;hi+=w>=0?w*b:w*a}
 return [lo-1e-12,hi+1e-12];
}
function intervalHead12(w,x){
 // CRD-11A frozen 5-state three-step recurrent global action head.
 const F=20,wx=Array.from({length:5},(_,i)=>affineInterval12(w.slice(F*i,F*i+F),x,w[125+i]));let h=Array.from({length:5},()=>[0,0]);
 for(let t=0;t<3;t++)h=Array.from({length:5},(_,i)=>{
  const u=affineInterval12(w.slice(100+5*i,105+5*i),h,0);return [Math.tanh(wx[i][0]+u[0])-1e-12,Math.tanh(wx[i][1]+u[1])+1e-12];
 });
 return affineInterval12(w.slice(130,135),h,w[135]);
}
const quant12=x=>Math.round(x*1e12)/1e12;
class Head12 extends Problem {
 constructor(root,cap,mode,localW){
  super(root,cap);this.mode=mode;this.localW=localW;
  this.exactCache=this.local.map(()=>new Map());this.surCache=this.local.map(()=>new Map());
  this.extra={formulaCalls:0,formulaHits:0,nontrivial:0,patterns:0,likelihoodProducts:0,surrogateCalls:0,surrogateHits:0,headCalls:0,intervalHeadCalls:0,certified:0,fallback:0,decisions:0,exactScoreChecks:0,intervalChecks:0,maxLocalError:0};
 }
 val(i,id,b,mode){
  const l=this.local[i];
  if(mode==="dp")return l.value(id,b);
  if(mode==="interval")return bounds12(l,id,b);
  const [lo,hi]=bounds12(l,id,b);
  if(mode==="surrogate"&&lo===hi)return lo;
  const cache=(mode==="surrogate"?this.surCache:this.exactCache)[i],key=id+":"+b;
  if(cache.has(key)){this.extra[mode==="surrogate"?"surrogateHits":"formulaHits"]++;return cache.get(key)}
  let v;
  if(mode==="surrogate"){
   this.extra.surrogateCalls++;v=clip12(forward12(this.localW,x12(l,id,b)).p,lo,hi);
  }else{this.extra.formulaCalls++;v=exact12(l,id,b,this.extra)}
  cache.set(key,v);return v;
 }
 q(i,id,a,b,mode){
  if(mode==="dp")return this.local[i].q(id,a,b);
  if(a===0)return this.val(i,id,b,mode);
  const v=qProbe12(this.local[i],id,a,b);return mode==="interval"?[v,v]:v;
 }
 features12(s,a,b,mode){
  this.featureEvals++;const i=a.i,l=this.local[i],v=l.at(s[i]),reveal=a.t===0,remain=l.L-v.stage,ev=a.evict;
  const other=s.map((id,j)=>({id,j})).filter(o=>o.j!==i&&o.id>=0);
  const otherVs=other.map(({id,j})=>this.val(j,id,b,mode)),interval=mode==="interval";
  const bestOther=interval?[Math.max(0,...otherVs.map(x=>x[0])),Math.max(0,...otherVs.map(x=>x[1]))]:Math.max(0,...otherVs);
  const otherProbe=Math.max(0,...other.map(({id,j})=>this.local[j].at(id).stage===this.local[j].L?this.local[j].at(id).max:0));
  const next=reveal?l.nextBest(s[i]):0;
  const x=[Number(reveal),b/8,remain/3,reveal?0:v.p[a.t-1],v.max,v.mass,v.top2,next,reveal?next-v.max:0,this.q(i,s[i],a.t,b,mode),this.val(i,s[i],b,mode),otherProbe,bestOther,sum(other.map(({id,j})=>this.local[j].at(id).mass))/3,this.active(s).length/3,this.cap/3,Number(ev>=0),this.evictMass(s,a),ev<0?(interval?[0,0]:0):this.val(ev,s[ev],b,mode),this.sensor(s,a)];
  return interval?x.map(z=>Array.isArray(z)?z:[z,z]):x;
 }
 choose(s,b,kind,w){
  if(kind!=="recurrent")return super.choose(s,b,kind,w);
  const as=this.legal(s,b);if(!as.length)return null;
  this.extra.decisions++;
  const rank=mode=>{
   const rows=as.map(a=>{this.extra.headCalls++;return {a,v:quant12(predict("recurrent",w,this.features12(s,a,b,mode)))}});
   this.scoreEvals+=rows.length;return rows.sort((a,b)=>b.v-a.v||b.a.id-a.a.id);
  };
  if(this.mode!=="certified")return rank(this.mode)[0].a;
  // The surrogate proposes a choice. Only analytic intervals certify it.
  const ranked=rank("surrogate"),top=ranked[0].a;
  const ranges=as.map(a=>{this.extra.intervalHeadCalls++;return {a,r:intervalHead12(w,this.features12(s,a,b,"interval"))}});
  const t=ranges.find(x=>x.a.id===top.id);
  if(ranges.every(x=>x===t||t.r[0]>x.r[1]+2e-12)){
   this.extra.certified++;return top;
  }
  this.extra.fallback++;return rank("formula")[0].a;
 }
}
function auditGlobal12(P,E,reference,w){
 let states=0,max=0;
 for(const v of E.memo.values()){
  if(!v.action)continue;
  const ref=reference.rec(v.s,v.b);
  ok(ref.action.id===v.action.id&&Math.abs(ref.v-v.v)<1e-10,"certified/exact policy mismatch");
  states++;max=Math.max(max,Math.abs(ref.v-v.v));
  // Score intervals checked against exact formula for every action on these states.
  for(const a of P.legal(v.s,v.b)){
   const bounds=intervalHead12(w,P.features12(v.s,a,v.b,"interval")),value=predict("recurrent",w,P.features12(v.s,a,v.b,"formula"));
   ok(value>=bounds[0]-1e-10&&value<=bounds[1]+1e-10,"global score interval");
  }
 }
 return {states,max};
}
function global12(localW,globalW){
 const roots=Array.from({length:192},(_,i)=>fixture(1870001+i,3,3)),modes=["optimal","sensor","local","rollout","dp","formula","surrogate","certified"],budgets=[4,6];
 const all=Object.fromEntries(budgets.map(b=>[b,Object.fromEntries(modes.map(m=>[m,[]]))])),costs={},audit={formulaStates:0,certifiedStates:0,maxError:0,policyRootBudgets:0};
 for(const m of modes)costs[m]={states:0,transitions:0,scores:0,features:0,localStates:0,localTransitions:0,localQueries:0,formulaCalls:0,formulaHits:0,nontrivial:0,patterns:0,likelihoodProducts:0,surrogateCalls:0,surrogateHits:0,headCalls:0,intervalHeadCalls:0,certified:0,fallback:0,decisions:0};
 for(const root of roots){
  const policies={},results={};
  for(const mode of modes){
   const isHead=["dp","formula","surrogate","certified"].includes(mode),P=isHead?new Head12(root,2,mode,localW):new Problem(root,2),E=new Engine(P,isHead?"recurrent":mode,isHead?globalW:null);policies[mode]={P,E};results[mode]=[];
   for(const b of budgets){
    const v=E.rec(P.initial(),b);results[mode].push(v);const opt=results.optimal[budgets.indexOf(b)].v;
    ok(v.v<=opt+1e-10,"optimal dominates");
    all[b][mode].push({v:v.v,regret:opt-v.v,calls:v.calls,evictions:v.evictions});audit.policyRootBudgets++;
   }
   const c=costs[mode];c.states+=E.stats.states;c.transitions+=E.stats.transitions;c.scores+=P.scoreEvals;c.features+=P.featureEvals;
   for(const l of P.local){c.localStates+=l.stats.states;c.localTransitions+=l.stats.transitions;c.localQueries+=l.stats.queries}
   if(isHead)for(const k of Object.keys(P.extra))if(k in c)c[k]+=P.extra[k];
   if(["formula","surrogate","certified"].includes(mode))ok(P.local.every(l=>l.stats.states===0&&l.stats.transitions===0&&l.stats.queries===0),"local DP gate");
  }
  // Audit after work counters frozen, so the reference queries do not count as deployment.
  const f=auditGlobal12(policies.formula.P,policies.formula.E,policies.dp.E,globalW),c=auditGlobal12(policies.certified.P,policies.certified.E,policies.formula.E,globalW);
  audit.formulaStates+=f.states;audit.certifiedStates+=c.states;audit.maxError=Math.max(audit.maxError,f.max,c.max);
  for(let j=0;j<budgets.length;j++)ok(Math.abs(results.dp[j].v-results.formula[j].v)<1e-10&&Math.abs(results.formula[j].v-results.certified[j].v)<1e-10,"root policy equality");
 }
 const rows=[],paired=[];
 for(const b of budgets){
  for(const m of modes){const a=all[b][m],mean=k=>sum(a.map(v=>v[k]))/a.length;rows.push({budget:b,mode:m,roots:a.length,expectedSuccess:mean("v"),meanRegret:mean("regret"),expectedCalls:mean("calls"),expectedEvictions:mean("evictions")})}
  for(const ref of ["dp","formula","certified","sensor","local","rollout","optimal"]){
   const a=all[b].surrogate,c=all[b][ref];paired.push({budget:b,mode:"surrogate",ref,...bootstrap(a.map((v,i)=>v.v-c[i].v),(0xC1200000+b*100+modes.indexOf(ref))>>>0)});
  }
 }
 return {rows,paired,costs,audit};
}
function experiment12(frozen){
 const start=Date.now(),gradient=gradient12(),dev=localRows12(1840001,512),val=localRows12(1850001,128),trained=train12(dev.rows,val.rows);
 const test=localRows12(1860001,256),metrics=metrics12(test.rows,trained.best.weights);
 const global=global12(trained.best.weights,frozen.training.choices.recurrent.weights);
 return {status:"PASS",scope:"exact local formula and distilled predictor on finite synthetic independent branches",gradient,datasets:{development:dev.stat,validation:val.stat,test:test.stat},training:trained,localTest:metrics,global,elapsedMs:Date.now()-start};
}
const frozen=JSON.parse(readFileSync(new URL("./information_gain_receipt.json",import.meta.url),"utf8"));
console.log(JSON.stringify(experiment12(frozen),null,2));
