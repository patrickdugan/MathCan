import {pathToFileURL} from "node:url";
// CRD-11A: exact finite decision teacher and learned action advantage heads.
import {rng} from "./search.mjs";
const D=6,F=20;
const sum=a=>a.reduce((s,v)=>s+v,0),dot=(a,b)=>sum(a.map((v,i)=>v*b[i])),zeros=n=>Array(n).fill(0);
function ok(v,m){if(!v)throw Error(m)}
function gcd(a,b){while(b){[a,b]=[b,a%b]}return a}
function norm(w){const g=w.reduce(gcd,0);ok(g>0,"empty belief");return w.map(x=>x/g)}
function predicate(j,x){return j===0?x%2:j===1?Number(x<3):Number(x%3===0)}
function fixture(seed,n,maxStages){
 const r=rng(seed),branches=[];
 for(let i=0;i<n;i++){const prior=Array.from({length:D},()=>1+Math.floor(r()*12)),L=1+Math.floor(r()*maxStages),sensors=Array.from({length:L},()=>[60,80,100][Math.floor(r()*3)]);branches.push({prior,sensors})}
 return {seed,branches};
}
class Local {
 constructor(spec){
  this.spec=spec;this.L=spec.sensors.length;this.states=[];this.ids=new Map();this.trans=new Map();this.memo=new Map();
  this.stats={states:0,transitions:0,queries:0};
  ok(this.intern(0,spec.prior)===0,"initial id");
 }
 intern(stage,w){
  const a=norm(w),key=stage+":"+a.join(",");
  if(this.ids.has(key))return this.ids.get(key);
  const z=sum(a),p=a.map(x=>x/z),top=p.slice(0,3).sort((a,b)=>b-a),id=this.states.length;
  this.states.push({stage,w:a,p,max:top[0],mass:sum(top),top2:top[0]+top[1]});this.ids.set(key,id);return id;
 }
 at(id){return this.states[id]}
 actions(id,b){
  if(id<0||b<=0)return [];
  const s=this.at(id);if(s.mass===0)return [];
  if(s.stage<this.L)return b>=this.L-s.stage+1?[0]:[];
  return [1,2,3].filter(a=>s.w[a-1]>0);
 }
 outcomes(id,a){
  const key=id+":"+a;if(this.trans.has(key))return this.trans.get(key);
  const s=this.at(id),w=s.w,z=sum(w);let out=[];
  if(a===0){
   ok(s.stage<this.L,"sensor stage");const acc=this.spec.sensors[s.stage];
   for(const bit of [0,1]){
    const v=w.map((x,i)=>x*(predicate(s.stage,i)===bit?acc:100-acc)),mass=sum(v);
    if(mass)out.push({p:mass/(100*z),id:sum(v.slice(0,3))?this.intern(s.stage+1,v):-1,hit:false});
   }
  }else{
   ok(s.stage===this.L&&w[a-1]>0,"probe support");
   const p=w[a-1]/z;out.push({p,hit:true,id:-1});
   if(p<1){const v=w.slice();v[a-1]=0;out.push({p:1-p,hit:false,id:sum(v.slice(0,3))?this.intern(s.stage,v):-1})}
  }
  ok(Math.abs(sum(out.map(o=>o.p))-1)<1e-12,"transition mass");this.trans.set(key,out);return out;
 }
 value(id,b){
  this.stats.queries++;if(id<0||b<=0)return 0;
  const key=id+":"+b;if(this.memo.has(key))return this.memo.get(key);
  const v=Math.max(0,...this.actions(id,b).map(a=>this.q(id,a,b)));
  this.memo.set(key,v);this.stats.states++;return v;
 }
 q(id,a,b){
  const out=this.outcomes(id,a);this.stats.transitions+=out.length;
  return sum(out.map(o=>o.p*(o.hit?1:this.value(o.id,b-1))));
 }
 nextBest(id){
  const s=this.at(id);if(s.stage>=this.L)return 0;
  return sum(this.outcomes(id,0).map(o=>o.p*(o.id<0?0:this.at(o.id).max)));
 }
}
class Problem {
 constructor(root,cap){
  this.root=root;this.cap=cap;this.local=root.branches.map(s=>new Local(s));
  this.scoreEvals=0;this.featureEvals=0;this.rollout=null;
 }
 initial(){return this.local.map(()=>0)}
 active(s){return s.map((id,i)=>id>0&&this.local[i].at(id).stage>0&&this.local[i].at(id).mass>0?i:-1).filter(i=>i>=0)}
 legal(s,b){
  if(b<=0)return [];
  const active=this.active(s),out=[];
  ok(active.length<=this.cap,"capacity");
  for(let i=0;i<s.length;i++)for(const t of this.local[i].actions(s[i],b)){
   const victims=t===0&&s[i]===0&&active.length>=this.cap?active:[-1];
   for(const evict of victims)out.push({i,t,evict,id:(i*4+t)*4+evict+1});
  }
  ok(new Set(out.map(a=>a.id)).size===out.length,"action id");return out;
 }
 outcomes(s,a){
  return this.local[a.i].outcomes(s[a.i],a.t).map(o=>{
   if(o.hit)return {p:o.p,hit:true,s:null};
   const next=s.slice();next[a.i]=o.id;if(a.evict>=0)next[a.evict]=-1;
   ok(this.active(next).length<=this.cap,"transition capacity");return {p:o.p,hit:false,s:next};
  });
 }
 current(s,a,prior=false){
  const l=this.local[a.i],v=l.at(prior?0:s[a.i]);return a.t===0?v.max:v.p[a.t-1];
 }
 sensor(s,a){
  const l=this.local[a.i],v=l.at(s[a.i]);
  return a.t===0?l.nextBest(s[a.i])/Math.max(1,l.L-v.stage):v.p[a.t-1];
 }
 evictMass(s,a,prior=false){return a.evict<0?0:this.local[a.evict].at(prior?0:s[a.evict]).mass}
 features(s,a,b){
  this.featureEvals++;
  const i=a.i,l=this.local[i],v=l.at(s[i]),remain=l.L-v.stage,reveal=a.t===0;
  const other=s.map((id,j)=>({id,j})).filter(o=>o.j!==i&&o.id>=0),bestOther=Math.max(0,...other.map(({id,j})=>this.local[j].value(id,b)));
  const otherProbe=Math.max(0,...other.map(({id,j})=>this.local[j].at(id).stage===this.local[j].L?this.local[j].at(id).max:0));
  const next=reveal?l.nextBest(s[i]):0,ev=a.evict;
  const x=[Number(reveal),b/8,remain/3,reveal?0:v.p[a.t-1],v.max,v.mass,v.top2,next,reveal?next-v.max:0,l.q(s[i],a.t,b),l.value(s[i],b),otherProbe,bestOther,sum(other.map(({id,j})=>this.local[j].at(id).mass))/3,this.active(s).length/3,this.cap/3,Number(ev>=0),this.evictMass(s,a),ev<0?0:this.local[ev].value(s[ev],b),this.sensor(s,a)];
  ok(x.length===F&&x.every(Number.isFinite),"feature");return x;
 }
 choose(s,b,kind,w){
  const all=this.legal(s,b);if(!all.length)return null;
  const probes=all.filter(a=>a.t!==0);
  let actions=all;
  if(["depth","marginal","noFeedback"].includes(kind))actions=probes.length?probes:all;
  const prior=kind==="noFeedback";
  const score=a=>{
   if(kind==="depth")return 0;
   if(kind==="marginal"||kind==="noFeedback")return this.current(s,a,prior)-.01*this.evictMass(s,a,prior);
   if(kind==="sensor"||kind==="randomEvict")return this.sensor(s,a)-(kind==="sensor"?.01*this.evictMass(s,a):0);
   if(kind==="local")return this.local[a.i].q(s[a.i],a.t,b)-(a.evict<0?0:.25*this.local[a.evict].value(s[a.evict],b));
   if(kind==="rollout"){
    if(!this.rollout)this.rollout=new Engine(this,"sensor",null);
    const out=this.outcomes(s,a);this.rollout.stats.lookaheadTransitions+=out.length;
    return sum(out.map(o=>o.p*(o.hit?1:this.rollout.rec(o.s,b-1).v)));
   }
   return predict(kind,w,this.features(s,a,b));
  };
  const ranked=actions.map(a=>({a,v:score(a)}));this.scoreEvals+=ranked.length;
  ranked.sort((x,y)=>y.v-x.v||y.a.id-x.a.id);let chosen=ranked[0].a;
  if(kind==="randomEvict"&&chosen.evict>=0){
   const vs=all.filter(a=>a.i===chosen.i&&a.t===chosen.t);let hash=(this.root.seed^Math.imul(b+1,0x9E3779B9))>>>0;
   for(const id of s)hash=Math.imul(hash^(id+2),16777619)>>>0;
   chosen=vs[Math.floor(rng(hash)()*vs.length)];
  }
  return chosen;
 }
}
function zeroResult(peak){return {v:0,calls:0,sensors:0,probes:0,evictions:0,peak,action:null,qs:[]}}
class Engine {
 constructor(problem,kind,w){
  this.P=problem;this.kind=kind;this.w=w;this.memo=new Map();
  this.stats={states:0,transitions:0,actions:0,lookaheadTransitions:0,expandWithProbe:0};
 }
 q(s,a,b){
  const P=this.P,out=P.outcomes(s,a);this.stats.transitions+=out.length;
  let r={v:0,calls:1,sensors:Number(a.t===0),probes:Number(a.t!==0),evictions:Number(a.evict>=0),peak:P.active(s).length,action:a};
  for(const o of out){
   if(o.hit){r.v+=o.p;continue}
   const z=this.rec(o.s,b-1);
   for(const k of ["v","calls","sensors","probes","evictions"])r[k]+=o.p*z[k];
   r.peak=Math.max(r.peak,z.peak);
  }
  ok(r.v>=-1e-12&&r.v<=1+1e-12&&r.calls<=b+1e-10&&r.peak<=P.cap,"Bellman bounds");
  return r;
 }
 rec(s,b){
  const P=this.P;if(b<=0)return zeroResult(P.active(s).length);
  const key=b+":"+s.join(",");if(this.memo.has(key))return this.memo.get(key);
  const legal=P.legal(s,b),actions=this.kind==="optimal"?legal:[P.choose(s,b,this.kind,this.w)].filter(Boolean);
  let best=zeroResult(P.active(s).length),qs=[];
  for(const a of actions){
   const r=this.q(s,a,b);this.stats.actions++;qs.push({a,q:r.v});
   if(!best.action||r.v>best.v+1e-14||(Math.abs(r.v-best.v)<=1e-14&&a.id>best.action.id))best=r;
  }
  best={...best,qs,s:s.slice(),b};this.stats.states++;
  this.stats.expandWithProbe+=Number(best.action&&best.action.t===0&&legal.some(a=>a.t>0));
  this.memo.set(key,best);return best;
 }
}
const modelKinds=["linear","mlp","recurrent"];
function init(kind){
 const n={linear:21,mlp:177,recurrent:136}[kind],r=rng({linear:502,mlp:503,recurrent:504}[kind]);
 return Array.from({length:n},()=>.2*r()-.1);
}
function forward(kind,w,x){
 if(kind==="linear")return {v:dot(w.slice(0,F),x)+w[F]};
 if(kind==="mlp"){
  const h=Array.from({length:8},(_,i)=>Math.tanh(w[160+i]+dot(w.slice(F*i,F*i+F),x)));
  return {v:dot(w.slice(168,176),h)+w[176],hs:[h]};
 }
 const hs=[zeros(5)],wx=Array.from({length:5},(_,i)=>w[125+i]+dot(w.slice(F*i,F*i+F),x));
 for(let t=0;t<3;t++){
  const prev=hs[t],h=Array.from({length:5},(_,i)=>Math.tanh(wx[i]+dot(w.slice(100+5*i,105+5*i),prev)));hs.push(h);
 }
 return {v:dot(w.slice(130,135),hs[3])+w[135],hs};
}
function predict(kind,w,x){return forward(kind,w,x).v}
function grad(kind,w,x,y,g){
 const {v,hs}=forward(kind,w,x),d=v-y; // half squared error
 if(kind==="linear"){for(let j=0;j<F;j++)g[j]+=d*x[j];g[F]+=d;return}
 if(kind==="mlp"){
  const h=hs[0];g[176]+=d;
  for(let i=0;i<8;i++){g[168+i]+=d*h[i];const z=d*w[168+i]*(1-h[i]**2);g[160+i]+=z;for(let j=0;j<F;j++)g[F*i+j]+=z*x[j]}return;
 }
 g[135]+=d;let dh=zeros(5);
 for(let i=0;i<5;i++){g[130+i]+=d*hs[3][i];dh[i]=d*w[130+i]}
 for(let t=3;t>=1;t--){
  const prev=zeros(5);
  for(let i=0;i<5;i++){const z=dh[i]*(1-hs[t][i]**2);g[125+i]+=z;
   for(let j=0;j<F;j++)g[F*i+j]+=z*x[j];
   for(let j=0;j<5;j++){g[100+5*i+j]+=z*hs[t-1][j];prev[j]+=z*w[100+5*i+j]}
  }dh=prev;
 }
}
function gradAudit(){
 const x=Array.from({length:F},(_,i)=>(i%7-3)/7),y=-.25,out={};
 for(const kind of modelKinds){
  const w=init(kind),g=zeros(w.length);grad(kind,w,x,y,g);let err=0;
  for(let i=0;i<w.length;i++){const old=w[i],eps=1e-5;w[i]=old+eps;const a=.5*(predict(kind,w,x)-y)**2;w[i]=old-eps;const b=.5*(predict(kind,w,x)-y)**2;w[i]=old;err=Math.max(err,Math.abs(g[i]-(a-b)/(2*eps)))}
  ok(err<1e-7,"gradient");out[kind]=err;
 }return out;
}
function teacher(){
 const states=[],stat={roots:384,teacherStates:0,teacherTransitions:0,teacherActions:0,sampledStates:0,labels:0,tiedOptimalActions:0,nontrivial:0,evictionLabels:0,evictionStates:0,localStates:0,localTransitions:0};
 for(let i=0;i<384;i++){
  const root=fixture(1740001+i,2,2),cap=1+i%2,b=3+i%3,P=new Problem(root,cap),E=new Engine(P,"optimal",null);E.rec(P.initial(),b);
  for(const k of ["states","transitions","actions"])stat["teacher"+k[0].toUpperCase()+k.slice(1)]+=E.stats[k];
  const r=rng((root.seed^0x8F6A28D1)>>>0),sample=[];let seen=0;
  for(const v of E.memo.values()){
   if(v.qs.length<2)continue;seen++;
   if(sample.length<24)sample.push(v);else{const j=Math.floor(r()*seen);if(j<24)sample[j]=v}
  }
  for(const v of sample){
   let distinct=false,eviction=false;const examples=[];
   for(const {a,q} of v.qs){const y=q-v.v;ok(y<=1e-12&&y>=-1-1e-12,"advantage");examples.push({x:P.features(v.s,a,v.b),y});stat.labels++;stat.tiedOptimalActions+=Number(Math.abs(y)<1e-12);distinct ||= y<-1e-12;stat.evictionLabels+=Number(a.evict>=0);eviction ||= a.evict>=0}
   states.push(examples);stat.sampledStates++;stat.nontrivial+=Number(distinct);stat.evictionStates+=Number(eviction);
  }
  for(const l of P.local){stat.localStates+=l.stats.states;stat.localTransitions+=l.stats.transitions}
 }
 ok(stat.labels>0&&stat.nontrivial>0&&stat.evictionLabels>0,"teacher signal");return {states,stat};
}
function validate(roots,kind,w){
 let v=0,calls=0;
 for(let i=0;i<roots.length;i++){const P=new Problem(roots[i],1+i%2),E=new Engine(P,kind,w),z=E.rec(P.initial(),3+i%3);v+=z.v;calls+=z.calls}
 return {value:v/roots.length,calls:calls/roots.length};
}
function train(data,val){
 const choices={},history=[];
 for(const kind of modelKinds){
  const w=init(kind),r=rng(711);let best=null;
  for(let ep=1;ep<=16;ep++){
   for(let b=0;b<64;b++){
    const g=zeros(w.length);
    for(let j=0;j<32;j++){const state=data.states[Math.floor(r()*data.states.length)],row=state[Math.floor(r()*state.length)];grad(kind,w,row.x,row.y,g)}
    for(let j=0;j<w.length;j++)w[j]-=.08*g[j]/32;
   }
   if([1,4,8,16].includes(ep)){
    const m=validate(val,kind,w),loss=sum(data.states.map(rows=>sum(rows.map(row=>(predict(kind,w,row.x)-row.y)**2))/rows.length))/data.states.length;
    const c={kind,epoch:ep,...m,trainMSE:loss,weights:w.slice()};history.push({kind,epoch:ep,...m,trainMSE:loss});
    if(!best||m.value>best.value+1e-14||(Math.abs(m.value-best.value)<=1e-14&&m.calls<best.calls-1e-14))best=c;
   }
  }choices[kind]=best;
 }return {choices,history};
}
function forwardWorld(root,E,budget){
 const P=E.P,n=root.branches.length,h=zeros(n);let total=0,worlds=0;
 const pred=(j,x)=>[ [0,1,0,1,0,1],[1,1,1,0,0,0],[1,0,0,1,0,0] ][j][x];
 function evaluate(s,b){
  if(b<=0)return 0;
  const a=E.rec(s,b).action;if(!a)return 0;
  const l=P.local[a.i],v=l.at(s[a.i]),state=s.slice();
  if(a.evict>=0)state[a.evict]=-1;
  if(a.t>0){
   if(h[a.i]===a.t-1)return 1;
   const w=v.w.slice();w[a.t-1]=0;state[a.i]=sum(w.slice(0,3))?l.intern(v.stage,w):-1;return evaluate(state,b-1);
  }
  const acc=l.spec.sensors[v.stage];let out=0;
  for(const bit of [0,1]){
   const q=(pred(v.stage,h[a.i])===bit?acc:100-acc)/100;if(!q)continue;
   const w=v.w.map((x,j)=>x*(pred(v.stage,j)===bit?acc:100-acc)),ns=state.slice();
   ok(sum(w)>0,"world evidence support");ns[a.i]=sum(w.slice(0,3))?l.intern(v.stage+1,w):-1;out+=q*evaluate(ns,b-1);
  }return out;
 }
 function enumerate(i,weight){
  if(i===n){worlds++;total+=weight*evaluate(P.initial(),budget);return}
  const w=root.branches[i].prior,z=sum(w);
  for(let x=0;x<D;x++){h[i]=x;enumerate(i+1,weight*w[x]/z)}
 }
 enumerate(0,1);return {value:total,worlds};
}
function handChecks(){
 const spec=(w,L)=>({prior:w,sensors:Array(L).fill(100)});
 const one={seed:1,branches:[spec([1,1,0,0,0,0],1),spec([1,1,0,0,0,0],1)]},uni={seed:2,branches:[spec([1,1,1,1,1,1],1),spec([1,1,1,1,1,1],1)]};
 for(const cap of [1,2]){
  const a=new Problem(one,cap),b=new Problem(uni,cap),x=new Engine(a,"optimal"),y=new Engine(b,"optimal");
  ok(x.rec(a.initial(),1).v===0&&Math.abs(x.rec(a.initial(),2).v-1)<1e-12,"perfect sensor");
  ok(Math.abs(y.rec(b.initial(),2).v-1/3)<1e-12,"uniform");
 }return 4;
}
function bootstrap(diffs,seed){
 const r=rng(seed),n=diffs.length,means=[];
 for(let k=0;k<2000;k++){let s=0;for(let j=0;j<n;j++)s+=diffs[Math.floor(r()*n)];means.push(s/n)}
 means.sort((a,b)=>a-b);return {mean:sum(diffs)/n,low:means[49],high:means[1949],wins:diffs.filter(v=>v>1e-12).length,losses:diffs.filter(v=>v<-1e-12).length,ties:diffs.filter(v=>Math.abs(v)<=1e-12).length};
}
function test(trained){
 const kinds=["depth","noFeedback","marginal","sensor","local","rollout","randomEvict",...modelKinds,"optimal"],rows=[],paired=[],audit={hand:handChecks(),monotonic:0,independentChecks:0,worlds:0,maxError:0,policyRootBudgets:0};
 for(const regime of ["ID","OOD"]){
  const roots=Array.from({length:192},(_,i)=>fixture((regime==="ID"?1760001:1770001)+i,regime==="ID"?2:3,regime==="ID"?2:3)),budgets=regime==="ID"?[3,5]:[4,6];
  for(const cap of [1,2]){
   const all=Object.fromEntries(budgets.map(b=>[b,Object.fromEntries(kinds.map(k=>[k,[]]))]));
   const costs=Object.fromEntries(kinds.map(k=>[k,{states:0,transitions:0,actions:0,scoreEvals:0,features:0,localStates:0,localTransitions:0,localQueries:0,rolloutStates:0,rolloutTransitions:0,rolloutLookaheadTransitions:0,expandWithProbe:0}]));
   for(let i=0;i<roots.length;i++){
    const root=roots[i];let optimum=[];
    for(const kind of ["optimal",...kinds.filter(k=>k!=="optimal")]){
     const P=new Problem(root,cap),E=new Engine(P,kind,trained.choices[kind]?.weights??null),res=[];
     for(let j=0;j<budgets.length;j++){
      const b=budgets[j],v=E.rec(P.initial(),b);res.push(v);
      if(kind==="optimal")optimum.push(v);else ok(v.v<=optimum[j].v+1e-10,"oracle domination");
      all[b][kind].push({v:v.v,calls:v.calls,sensors:v.sensors,probes:v.probes,evictions:v.evictions,peak:v.peak,regret:optimum[j].v-v.v,firstDifferent:Number(v.action?.id!==optimum[j].action?.id)});
      audit.policyRootBudgets++;
     }
     if(kind==="optimal"){ok(res[1].v>=res[0].v-1e-12,"budget monotonic");audit.monotonic++}
     if(cap===2&&i<(regime==="ID"?8:4)&&["optimal","recurrent"].includes(kind)){
      const z=forwardWorld(root,E,budgets[1]),err=Math.abs(z.value-res[1].v);ok(err<1e-10,"independent world check");audit.independentChecks++;audit.worlds+=z.worlds;audit.maxError=Math.max(audit.maxError,err);
     }
     const c=costs[kind];for(const k of ["states","transitions","actions","expandWithProbe"])c[k]+=E.stats[k];c.scoreEvals+=P.scoreEvals;c.features+=P.featureEvals;
     for(const l of P.local){c.localStates+=l.stats.states;c.localTransitions+=l.stats.transitions;c.localQueries+=l.stats.queries}
     if(P.rollout){c.rolloutStates+=P.rollout.stats.states;c.rolloutTransitions+=P.rollout.stats.transitions;c.rolloutLookaheadTransitions+=P.rollout.stats.lookaheadTransitions}
    }
   }
   for(const b of budgets){
    for(const kind of kinds){
     const a=all[b][kind],mean=k=>sum(a.map(v=>v[k]))/a.length;
     rows.push({regime,cap,budget:b,kind,roots:a.length,expectedSuccess:mean("v"),meanRegret:mean("regret"),expectedCalls:mean("calls"),expectedSensors:mean("sensors"),expectedProbes:mean("probes"),expectedEvictions:mean("evictions"),peakActive:Math.max(...a.map(v=>v.peak)),peakBeliefSlots:6*Math.max(...a.map(v=>v.peak)),firstDifferent:sum(a.map(v=>v.firstDifferent))});
    }
    for(const ref of kinds.filter(k=>k!=="recurrent")){
     const a=all[b].recurrent,other=all[b][ref],diff=a.map((v,i)=>v.v-other[i].v);
     paired.push({regime,cap,budget:b,kind:"recurrent",ref,...bootstrap(diff,(0xCA5E0000+cap*1000+b*100+kinds.indexOf(ref)+(regime==="OOD"?10000:0))>>>0)});
    }
   }
   // Costs aggregate both budgets, sharing within-root memoization; not a per-deployment benchmark.
   rows.push({regime,cap,costsAcrossBudgets:costs});
  }
 }
 return {rows,paired,audit};
}
function experiment11(){
 const start=Date.now(),gradients=gradAudit(),data=teacher(),val=Array.from({length:96},(_,i)=>fixture(1750001+i,2,2)),trained=train(data,val);
 const evaluation=test(trained);
 return {status:"PASS",scope:"finite independent-branch decision model with explicit abandonment; no factoring result",gradients,teacher:data.stat,training:{validationRoots:96,epochs:16,batchesPerEpoch:64,batchSize:32,learningRate:.08,parameters:{linear:21,mlp:177,recurrent:136},...trained},evaluation,elapsedMs:Date.now()-start};
}
export {D,F,ok,sum,zeros,fixture,Problem,Engine,teacher,modelKinds,init,grad,predict,forwardWorld,bootstrap,experiment11};
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(experiment11(),null,2));
