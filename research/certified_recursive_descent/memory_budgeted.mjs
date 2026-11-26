import {pathToFileURL} from "node:url";
// CRD-10: bounded evidence arena, certified stale ranking, finite information oracle.
import {verify,upperRoot} from "./audit.mjs";
import {rng} from "./search.mjs";
import {ok,exactPaired} from "./learned_frontier.mjs";
const D=6,LABEL=[2,5,1,4,0,3],INV=Array.from({length:D},(_,i)=>LABEL.indexOf(i));
const sum=x=>x.reduce((s,v)=>s+v,0),dot=(a,b)=>sum(a.map((v,i)=>v*b[i])),one=()=>Array(D).fill(1),unit=i=>Array.from({length:D},(_,j)=>Number(i===j));
const prod=(a,b)=>a.map((v,i)=>v*b[i]),quant=x=>Math.round(x*1e12)/1e12;
const par=id=>Math.floor((id-1)/3),kids=id=>[3*id+1,3*id+2,3*id+3];
function depth(id){let d=0;while(id>0){id=par(id);d++}return d}
function gmul(a,b){const k=a%3,s=a>=3?1:0,l=b%3,t=b>=3?1:0;return 3*(s^t)+(k+(s?-l:l)+3)%3}
const PERM=[1,3].map(g=>Array.from({length:D},(_,i)=>LABEL[gmul(INV[i],g)]));
const explicit=g=>[0,1,2].map(x=>(g%3+(g>=3?-x:x)+3)%3);
const levels=(regime,d,L)=>regime==="independent"&&d===L?[1]:d===1?[.60,.80]:[0,.05,.15];
function col(a,c,m){const u=c*sum(m)/D;return PERM[a].map(j=>(1-c)*m[j]+u)}
function row(p,a,c){const q=Array(D).fill(c*sum(p)/D);for(let i=0;i<D;i++)q[PERM[a][i]]+=(1-c)*p[i];return q}
const FORECAST=new Map();
function forecast(regime,L,target){
 const key=[regime,L,target].join(":");if(FORECAST.has(key))return FORECAST.get(key);
 const f=Array(L+1);f[L]=unit(target);
 for(let d=L-1;d>=0;d--){
  const cs=levels(regime,d+1,L),rows=[0,1].flatMap(a=>cs.map(c=>col(a,c,f[d+1])));
  f[d]=one().map((_,i)=>sum(rows.map(r=>r[i]))/rows.length);
 }
 FORECAST.set(key,f);return f;
}
function cert(id,d){const pDen=23,pNum=1+(id+3*d)%22,rDen=5000,rNum=upperRoot(pNum,pDen,rDen),c=10400,a=Math.floor((c*(rDen-rNum)-1)/rDen);return {pNum,pDen,rNum,rDen,a,c}}
function checkCert(c){return BigInt(c.rNum)**3n*BigInt(c.pDen)>=BigInt(c.pNum)*BigInt(c.rDen)**3n&&BigInt(c.a)*BigInt(c.rDen)<BigInt(c.c)*BigInt(c.rDen-c.rNum)}
function tree(seed,regime){
 const r=rng(seed),L=4+Math.floor(r()*2),target=Math.floor(r()*D),nodes=[{id:0,d:0,h:0}];
 const count=(3**(L+1)-1)/2;
 for(let id=1;id<count;id++){
  const p=nodes[par(id)],d=p.d+1,a=Math.floor(r()*2),cs=levels(regime,d,L),c=cs[Math.floor(r()*cs.length)],reset=r()<c,replacement=Math.floor(r()*D);
  nodes.push({id,d,a,c,reset,replacement,h:reset?replacement:gmul(p.h,a===0?1:3),cert:cert(id,d)});
 }return {seed,regime,L,target,nodes};
}
function terminal(root,id){
 const path=[];for(let i=id;i>0;i=par(i))path.push(root.nodes[i]);
 let h=explicit(0);
 for(const n of path.reverse()){if(n.reset)h=explicit(n.replacement);else h=explicit(n.a===0?1:3).map(x=>h[x])}
 const g=Array.from({length:D},(_,i)=>i).find(i=>explicit(i).every((v,j)=>v===h[j]));
 ok(root.nodes[id].d===root.L&&g===root.nodes[id].h,"terminal witness");return LABEL[g]===root.target;
}
const LIMIT={workLimit:true};
class Arena{
 constructor(B,cap,target,limit){
  this.B=B;this.cap=cap;this.target=target;this.limit=limit;
  this.reserve=4*(cap+2);
  this.records=new Map([[0,{id:0,a:0,c:0,fail:0,count:0}]]);this.cache=new Map();this.version=0;
  this.stats={transports:0,up:0,down:0,queries:0,hits:0,misses:0,evictions:0,invalidations:0,skips:0,peakSlots:0,peakCacheVectors:0,scratchSlotsUpper:0,schedules:0,reused:0,refined:0,certified:0,fallbackRounds:0};
  this.trim();
 }
 base(){return 5*this.records.size+this.reserve}
 capacity(){return Math.max(0,Math.floor((this.B-this.base())/D))}
 trim(){
  ok(this.base()<=this.B,"arena base overflow");
  while(this.cache.size>this.capacity()){this.cache.delete(this.cache.keys().next().value);this.stats.evictions++}
  this.stats.peakSlots=Math.max(this.stats.peakSlots,this.base()+D*this.cache.size);this.stats.peakCacheVectors=Math.max(this.stats.peakCacheVectors,this.cache.size);
  ok(this.base()+D*this.cache.size<=this.B,"arena overflow");
 }
 canObserve(){return this.base()+5<=this.B}
 observe(id,a,c){
  ok(this.canObserve()&&id>0&&this.records.has(par(id))&&!this.records.has(id),"observe");
  this.records.set(id,{id,a,c,fail:0,count:0});this.trim();
 }
 fail(id,useEvidence){
  const x=this.records.get(id);ok(x&&!x.fail,"duplicate evidence");x.fail=1;
  if(!useEvidence)return;
  this.version++;
  for(let n=id;;n=par(n)){this.records.get(n).count++;if(this.cache.delete(n))this.stats.invalidations++;if(n===0)break}
 }
 spend(dir){if(this.stats.transports>=this.limit)throw LIMIT;this.stats.transports++;this.stats[dir]++}
 local(id){
  const x=this.records.get(id);let v=one();
  // count==0 means no evidence, including the no-feedback arm.
  if(x.fail&&x.count)v[this.target]=0;
  for(const ch of kids(id))if(this.records.has(ch))v=prod(v,this.message(ch));
  return v;
 }
 message(id){
  const n=this.records.get(id);ok(id>0&&n,"message record");
  if(!n.count){this.stats.skips++;return one()}
  if(this.cache.has(id)){const v=this.cache.get(id);this.cache.delete(id);this.cache.set(id,v);this.stats.hits++;return v}
  this.stats.misses++;
  const m=this.local(id);this.spend("up");const v=col(n.a,n.c,m);
  if(this.capacity()>0){this.cache.set(id,v);this.trim()}
  return v;
 }
 Z(){return this.local(0)[LABEL[0]]}
 batch(ids,z,F){
  if(!ids.length)return new Map();
  ok(z>1e-14,"impossible evidence");const wanted=new Set(ids),paths=new Set([0]),result=new Map();
  for(const id of ids)for(let n=id;n>0;n=par(n))paths.add(n);
  // Conservative payload upper bound for transient union IDs, result pairs and
  // recursive vectors (including nested upward recursion), not measured JS heap.
  this.stats.scratchSlotsUpper=Math.max(this.stats.scratchSlotsUpper,paths.size+2*ids.length+8*D*(F.length+1));
  const visit=(id,p)=>{
   if(wanted.has(id)){
    const v=prod(p,this.local(id)).map(x=>x/z);
    ok(Math.abs(sum(v)-1)<1e-8&&v.every(x=>x>=-1e-9),"posterior");
    const score=dot(v,F[depth(id)]);result.set(id,Math.max(0,Math.min(1,score)));this.stats.queries++;
   }
   const rec=this.records.get(id);
   for(const child of kids(id))if(paths.has(child)){
    let q=p.slice();if(rec.fail&&rec.count)q[this.target]=0;
    for(const sib of kids(id))if(sib!==child&&this.records.has(sib))q=prod(q,this.message(sib));
    const x=this.records.get(child);this.spend("down");visit(child,row(q,x.a,x.c));
   }
  };
  visit(0,unit(LABEL[0]));ok(result.size===wanted.size,"batch completeness");return result;
 }
}
function cmp(a,b,s){return s(b)-s(a)||b.id-a.id}
function depthScore(e){return 2*depth(e.id)}
function rankExact(bank,cap){return bank.slice().sort((a,b)=>cmp(a,b,e=>depthScore(e)+quant(e.p))).slice(0,cap)}
function schedule(arena,bank,engine,F,cap){
 arena.stats.schedules++;
 if(engine==="depth")return bank.slice().sort((a,b)=>cmp(a,b,depthScore)).slice(0,cap);
 try{
  const z=arena.Z();ok(z>1e-14,"known evidence zero");
  function refine(entries,path=false){
   if(!entries.length)return;
   const q=path?new Map(entries.flatMap(e=>[...arena.batch([e.id],z,F)])):arena.batch(entries.map(e=>e.id),z,F);
   for(const e of entries){e.p=q.get(e.id);e.z=z;e.version=arena.version}
   arena.stats.refined+=entries.length;
  }
  if(engine!=="lazy"){refine(bank,engine==="path");return rankExact(bank,cap)}
  const missing=bank.filter(e=>e.p===null);refine(missing);
  const before=bank.filter(e=>!missing.includes(e)).length;arena.stats.reused+=before;
  function interval(e){
   if(e.version===arena.version)return [quant(e.p),quant(e.p)];
   ok(e.z>0&&z<=e.z+1e-10,"nonmonotone evidence");
   const eps=Math.max(0,1-z/e.z)+1e-12;
   return [quant(Math.max(0,e.p-eps)),quant(Math.min(1,e.p+eps))];
  }
  for(let round=0;round<=bank.length;round++){
   const ranges=new Map(bank.map(e=>[e.id,interval(e)]));
   const low=e=>depthScore(e)+ranges.get(e.id)[0],high=e=>depthScore(e)+ranges.get(e.id)[1];
   const sorted=bank.slice().sort((a,b)=>cmp(a,b,low)),chosen=sorted.slice(0,cap),outside=sorted.slice(cap),top=chosen[0],amb=new Set();
   function certify(a,b){
    const v=low(a)-high(b);
    if(v>0||(v===0&&a.id>b.id))return;
    for(const e of [a,b])if(e.version!==arena.version)amb.add(e);
    ok(amb.size>0,"exact ranking inconsistency");
   }
   for(const e of sorted)if(e!==top)certify(top,e);
   for(const a of chosen)for(const b of outside)certify(a,b);
   if(!amb.size){arena.stats.certified++;return chosen}
   refine([...amb]);
  }
  throw Error("lazy refinement bound");
 }catch(e){
  if(e!==LIMIT)throw e;
  arena.stats.fallbackRounds++;return bank.slice().sort((a,b)=>cmp(a,b,depthScore)).slice(0,cap);
 }
}
// Independent dense posterior recomputation from reached records only.
function oracleRank(arena,bank,F,cap){
 const target=arena.target,records=arena.records;
 const T=(rec,x,y)=>rec.c/D+(1-rec.c)*Number(PERM[rec.a][x]===y);
 const up=new Map(),edge=new Map(),ids=[...records.keys()].sort((a,b)=>b-a);
 function localEvidence(id,i){const n=records.get(id);return n.fail&&n.count&&i===target?0:1}
 for(const id of ids){
  const v=Array.from({length:D},(_,i)=>localEvidence(id,i)*kids(id).reduce((p,ch)=>p*(edge.has(ch)?edge.get(ch)[i]:1),1));
  up.set(id,v);
  if(id>0)edge.set(id,Array.from({length:D},(_,i)=>sum(v.map((m,j)=>T(records.get(id),i,j)*m))));
 }
 const z=up.get(0)[LABEL[0]];ok(z>0,"audit Z");
 const scores=new Map();
 for(const e of bank){
  const path=[];for(let n=e.id;n>0;n=par(n))path.push(n);path.reverse();let p=unit(LABEL[0]),parent=0;
  for(const id of path){
   const q=p.map((v,i)=>v*localEvidence(parent,i)*kids(parent).reduce((r,ch)=>r*(ch!==id&&edge.has(ch)?edge.get(ch)[i]:1),1));
   p=Array.from({length:D},(_,j)=>sum(q.map((v,i)=>v*T(records.get(id),i,j))));parent=id;
  }
  const v=prod(p,up.get(e.id)).map(x=>x/z);scores.set(e.id,dot(v,F[depth(e.id)]));
 }
 const order=bank.slice().sort((a,b)=>cmp(a,b,e=>depthScore(e)+quant(scores.get(e.id)))).slice(0,cap);
 return {order,scores};
}
function sameChoice(a,b){return a[0]?.id===b[0]?.id&&a.map(x=>x.id).sort((a,b)=>a-b).join(",")===b.map(x=>x.id).sort((a,b)=>a-b).join(",")}
function run(root,B,cap,engine,limit=Infinity,audit=false){
 const arena=new Arena(B,cap,root.target,limit),F=forecast(root.regime,root.L,root.target),feedback=engine!=="marginal"&&engine!=="depth",method=engine==="marginal"?"batch":engine;
 let bank=[{id:0,p:null,z:null,version:-1}],calls=0,prefix=0,probes=0,success=false,memoryStop=false,peakBank=1,transient=1;
 const trace=[],decisions=[],expanded=new Set(),aud={states:0,scoreChecks:0,maxError:0,topChanged:0,setChanged:0};
 while(bank.length&&calls<48){
  const e=bank.shift(),id=e.id;ok(arena.records.has(id)&&!expanded.has(id),"frontier");expanded.add(id);
  if(depth(id)===root.L){
   calls++;probes++;success=terminal(root,id);trace.push(["probe",id,success]);
   if(success)break;arena.fail(id,feedback);
  }else{
   for(const ch of kids(id)){
    if(calls>=48)break;
    if(!arena.canObserve()){memoryStop=true;break}
    const n=root.nodes[ch];calls++;prefix++;ok(verify(n.cert)==="valid"&&checkCert(n.cert),"certificate");
    arena.observe(ch,n.a,n.c);bank.push({id:ch,p:null,z:null,version:-1});trace.push(["edge",id,ch]);
   }
  }
  transient=Math.max(transient,bank.length);ok(transient<=cap+2,"bank reserve");
  if(memoryStop)break;
  if(bank.length){
   const before=bank.slice(),next=schedule(arena,bank,method,F,cap);
   if(audit&&method!=="depth"&&limit===Infinity){
    const o=oracleRank(arena,before,F,cap),base=before.slice().sort((a,b)=>cmp(a,b,depthScore)).slice(0,cap);
    ok(sameChoice(next,o.order),"dense oracle decision mismatch");
    aud.states++;aud.topChanged+=Number(next[0].id!==base[0].id);aud.setChanged+=Number(next.map(x=>x.id).sort((a,b)=>a-b).join(",")!==base.map(x=>x.id).sort((a,b)=>a-b).join(","));
    for(const x of before)if(x.version===arena.version){const err=Math.abs(x.p-o.scores.get(x.id));ok(err<1e-10,"dense score");aud.scoreChecks++;aud.maxError=Math.max(aud.maxError,err)}
   }
   bank=next;peakBank=Math.max(peakBank,bank.length);decisions.push([bank[0].id,bank.map(x=>x.id).sort((a,b)=>a-b)]);
  }
 }
 const seen=new Set([0]),probed=new Set();let hit=false;
 for(const t of trace){
  ok(!hit,"event after success");
  if(t[0]==="edge"){const [,p,id]=t;ok(seen.has(p)&&par(id)===p&&!seen.has(id)&&checkCert(root.nodes[id].cert),"edge replay");seen.add(id)}
  else{const [,id,s]=t;ok(seen.has(id)&&!probed.has(id)&&depth(id)===root.L,"probe replay");probed.add(id);hit=terminal(root,id);ok(hit===s,"outcome replay")}
 }
 ok(hit===success&&trace.length===calls&&calls===prefix+probes&&calls<=48&&peakBank<=cap&&arena.stats.peakSlots<=B&&arena.stats.transports<=limit,"accounting");
 return {success,calls,prefix,probes,memoryStop,peakBank,transient,trace,decisions,stats:{...arena.stats},aud};
}
function experimentA(){
 const rows=[],paired=[],audit={states:0,scoreChecks:0,maxError:0,topChanged:0,setChanged:0,traceComparisons:0},totals={episodes:0,calls:0};
 for(const regime of ["correlated","independent"]){
  const roots=Array.from({length:192},(_,i)=>tree(1640001+i,regime));
  for(const B of [256,512])for(const cap of [2,4,8]){
   const groups=[{limit:Infinity,engines:["path","batch","lazy",...(cap===2?[]:["marginal","depth"])]}];
   if(B===256&&cap===4)groups.push({limit:256,engines:["path","batch","lazy"]});
   for(const {limit,engines} of groups){
    const all={};
    for(const engine of engines){
     const rs=roots.map((root,i)=>run(root,B,cap,engine,limit,i<16&&B===512&&cap===4));
     all[engine]=rs;totals.episodes+=rs.length;totals.calls+=sum(rs.map(r=>r.calls));
     for(const r of rs){for(const k of ["states","scoreChecks","topChanged","setChanged"])audit[k]+=r.aud[k];audit.maxError=Math.max(audit.maxError,r.aud.maxError)}
     const s=k=>sum(rs.map(r=>r[k])),stat=k=>sum(rs.map(r=>r.stats[k])),peak=k=>Math.max(...rs.map(r=>r.stats[k]));
     rows.push({regime,B,cap,limit:Number.isFinite(limit)?limit:null,engine,roots:rs.length,solved:rs.filter(r=>r.success).length,meanCalls:s("calls")/rs.length,prefix:s("prefix"),probes:s("probes"),memoryStops:rs.filter(r=>r.memoryStop).length,peakBank:Math.max(...rs.map(r=>r.peakBank)),peakSlots:peak("peakSlots"),peakCacheVectors:peak("peakCacheVectors"),scratchSlotsUpper:peak("scratchSlotsUpper"),transports:stat("transports"),up:stat("up"),down:stat("down"),queries:stat("queries"),hits:stat("hits"),misses:stat("misses"),evictions:stat("evictions"),invalidations:stat("invalidations"),skips:stat("skips"),schedules:stat("schedules"),reused:stat("reused"),refined:stat("refined"),certified:stat("certified"),fallbackRounds:stat("fallbackRounds")});
    }
    if(limit===Infinity)for(const engine of ["batch","lazy"])for(let i=0;i<roots.length;i++){
     const a=all.path[i],b=all[engine][i];
     ok(JSON.stringify(a.trace)===JSON.stringify(b.trace)&&JSON.stringify(a.decisions)===JSON.stringify(b.decisions)&&a.memoryStop===b.memoryStop,"exact trace mismatch");
     audit.traceComparisons++;
    }
    for(const ref of engines.filter(x=>x!=="lazy"))paired.push({regime,B,cap,limit:Number.isFinite(limit)?limit:null,engine:"lazy",ref,...exactPaired(all.lazy,all[ref])});
   }
  }
 }
 return {rows,paired,audit,totals,sharedForecastSlots:sum([...FORECAST.values()].map(f=>D*f.length)),falseAccepts:0};
}

// Small adaptive information-acquisition problem. Beliefs are integer weights;
// conditioning on a noisy sensor multiplies by integer likelihoods.
function gcd(a,b){while(b){[a,b]=[b,a%b]}return a}
function normalizeWeights(w){const g=w.reduce(gcd,0);return g?w.map(x=>x/g):w}
function decisionRoot(seed){const r=rng(seed);return {seed,prior:Array.from({length:2},()=>Array.from({length:D},()=>1+Math.floor(r()*12))),accuracy:Array.from({length:2},()=>[60,80,100][Math.floor(r()*3)])}}
function state0(root){return {expanded:[0,0],w:root.prior.map(w=>w.slice())}}
function stateKey(s,b){return [b,...s.expanded,...s.w.flat()].join(",")}
function legal(s,b){
 const a=[];
 for(let i=0;i<2;i++){
  if(!s.expanded[i]){if(b>1)a.push(i)}
  else for(let j=0;j<3;j++)if(s.w[i][j]>0)a.push(2+3*i+j);
 }return a;
}
function unpack(a){return a<2?{branch:a,expand:true}:{branch:Math.floor((a-2)/3),probe:(a-2)%3,expand:false}}
function branches(root,s,a){
 const {branch:i,expand,probe:j}=unpack(a),w=s.w[i],z=sum(w);
 function next(wi,expandFlag){return {expanded:s.expanded.map((v,k)=>k===i?expandFlag:v),w:s.w.map((v,k)=>k===i?normalizeWeights(wi):v)}}
 if(expand){
  return [0,1].map(bit=>{
   const v=w.map((x,k)=>x*(k%2===bit?root.accuracy[i]:100-root.accuracy[i]));
   return {prob:sum(v)/(100*z),state:next(v,1),success:false};
  }).filter(o=>o.prob>0);
 }
 const p=w[j]/z,v=w.slice();v[j]=0;
 const out=[{prob:p,success:true}];if(p<1)out.push({prob:1-p,success:false,state:next(v,1)});return out;
}
function marginal(s,a,original=null){
 const {branch:i,expand,probe:j}=unpack(a),w=original?original[i]:s.w[i],z=sum(w);
 return expand?Math.max(...w.slice(0,3))/z:w[j]/z;
}
function chooseHeuristic(root,s,b,kind){
 const as=legal(s,b);if(!as.length)return null;
 const probes=as.filter(a=>a>=2);
 if(kind==="depth")return Math.max(...(probes.length?probes:as));
 if(kind==="marginal"||kind==="noFeedback"){
  const xs=probes.length?probes:as;return xs.sort((a,b)=>marginal(s,b,kind==="noFeedback"?root.prior:null)-marginal(s,a,kind==="noFeedback"?root.prior:null)||b-a)[0];
 }
 const score=a=>{
  if(a>=2)return marginal(s,a);
  return sum(branches(root,s,a).map(o=>o.prob*marginal(o.state,a)));
 };
 return as.sort((a,b)=>score(b)-score(a)||b-a)[0];
}
function solveDecision(root,kind){
 const memo=new Map(),stats={states:0,transitions:0,expandWithProbe:0};
 function rec(s,b){
  if(b<=0)return {value:0,action:null};
  const key=stateKey(s,b);if(memo.has(key))return memo.get(key);
  const as=kind==="optimal"?legal(s,b):[chooseHeuristic(root,s,b,kind)].filter(a=>a!==null);
  let best={value:0,action:null};
  for(const a of as){
   const outcomes=branches(root,s,a);ok(Math.abs(sum(outcomes.map(o=>o.prob))-1)<1e-10,"decision transition");
   stats.transitions+=outcomes.length;
   const v=sum(outcomes.map(o=>o.prob*(o.success?1:rec(o.state,b-1).value)));
   if(best.action===null||v>best.value+1e-14||(Math.abs(v-best.value)<=1e-14&&a>best.action))best={value:v,action:a};
  }
  stats.states++;stats.expandWithProbe+=Number(best.action!==null&&best.action<2&&legal(s,b).some(a=>a>=2));
  memo.set(key,best);return best;
 }
 return {rec,stats};
}
// Independent forward evaluation of optimal decision policy by enumerating all
// 36 latent worlds and both sensor branches; conditional probability never uses
// a hidden value in selecting an action.
function forwardDecision(root,policy,b){
 let total=0,worlds=0;
 for(let x=0;x<D;x++)for(let y=0;y<D;y++){
  const h=[x,y],prior=root.prior[0][x]/sum(root.prior[0])*root.prior[1][y]/sum(root.prior[1]);
  if(!prior)continue;worlds++;
  function go(s,k){
   if(!k)return 0;const a=policy.rec(s,k).action;if(a===null)return 0;
   const z=unpack(a),i=z.branch;
   if(!z.expand){if(h[i]===z.probe)return 1;const fail=branches(root,s,a).find(o=>!o.success);return fail?go(fail.state,k-1):0}
   let v=0;
   // reconstruct sensor likelihood independently of branches() ordering.
   for(const bit of [0,1]){
    const p=(h[i]%2===bit?root.accuracy[i]:100-root.accuracy[i])/100;if(!p)continue;
    const w=s.w[i].map((x,j)=>x*(j%2===bit?root.accuracy[i]:100-root.accuracy[i]));
    const ns={expanded:s.expanded.map((v,j)=>j===i?1:v),w:s.w.map((v,j)=>j===i?normalizeWeights(w):v)};
    v+=p*go(ns,k-1);
   }return v;
  }
  total+=prior*go(state0(root),b);
 }
 return {total,worlds};
}
function experimentB(){
 const hand={seed:0,prior:[[1,1,0,0,0,0],[1,1,0,0,0,0]],accuracy:[100,100]},h=solveDecision(hand,"optimal");
 ok(h.rec(state0(hand),1).value===0&&Math.abs(h.rec(state0(hand),2).value-1)<1e-12,"perfect sensor fixture");
 const uniform={seed:1,prior:[one(),one()],accuracy:[100,100]},u=solveDecision(uniform,"optimal");
 ok(Math.abs(u.rec(state0(uniform),2).value-1/3)<1e-12,"uniform fixture");
 const roots=Array.from({length:192},(_,i)=>decisionRoot(1650001+i)),kinds=["depth","noFeedback","marginal","sensor","optimal"];
 const aggregate=Object.fromEntries([2,3,4,5].map(b=>[b,Object.fromEntries(kinds.map(k=>[k,{value:0,regret:0,firstDifferent:0}]))]));
 const stats=Object.fromEntries(kinds.map(k=>[k,{states:0,transitions:0,expandWithProbe:0}]));
 let independentWorlds=0,independentChecks=0,maxError=0,monotonic=0;
 for(let i=0;i<roots.length;i++){
  const root=roots[i],pol=Object.fromEntries(kinds.map(k=>[k,solveDecision(root,k)])),s=state0(root);let prev=0;
  for(const b of [2,3,4,5]){
   const opt=pol.optimal.rec(s,b);ok(opt.value>=prev-1e-12,"optimal monotonicity");prev=opt.value;monotonic++;
   for(const k of kinds){const v=pol[k].rec(s,b);ok(v.value<=opt.value+1e-10,"optimal dominates");
    const a=aggregate[b][k];a.value+=v.value;a.regret+=opt.value-v.value;a.firstDifferent+=Number(v.action!==opt.action);
   }
   if(i<12){const f=forwardDecision(root,pol.optimal,b);const err=Math.abs(f.total-opt.value);ok(err<1e-10,"independent world evaluation");maxError=Math.max(maxError,err);independentChecks++;independentWorlds+=f.worlds}
  }
  for(const k of kinds)for(const key of Object.keys(stats[k]))stats[k][key]+=pol[k].stats[key];
 }
 const rows=[];for(const [budget,values] of Object.entries(aggregate))for(const [kind,a] of Object.entries(values))rows.push({budget:Number(budget),kind,roots:roots.length,expectedSuccess:a.value/roots.length,meanRegret:a.regret/roots.length,firstDifferent:a.firstDifferent});
 return {rows,stats,handChecks:2,monotonic,independentChecks,independentWorlds,maxError};
}
function experiment10(){
 const start=Date.now(),arena=experimentA(),decision=experimentB();
 return {status:"PASS",scope:"logical persistent arena and synthetic adaptive information oracle",arena,decision,elapsedMs:Date.now()-start};
}
export {tree,run,experiment10};
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href) console.log(JSON.stringify(experiment10(),null,2));
