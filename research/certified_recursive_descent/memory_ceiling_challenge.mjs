// CRD-10B: preregistered transport-ceiling challenge, no test tuning.
import {tree,run} from "./memory_budgeted.mjs";
import {ok,exactPaired} from "./learned_frontier.mjs";
function challenge10(){
 const begin=Date.now(),rows=[],paired=[];let episodes=0,calls=0,traceComparisons=0;
 const sum=a=>a.reduce((s,v)=>s+v,0);
 for(const regime of ["correlated","independent"]){
  const roots=Array.from({length:192},(_,i)=>tree(1660001+i,regime));
  for(const limit of [64,128,Infinity]){
   const engines=["path","batch","lazy",...(limit===Infinity?["marginal","depth"]:[])],all={};
   for(const engine of engines){
    const rs=roots.map(root=>run(root,256,8,engine,limit,false));all[engine]=rs;
    episodes+=rs.length;calls+=sum(rs.map(r=>r.calls));
    const stat=k=>sum(rs.map(r=>r.stats[k])),s=k=>sum(rs.map(r=>r[k]));
    rows.push({regime,limit:Number.isFinite(limit)?limit:null,engine,roots:rs.length,solved:rs.filter(r=>r.success).length,meanCalls:s("calls")/rs.length,transports:stat("transports"),queries:stat("queries"),fallbackRounds:stat("fallbackRounds"),fallbackRoots:rs.filter(r=>r.stats.fallbackRounds>0).length,peakSlots:Math.max(...rs.map(r=>r.stats.peakSlots)),memoryStops:rs.filter(r=>r.memoryStop).length});
   }
   if(limit===Infinity)for(const name of ["batch","lazy"])for(let i=0;i<roots.length;i++){
    const a=all.path[i],b=all[name][i];ok(JSON.stringify(a.trace)===JSON.stringify(b.trace)&&JSON.stringify(a.decisions)===JSON.stringify(b.decisions)&&a.memoryStop===b.memoryStop,"unlimited equivalence");traceComparisons++;
   }
   for(const ref of engines.filter(e=>e!=="lazy"))paired.push({regime,limit:Number.isFinite(limit)?limit:null,engine:"lazy",ref,...exactPaired(all.lazy,all[ref])});
  }
 }
 return {status:"PASS",scope:"fresh-root transport-count ceiling, not CPU or RSS budget",rows,paired,episodes,calls,traceComparisons,falseAccepts:0,elapsedMs:Date.now()-begin};
}
console.log(JSON.stringify(challenge10(),null,2));
