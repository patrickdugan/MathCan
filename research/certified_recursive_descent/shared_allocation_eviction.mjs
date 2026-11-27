// CRD-24E: targeted two-factor change trace, no policy fitting.
import {ok,sum,fixture,Problem} from "./information_gain.mjs";
import {AllocationProblem} from "./global_allocation.mjs";
import {align16} from "./persistent_symmetry.mjs";
import {charges,setup,Planner,key} from "./metered_refinement.mjs";
import {meter24,blank24,Factor24} from "./shared_allocation_factors.mjs";
function eviction24(){
 const modes=["direct","scalar","fold","prefix","tree","tree16"],rows=[],totals={parents:0,queries:0,twoChanges:0,valueChecks:0,coeffChecks:0,maxError:0};
 for(let j=0;j<3;j++){
  const pop=[3,5,7][j],stats=Object.fromEntries(modes.map(k=>[k,{work:0,allocation:0,likelihood:0,storeHits:0,storeEvictions:0,storePeak:0,segmentHits:0,rootHits:0,vectorReads:0,vectorWrites:0}]));
  let parents=0,queries=0,twoChanges=0,valueChecks=0,coeffChecks=0,maxError=0;
  for(let i=0;i<4;i++){
   const root=fixture(3060001+j*100+i,pop,2),P=new Problem(root,2);setup(P);
   const seen=new Set(),ps=[],s=P.initial();
   for(const a of P.legal(s,6))for(const o of P.outcomes(s,a))if(!o.hit){
    for(const b of P.legal(o.s,5))for(const q of P.outcomes(o.s,b))if(!q.hit&&P.active(q.s).length===2&&P.legal(q.s,4).some(a=>a.evict>=0)){
     const k=key(q.s,4);if(!seen.has(k)){seen.add(k);ps.push(q.s)}
    }
   }
   const qs=[];
   for(const s of ps.slice(0,16)){
    parents++;qs.push({s,b:4});
    for(const a of P.legal(s,4))if(a.evict>=0)for(const o of P.outcomes(s,a))if(!o.hit){
     const n=o.s.filter((x,i)=>x!==s[i]).length;ok(n===2&&o.s[a.evict]===-1,"two changed branches");
     twoChanges++;qs.push({s:o.s,b:3})
    }
   }
   queries+=qs.length;
   const R=new AllocationProblem(root,2);setup(R);
   const truth=qs.map(q=>{const s=align16(P,q.s,R);return Array.from({length:q.b+1},(_,t)=>R.alloc(s,t).v)});
   for(const mode of modes){
    const M=meter24(Infinity),G=mode==="direct"?new Planner(P,M,"prophet",null):new Factor24(P,M,mode,6);
    for(let i=0;i<qs.length;i++){
     const q=qs[i],r=G.alloc(q.s,q.b),e=Math.abs(r-truth[i][q.b]);ok(e<1e-10,"eviction trace value");valueChecks++;maxError=Math.max(maxError,e);
     if(G.lastVec)for(let t=0;t<=q.b;t++){const e=Math.abs(1-G.lastVec[t]-truth[i][t]);ok(e<1e-10,"eviction vector coefficient");coeffChecks++;maxError=Math.max(maxError,e)}
    }
    ok(M.used===sum(charges.map(k=>M.c[k])),"eviction ledger");
    const a=stats[mode];a.work+=M.used;
    for(const k of Object.keys(a).filter(k=>k!=="work"))a[k]=k==="storePeak"?Math.max(a[k],M.c[k]):a[k]+M.c[k];
   }
  }
  rows.push({population:pop,roots:4,parents,queries,twoChanges,valueChecks,coeffChecks,maxError,stats});
  for(const k of ["parents","queries","twoChanges","valueChecks","coeffChecks"])totals[k]+={parents,queries,twoChanges,valueChecks,coeffChecks}[k];totals.maxError=Math.max(totals.maxError,maxError);
 }
 return {status:"PASS",scope:"post-main registered two-factor change diagnostic, no policy result",totals,rows};
}
console.log(JSON.stringify(eviction24(),null,2));
