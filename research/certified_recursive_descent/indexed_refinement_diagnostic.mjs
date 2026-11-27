// Post-campaign deterministic unit diagnostic. No policy changes.
import {rng} from "./search.mjs";
import {ok} from "./information_gain.mjs";
import {STOP} from "./metered_refinement.mjs";
import {Memo21,Arena21,Heap21,meter21} from "./indexed_refinement.mjs";
function diagnostic21(){
 let heapChecks=0,pops=0,arenaChecks=0,memoChecks=0,abortChecks=0;
 const M=meter21(Infinity),r=rng(2750001);
 for(const cap of [32,96]){
  for(let trial=0;trial<24;trial++){
   const A=new Arena21(M,cap),H=new Heap21(A,M,cap);ok(A.admit(cap)===0,"full arena");
   ok(A.admit(1)===-1&&A.n===cap,"arena denial");arenaChecks+=2;
   ok(A.a.byteLength===cap*64&&H.buf.byteLength===cap*4,"typed payload");arenaChecks++;
   const ids=Array.from({length:cap},(_,i)=>i);
   for(const i of ids){A.set(i,6,Math.floor(r()*8));H.push(i);for(let j=1;j<H.n;j++){const p=(j-1)>>1;ok(!H.higher(H.buf[j],H.buf[p]),"heap order");heapChecks++}}
   const expected=ids.sort((a,b)=>A.get(b,6)-A.get(a,6)||a-b);
   for(const i of expected){ok(H.pop()===i,"pop order");pops++;for(let j=1;j<H.n;j++){const p=(j-1)>>1;ok(!H.higher(H.buf[j],H.buf[p]),"heap order after pop");heapChecks++}}
  }
 }
 const B=meter21(Infinity),memo=new Memo21(B,128),m=memo.map("L:"),h=memo.map("H:");
 for(let i=0;i<384;i++){
  const map=i%2===0?m:h;map.set(String(i),i+.25);memoChecks++;
  for(let j=Math.max(0,i-127);j<=i;j++){const x=j%2===0?m:h;ok(x.has(String(j))&&x.get(String(j))===j+.25,"FIFO live value");memoChecks++}
  if(i>=128){const j=i-128,x=j%2===0?m:h;ok(!x.has(String(j)),"FIFO eviction");memoChecks++}
 }
 ok(B.c.memoEvictions===256&&memo.v.byteLength===1024&&memo.index.size===128,"memo bound");
 const C=meter21(1),small=new Memo21(C,1),q=small.map("L:");
 q.set("first",7);try{q.set("second",8);throw Error("expected abort")}catch(e){if(e!==STOP)throw e}
 ok(q.has("first")&&q.get("first")===7&&!q.has("second")&&C.used===1,"atomic memo abort");abortChecks++;
 const D=meter21(1),a=new Arena21(D,32);try{a.admit(2);throw Error("expected abort")}catch(e){if(e!==STOP)throw e}
 ok(a.n===0&&D.used===0,"atomic arena abort");abortChecks++;
 return {status:"PASS",scope:"post-campaign unit diagnostic; separate from frozen policy cohorts",heapChecks,pops,arenaChecks,memoChecks,memoEvictions:B.c.memoEvictions,abortChecks,typedBytes:{arena96:6144,arena32:2048,heap96:384,heap32:128,memo:1024}}
}
console.log(JSON.stringify(diagnostic21(),null,2));
