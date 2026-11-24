// QBTC-01: finite authorization and phase-ensemble games; no cryptographic implementation.
function qbtc(){
 const check=(p,m)=>{if(!p)throw Error(m)};
 const receipt={schema:"qbtc-01-v1",checks:[],prefix:[],discrimination:[]};
 const test=(name,p)=>{check(p,name);receipt.checks.push(name)};
 const fields=["domain","network","outpoint","key","sighash","digest"];
 function message(m){
   check(Object.keys(m).length===fields.length && fields.every(f=>Object.hasOwn(m,f)&&typeof m[f]==="string"&&m[f].length>0),"invalid message");
   return JSON.stringify(["QBTC-01/v1",...fields.map(f=>m[f])]);
 }
 const tx={domain:"QBTC-01/spend",network:"regtest-A",outpoint:"toy:0",key:"key-A",sighash:"ALL",digest:"pay:alice:7"};
 const tx2={...tx,digest:"pay:bob:7"};
 const tx3={...tx,outpoint:"toy:1"};
 const variants=fields.map(f=>({...tx,[f]:tx[f]+"!"}));
 const msgs=[tx,tx2,tx3,...variants].map(message);
 test("canonical field order",message(tx)===message(Object.fromEntries(Object.entries(tx).reverse())));
 test("all context fields bound",new Set(msgs).size===msgs.length);
 let rejected=0;for(const m of [{...tx,extra:"x"},{...tx,digest:""},{...tx,sighash:null}]){try{message(m)}catch{rejected++}}test("malformed messages rejected",rejected===3);
 // A PUBLIC finite relation: this is a toy verifier, not a signature primitive.
 // Signing resource is an ideal counter; the public verifier remains usable after exhaustion.
 const table=new Map(msgs.map((m,i)=>[m,new Set([((37*i+11)%256).toString(2).padStart(8,"0")])]));
 const V=(m,s)=>typeof s==="string"&&s.length===8&&table.get(m)?.has(s)===true;
 let remaining=2;const signed=new Set();
 function sign(m){if(remaining===0||!table.has(m))return null;remaining--;signed.add(m);return [...table.get(m)][0]}
 const t=message(tx),t2=message(tx2),t3=message(tx3);
 const sig=sign(t);
 test("honest evidence validates",V(t,sig));
 test("repeat signing consumes resource",sign(t)===sig&&remaining===0);
 test("exhaustion is signing-side only",sign(t2)===null&&V(t,sig));
 test("all field substitutions rejected",variants.every(m=>!V(message(m),sig)));
 test("fresh transaction substitution rejected",!V(t2,sig));
 function ledger(){const utxo=new Map([[tx.outpoint,tx.key],[tx3.outpoint,tx3.key]]);
   return {accept(m,s){if(m.network!==tx.network||m.domain!==tx.domain||m.sighash!=="ALL"||utxo.get(m.outpoint)!==m.key||!V(message(m),s))return false;utxo.delete(m.outpoint);return true},unspent:()=>[...utxo.keys()]}}
 const l=ledger();
 test("wrong network rejected before spend",!l.accept({...tx,network:"regtest-B"},sig));
 test("spend accepted deterministically",l.accept(tx,sig));
 test("same-ledger replay rejected",!l.accept(tx,sig));
 test("same-network fork permits replay",ledger().accept(tx,sig));
 test("independent validators agree",ledger().accept(tx,sig)===ledger().accept(tx,sig));
 // Generic prefix search: oracle tests existence of a fixed-length accepted witness
 function recover(m,L,exists){let queries=1,p="";if(!exists(m,p,L))return {witness:null,queries};for(let i=0;i<L;i++){queries++;p+=exists(m,p+"0",L)?"0":"1"}return {witness:p,queries}}
 function toyExists(m,p,L){return [...(table.get(m)||[])].some(s=>s.length===L&&s.startsWith(p))}
 const forged=recover(t2,8,toyExists);
 test("fresh-message forgery with existence oracle",V(t2,forged.witness)&&!signed.has(t2)&&forged.queries<=9);
 test("conflicting spend rejected after first spend",!l.accept(tx2,forged.witness));
 const next=recover(t3,8,toyExists);
 test("fresh outpoint forgery after signer exhaustion",V(t3,next.witness)&&!signed.has(t3)&&l.accept(tx3,next.witness));
 test("unsatisfiable message detected",recover("unknown",8,toyExists).witness===null);
 // Exhaustive prefix self-test over every singleton 8-bit relation plus sparse multivalued relations.
 for(let i=0;i<256;i++){
   const witness=i.toString(2).padStart(8,"0");
   const out=recover("m",8,(_,p)=>witness.startsWith(p));
   check(out.witness===witness&&out.queries===9,"prefix singleton");
 }
 for(let i=0;i<32;i++){
   const ss=[i,255-i,(i*7)%256].map(x=>x.toString(2).padStart(8,"0")).sort();
   const out=recover("m",8,(_,p)=>ss.some(s=>s.startsWith(p)));
   check(out.witness===ss[0]&&out.queries===9,"prefix multivalued");
 }
 receipt.prefix={singletonCases:256,multivaluedCases:32,queriesPerSatisfiable8bitInstance:9,forgedFreshMessage:true};
 // Orthogonal phase families: full Hadamard basis of m labels. The state label is
 // either X itself (all frequencies) or the first row of X (common-row frequencies).
 // In either case a uniform secret X hides a single shifted state in the maximally mixed ensemble.
 // With a reference the two labels reveal the projected A. Compute exact integer TV.
 function rank(a,n){let S=new Set([0]);for(let i=0;i<n;i++){const row=(a>>(i*n))&((1<<n)-1);for(const s of [...S])S.add(s^row)}return Math.log2(S.size)}
 function tv(a,b){const sa=a.reduce((x,y)=>x+y,0),sb=b.reduce((x,y)=>x+y,0);let numerator=a.reduce((s,x,i)=>s+Math.abs(x*sb-b[i]*sa),0);let denominator=2*sa*sb;const gcd=(x,y)=>y?gcd(y,x%y):x;const g=gcd(numerator,denominator);return [numerator/g,denominator/g]}
 for(let n=2;n<=3;n++){
  const N=1<<(n*n),q=1<<n,all=Array.from({length:N},(_,x)=>x),rs=all.map(x=>rank(x,n)),S=[all.filter(x=>rs[x]===1),all.filter(x=>rs[x]===n)];
  for(const family of ["full-orthogonal","common-row-orthogonal"]){
   const label=x=>family==="full-orthogonal"?x:x&(q-1);
   const d=family==="full-orthogonal"?N:q;
   const distributions=S.map(A=>{const shift=Array(d).fill(0),single=Array(d).fill(0);for(const a of A){shift[label(a)]++;for(const x of all)single[label(x^a)]++}return {shift,single,energy:[2*(A.length-shift[0]),A.length]}});
   const single=tv(distributions[0].single,distributions[1].single),pair=tv(distributions[0].shift,distributions[1].shift);
   const [[e1,d1],[en,dn]]=distributions.map(x=>x.energy);
   check(single[0]===0,"hidden single ensemble identical");
   check(en*d1*q<=2*(q-1)*e1*dn,"observer bound");
   if(family==="full-orthogonal"){check(pair[0]===pair[1]&&en*d1===e1*dn,"orthogonal counterexample")}
   else {check(pair[0]*(q-1)===pair[1]*(q/2-1),"row projection TV");check(en*d1*q===2*(q-1)*e1*dn,"row saturation")}
   receipt.discrimination.push({n,family,hiddenSingleTV:single,referencePairTV:pair,hsRatio:[en*d1,e1*dn],perfectLabelRecovery:true});
  }
 }
 test("four exact hidden-ensemble controls",receipt.discrimination.length===4);
 test("fresh message existence oracle defeats ideal resource counter",remaining===0&&forged.witness!==null);
 check(receipt.checks.length===19,"frozen checks count");
 return receipt
}
console.log(JSON.stringify(qbtc(),null,2));
