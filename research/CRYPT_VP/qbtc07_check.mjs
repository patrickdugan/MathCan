// QBTC-07: finite target-before-key and keyed tree controls; intentionally insecure hashes.
function qbtc07(){
 const ck=(x,m)=>{if(!x)throw Error(m)};
 const gcd=(a,b)=>b===0n?a:gcd(b,a%b);
 const frac=(a,b)=>{const g=gcd(a,b);return [String(a/g),String(b/g)]};
 const grinding=[];
 // Key picks one exceptional pair; maps both to smaller endpoint, leaves others distinct.
 // Deliberately non-compressing public finite example, not an assumed secure primitive.
 for(const N of [8,16,32,64]){
  const keys=[];for(let a=0;a<N;a++)for(let b=a+1;b<N;b++)keys.push([a,b]);
  const hash=([a,b],x)=>x===b?a:x;
  let max=0;
  for(let x=0;x<N;x++){
   let win=0;
   for(const k of keys){
    const coll=Array.from({length:N},(_,i)=>i).some(y=>y!==x&&hash(k,y)===hash(k,x));
    if(coll)win++;
   }
   ck(win===N-1,"fixed target census");max=Math.max(max,win);
  }
  ck(keys.every(k=>hash(k,k[0])===hash(k,k[1])),"post-key adaptive target");
  for(const g of [1,2,4,8,16]){
   const d=BigInt(keys.length),a=BigInt(max),den=d**BigInt(g),num=den-(d-a)**BigInt(g);
   ck(num<=BigInt(g)*a*d**BigInt(g-1),"grinding union bound");
   grinding.push({N,g,keys:keys.length,one:frac(a,d),grind:frac(num,den),adaptive:["1","1"],display:Number(num)/Number(den)});
  }
 }
 // Intentionally insecure 4-input -> 2-output compression family. 16 keys enumerate all functions.
 const H=(key,a,b)=>(key>>(a*4+b*2))&1;
 // Inputs are bit tuples; fixed 4 leaves, both levels independently keyed.
 function tree(bits,keys){
  const [k1,k2]=keys;
  const ch=[H(k1,bits[0],bits[1]),H(k1,bits[2],bits[3])];
  return {ch,root:H(k2,...ch)};
 }
 function extract(x,y,keys){
  const a=tree(x,keys),b=tree(y,keys);
  if(a.root!==b.root||x.every((v,i)=>v===y[i]))return null;
  if(a.ch.some((v,i)=>v!==b.ch[i]))return {level:2,node:0,k:keys[1],target:a.ch,alternate:b.ch};
  for(let i=0;i<2;i++){
   const u=x.slice(2*i,2*i+2),v=y.slice(2*i,2*i+2);
   if(u.some((z,j)=>z!==v[j]))return {level:1,node:i,k:keys[0],target:u,alternate:v};
  }
  throw Error("missing collision");
 }
 const batches=Array.from({length:16},(_,x)=>Array.from({length:4},(_,i)=>(x>>i)&1));
 let pairs=0,alternate=0,rootCollision=0,extracted=[0,0],honest=0,pathAccept=0,pathReject=0,pathLeafForge=0;
 function open(bits,keys,i){
  const ch=tree(bits,keys).ch;
  return [bits[i^1],ch[(i>>1)^1]];
 }
 function verify(value,i,path,keys,root){
  if(!Number.isInteger(i)||i<0||i>=4||!Array.isArray(path)||path.length!==2||![value,...path].every(x=>x===0||x===1))return false;
  const h=i&1?H(keys[0],path[0],value):H(keys[0],value,path[0]);
  const p=i&2?H(keys[1],path[1],h):H(keys[1],h,path[1]);
  return p===root;
 }
 // Extract target collision from a changed leaf and arbitrary accepted path, comparing
 // to honest path, with a top-down first difference (root first).
 function pathExtract(x,keys,i,value,path){
  const a=tree(x,keys),old=open(x,keys,i),b=i&1?H(keys[0],path[0],value):H(keys[0],value,path[0]);
  const rootAlt=i&2?[path[1],b]:[b,path[1]];
  if(rootAlt.some((z,j)=>z!==a.ch[j]))return {level:2,k:keys[1],target:a.ch,alternate:rootAlt};
  const childAlt=i&1?[path[0],value]:[value,path[0]];
  return {level:1,k:keys[0],target:x.slice(i&2,(i&2)+2),alternate:childAlt};
 }
 const isCollision=e=>e&&e.target.some((z,j)=>z!==e.alternate[j])&&H(e.k,...e.target)===H(e.k,...e.alternate);
 for(let a=0;a<16;a++)for(let b=0;b<16;b++){
  const keys=[a,b];
  for(const x of batches){
   const root=tree(x,keys).root;
   for(const y of batches){
    pairs++;if(x===y)continue;alternate++;
    const e=extract(x,y,keys);
    if(root===tree(y,keys).root){ck(isCollision(e),"full-batch target collision");rootCollision++;extracted[e.level-1]++}
    else ck(e===null,"distinct root");
   }
   for(let i=0;i<4;i++){
    ck(verify(x[i],i,open(x,keys,i),keys,root),"honest proof");honest++;
    for(let v=0;v<2;v++)for(let j=0;j<4;j++){
     const path=[j&1,j>>1];
     if(verify(v,i,path,keys,root)){pathAccept++;if(v!==x[i]){ck(isCollision(pathExtract(x,keys,i,v,path)),"path target collision");pathLeafForge++}}
     else pathReject++;
    }
   }
  }
 }
 ck(pairs===65536&&alternate===61440&&honest===16384&&pathAccept+pathReject===131072&&extracted.reduce((x,y)=>x+y,0)===rootCollision,"tree census");
 // Explicit state machine: raw batch and context frozen before external fresh key draws.
 // Registry is a modeled authenticated finality service; it is not supplied by the hash.
 let state="open",target=null,keys=[],record=null;let tests=[];
 const test=(name,v)=>{ck(v,name);tests.push(name)};
 const encode=x=>JSON.stringify(x);
 const freeze=(ctx,leaf)=>{if(state!=="open"||leaf.length!==4||!leaf.every(v=>v===0||v===1))return false;target=JSON.parse(encode({ctx,leaf}));state="frozen";return true};
 const draw=k=>{if(!Number.isInteger(k)||k<0||k>=16)return false;if(state==="frozen"){keys=[k];state="level1";return true}if(state==="level1"){keys.push(k);state="sealed";record=JSON.parse(encode({ctx:target.ctx,keys,root:tree(target.leaf,keys).root}));return true}return false};
 const authenticated=r=>state==="sealed"&&encode(r)===encode(record);
 const ctx=["network-A",7,"finality-A",4];
 test("key before freeze rejected",!draw(0));
 test("freeze full batch",freeze(ctx,[1,0,1,1]));
 test("target replacement rejected",!freeze(ctx,[0,0,1,1]));
 test("first fresh level key",draw(6)&&state==="level1");
 test("checkpoint unpublished after one key",record===null);
 test("second fresh level key",draw(9)&&state==="sealed");
 test("key grinding replacement rejected",!draw(1));
 test("registry accepts pinned manifest",authenticated(record));
 test("network replay rejected",!authenticated({...record,ctx:["network-B",7,"finality-A",4]}));
 test("fork replay rejected for distinct finality context",!authenticated({...record,ctx:["network-A",7,"finality-B",4]}));
 test("key substitution rejected",!authenticated({...record,keys:[7,9]}));
 test("identical checkpoint replay allowed",authenticated(JSON.parse(encode(record))));
 test("malformed proof rejected",!verify(1,4,[1,1],keys,record.root)&&!verify(1,0,[1],keys,record.root));
 return {schema:"qbtc-07-v1",grinding,tree:{pairs,alternate,rootCollision,extracted,honest,pathAccept,pathReject,pathLeafForge},ledger:tests};
}
console.log(JSON.stringify(qbtc07(),null,2));
