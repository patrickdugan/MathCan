import {readFileSync} from "node:fs";
// Restricted standalone, uncompressed, no-$d checker; not a general Metamath implementation.
function verify(db){
 const t=db.replace(/\$\([\s\S]*?\$\)/g," ").trim().split(/\s+/);let i=0;
 const vars=new Set(),cons=new Set(),labels=new Set(),scopes=[[]],rules=new Map(),out=[];
 const active=()=>scopes.flat(),same=(a,b)=>a.join(" ")===b.join(" ");
 const until=end=>{const s=[];while(i<t.length&&t[i]!==end)s.push(t[i++]);if(t[i++]!==end)throw Error("delimiter");return s;};
 const sub=(s,m)=>s.flatMap(x=>m.get(x)??[x]);
 while(i<t.length){const q=t[i++];if(q==="${"){scopes.push([]);continue}if(q==="$}"){if(scopes.length<2)throw Error("scope");scopes.pop();continue}
 if(q==="$c"||q==="$v"){for(const x of until("$.")){if(vars.has(x)||cons.has(x))throw Error("symbol");(q==="$c"?cons:vars).add(x)}continue}
 if(labels.has(q)||vars.has(q)||cons.has(q))throw Error("label");labels.add(q);const op=t[i++];if(!["$f","$e","$a","$p"].includes(op))throw Error("unsupported");
 const s=until(op==="$p"?"$=":"$.");for(const x of s)if(!vars.has(x)&&!cons.has(x))throw Error("symbol");if(op==="$f"||op==="$e"){if(op==="$f"&&(s.length!==2||!cons.has(s[0])||!vars.has(s[1])))throw Error("floating");scopes.at(-1).push({q,op,s});continue}
 const es=active().filter(h=>h.op==="$e"),vs=new Set([...s,...es.flatMap(h=>h.s)].filter(x=>vars.has(x)));
 const fs=active().filter(h=>h.op==="$f"&&vs.has(h.s[1]));if(fs.length!==vs.size)throw Error("floating count");const hy=[...fs,...es];
 if(op==="$p"){const proof=until("$."),stack=[];for(const k of proof){const h=active().find(h=>h.q===k);if(h){stack.push(h.s);continue}
 const rule=rules.get(k);if(!rule||stack.length<rule.hy.length)throw Error("assertion or underflow "+k);
 const args=stack.splice(stack.length-rule.hy.length,rule.hy.length),m=new Map();
 rule.hy.forEach((h,j)=>{if(h.op==="$f"){if(args[j][0]!==h.s[0])throw Error("type");m.set(h.s[1],args[j].slice(1))}else if(!same(sub(h.s,m),args[j]))throw Error("hyp "+k)});
 stack.push(sub(rule.s,m));}if(stack.length!==1||!same(stack[0],s))throw Error("final "+q);out.push({theorem:q,steps:proof.length});}
 rules.set(q,{s,hy});}
 if(scopes.length!==1)throw Error("scope end");return out;
}
console.log(JSON.stringify(verify(readFileSync(process.argv[2] ?? new URL("./spectral_geometry.mm",import.meta.url),"utf8")),null,2));
