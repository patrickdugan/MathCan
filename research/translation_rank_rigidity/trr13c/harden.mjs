// Read the original unmodified verifier and produce a guarded copy.
import fs from 'node:fs';
import crypto from 'node:crypto';
const source=fs.readFileSync(new URL('./verify.js',import.meta.url),'utf8');
if(crypto.createHash('sha256').update(source).digest('hex')!=='1edae6f84507afa571dbb617fca68eb1a993e659a95412dad7c631290caaf109') throw Error('original source hash');
function replaceOnce(s,a,b){if(s.split(a).length!==2)throw Error('unexpected patch context: '+a);return s.replace(a,b)}
let s=source;
s=replaceOnce(s,'  for (let trial = 0; trial < 1e6; trial++) {','  let constructed = false;\n  for (let trial = 0; trial < 1e6; trial++) {');
s=replaceOnce(s,'    log[0] = -1;\n    break;','    log[0] = -1;\n    constructed = true;\n    break;');
s=replaceOnce(s,'  const sub = (p === 2) ?','  if (!constructed) throw new Error("field construction exhausted");\n  const sub = (p === 2) ?');
s=replaceOnce(s,'const F = makeField(p, d), C = new Uint16Array(Q);','const F = makeField(p, d), C = new Uint32Array(Q);');
s=replaceOnce(s,'while (m * (m - 1) / 2 < run) m++;','while (m * (m - 1) / 2 < run) m++;\n       if (run && m * (m - 1) / 2 !== run) throw new Error("nontriangular pair count");');
fs.writeFileSync(process.argv[2],s);
