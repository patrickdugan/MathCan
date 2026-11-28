// ACE-03V: replay each proof family in a separate bounded-heap process.
// Compare complete receipts and record their current static import closure.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root=new URL('./',import.meta.url),repo=new URL('../../',root);
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const insist=(condition,message)=>{if(!condition)throw Error(message);};
const names=['instruction_tags','instruction_witnesses','instruction_decoding','syntax_decoration'];
const receipts={},receiptHashes={},sources=new Map();

for(const name of names) {
  const result=spawnSync(process.execPath,
    ['--max-old-space-size=3072',fileURLToPath(new URL(`${name}_replay.mjs`,root))],
    {encoding:'utf8',timeout:300000,maxBuffer:4*1024*1024});
  insist(!result.error&&result.status===0,
    `${name} replay failed: ${result.error?.message||result.stderr||result.status}`);
  const expected=readFileSync(new URL(`${name}_receipt.json`,root),'utf8');
  insist(result.stdout===expected,`${name} receipt differs`);
  const r=JSON.parse(expected);
  insist(r.pinned_L_unchanged===true,'pinned L changed');
  insist(r.checked_modules===r.checks.length,'module accounting');
  insist(r.kernel_visits===r.checks.reduce((n,c)=>n+c.nodes,0),'visit accounting');
  insist(r.independent_exact_goals===r.checked_modules,'missing independent target');
  insist(r.negative_controls===r.controls.length,'control accounting');
  insist(r.checks.every(c=>!c.ambient_axioms.includes('choice')),'Choice import');
  receipts[name]=r;receiptHashes[`${name}_receipt.json`]=hash(expected);
}

// Verify the prior checkpoints' source bytes before recording this extension.
const baselines=[['full_replay_provenance.json',repo],['ace03u_receipt.json',root]];
let priorHashes=0;
for(const [name,base] of baselines) {
  const bytes=readFileSync(new URL(name,root),'utf8');
  const manifest=JSON.parse(bytes);
  for(const [file,expected] of Object.entries(manifest.source_files_sha256)) {
    insist(hash(readFileSync(new URL(file,base)))===expected,`prior source changed: ${file}`);
    priorHashes++;
  }
  sources.set(name,hash(bytes));
}

function collect(name) {
  insist(/^[A-Za-z0-9_]+\.mjs$/.test(name),`unexpected source path: ${name}`);
  if(sources.has(name))return;
  const source=readFileSync(new URL(name,root),'utf8');
  sources.set(name,hash(source));
  for(const match of source.matchAll(/^\s*import\s+[\s\S]*?\sfrom\s*['"]([^'"]+)['"]/gm)) {
    if(match[1].startsWith('./'))collect(match[1].slice(2));
    else insist(match[1].startsWith('node:'),`unexpected import: ${match[1]}`);
  }
}
collect('ace03v_replay.mjs');
for(const name of names)collect(`${name}_replay.mjs`);
sources.set('L_formula.json',hash(readFileSync(new URL('L_formula.json',root))));

const all=Object.values(receipts),sum=k=>all.reduce((n,r)=>n+(r[k]||0),0);
const reused=sum('reused_helper_checks'),reproved=sum('reproved_existing_statement_checks');
const fresh=all.reduce((n,r)=>n+(r.new_statement_checks??r.checked_modules-(r.reused_helper_checks||0)-(r.reproved_existing_statement_checks||0)),0);
insist(fresh+reused+reproved===sum('checked_modules'),'statement accounting');
console.log(JSON.stringify({
  experiment:'ACE-03V',part:'combined_finite_syntax_decoration_replay',
  exact_receipt_comparisons:names.length,
  checked_modules:sum('checked_modules'),new_statement_checks:fresh,
  reproved_existing_statement_checks:reproved,reused_helper_checks:reused,
  independent_exact_goals:sum('independent_exact_goals'),
  kernel_visits:sum('kernel_visits'),proof_rejection_controls:sum('negative_controls'),
  independent_formula_interfaces:sum('independent_formula_interfaces'),
  logic_only_checks:all.reduce((n,r)=>n+(r.logic_only_checks??r.pure_logic_checks?.length??0),0),
  existing_statement_identity_checks:sum('existing_statement_identity_checks'),
  pinned_def_skeleton_checks:receipts.syntax_decoration.pinned_def_skeleton_checks,
  prior_source_hash_comparisons:priorHashes,
  replay_heap_limit_mib:3072,replay_timeout_seconds:300,
  receipt_sha256:receiptHashes,source_file_count:sources.size,
  source_files_sha256:Object.fromEntries([...sources].sort(([a],[b])=>a<b?-1:a>b?1:0)),
  scope:'all finite decoration proof families with exact pinned definable and Def equivalences; natural-number coding, total execution existence and internal Choice remain open'
},null,2));
