// ACE-03X: replay each proof family in a separate bounded process, compare
// complete receipts, and verify the unchanged earlier source/receipt chain.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root=new URL('./',import.meta.url),repo=new URL('../../',root);
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const insist=(condition,message)=>{if(!condition)throw Error(message);};
const historyParts=['range','structure','functional','total','coherence','existence'];
const names=['canonical_description_order','canonical_limit_order','uniform_history_recursion',
  'uniform_history_example','canonical_stage_order','indexed_order_family',
  ...historyParts.map(part=>`constructible_order_history_${part}`),
  'carrier_history_projection','restricted_well_order','constructible_stage_well_order'];
const historyPrefix='constructible_order_history_';
const scripts=Object.fromEntries(names.map(name=>[name,
  name.startsWith(historyPrefix)?'constructible_order_history':
  name==='uniform_history_example'?'uniform_history_recursion':name]));
const args=Object.fromEntries(names.map(name=>[name,
  name.startsWith(historyPrefix)?[`--part=${name.slice(historyPrefix.length)}`]:
  name==='uniform_history_example'?['--example']:[]]));
const timeouts=Object.fromEntries(names.map(name=>[name,
  name.startsWith(historyPrefix)||['carrier_history_projection','constructible_stage_well_order'].includes(name)?1200:
  name==='canonical_stage_order'?600:300]));
const heaps=Object.fromEntries(names.map(name=>[name,
  name.startsWith(historyPrefix)||name==='constructible_stage_well_order'?3000:3072]));
const receipts={},receiptHashes={},sources=new Map(),sourceImports=new Map(),inputs=new Map();
const priorSourceFiles=new Set(),priorReceiptHashes={},priorManifestChecks=[];
let priorSourceComparisons=0,priorReceiptComparisons=0;
const count=(r,key,fallback=0)=>{
  const n=r[key]??fallback;
  insist(Number.isSafeInteger(n)&&n>=0,`invalid ${key}`);return n;
};
function readInput(url,expected) {
  const bytes=readFileSync(url),digest=hash(bytes),key=url.href;
  if(expected!==undefined)insist(digest===expected,`checkpoint bytes changed: ${url.pathname}`);
  if(inputs.has(key))insist(inputs.get(key)===digest,`input changed during snapshot: ${url.pathname}`);
  inputs.set(key,digest);return {bytes,digest};
}

// Check all original modules and the U, V and W source manifests. These
// overlap; the comparison and distinct-file counts are reported separately.
for(const [name,base] of [['full_replay_provenance.json',repo],['ace03u_receipt.json',root],['ace03v_receipt.json',root],['ace03w_receipt.json',root]]) {
  const {bytes,digest}=readInput(new URL(name,root)),manifest=JSON.parse(bytes);
  sources.set(name,digest);
  let sourceChecks=0,receiptChecks=0;
  for(const [file,expected] of Object.entries(manifest.source_files_sha256)) {
    const url=new URL(file,base);readInput(url,expected);priorSourceFiles.add(url.href);
    priorSourceComparisons++;sourceChecks++;
  }
  const priorReceipts=manifest.receipt_sha256?
    Object.entries(manifest.receipt_sha256).map(([file,sha])=>({url:new URL(file,root),sha})):
    Object.values(manifest.runs).map(run=>({url:new URL(run.receipt,repo),sha:run.receipt_sha256}));
  for(const {url,sha} of priorReceipts) {
    readInput(url,sha);priorReceiptHashes[url.pathname.split('/').at(-1)]=sha;
    priorReceiptComparisons++;receiptChecks++;
  }
  priorManifestChecks.push({manifest:name,source_hash_comparisons:sourceChecks,receipt_hash_comparisons:receiptChecks});
}

// Every current dependency uses a static local import-from declaration.
// Snapshot source bytes before execution and check the same bytes afterward.
function collect(name) {
  insist(/^[A-Za-z0-9_]+\.mjs$/.test(name),`unexpected source path: ${name}`);
  if(sources.has(name))return;
  const {bytes,digest}=readInput(new URL(name,root));sources.set(name,digest);
  const dependencies=[];
  for(const match of bytes.toString('utf8').matchAll(/^\s*import\s+[\s\S]*?\sfrom\s*['"]([^'"]+)['"]/gm)) {
    if(match[1].startsWith('./')){dependencies.push(match[1].slice(2));collect(match[1].slice(2));}
    else insist(match[1].startsWith('node:'),`unexpected import: ${match[1]}`);
  }
  sourceImports.set(name,[...new Set(dependencies)].sort());
}
collect('ace03x_replay.mjs');
for(const name of names)collect(`${scripts[name]}_replay.mjs`);
const pinned=readInput(new URL('L_formula.json',root));sources.set('L_formula.json',pinned.digest);
const expectedOutputs={};
for(const name of names) {
  const filename=`${name}_receipt.json`,{bytes,digest}=readInput(new URL(filename,root));
  expectedOutputs[name]=bytes.toString('utf8');receiptHashes[filename]=digest;
}

for(const name of names) {
  const started=Date.now();
  if(process.env.ACE_REPLAY_PROGRESS)console.error(`Checking ${name}`);
  const result=spawnSync(process.execPath,
    [`--max-old-space-size=${heaps[name]}`,'--expose-gc',fileURLToPath(new URL(`${scripts[name]}_replay.mjs`,root)),...args[name]],
    {encoding:'utf8',timeout:timeouts[name]*1000,maxBuffer:4*1024*1024});
  insist(!result.error&&result.status===0,
    `${name} replay failed: ${JSON.stringify({status:result.status,signal:result.signal,
      error:result.error?.message,error_code:result.error?.code,stderr:result.stderr})}`);
  insist(result.stdout===expectedOutputs[name],`${name} receipt differs`);
  const r=JSON.parse(expectedOutputs[name]);
  insist(r.pinned_L_unchanged===true,`${name}: pinned L changed`);
  insist(count(r,'checked_modules')===r.checks.length,`${name}: module accounting`);
  insist(count(r,'kernel_visits')===r.checks.reduce((n,c)=>n+c.nodes,0),`${name}: visit accounting`);
  insist(count(r,'independent_exact_goals')===r.checked_modules,`${name}: missing exact targets`);
  insist(count(r,'negative_controls')===r.controls.length,`${name}: control accounting`);
  insist(r.checks.every(c=>!c.ambient_axioms.includes('choice')),`${name}: Choice import`);
  const reused=count(r,'reused_helper_checks'),reproved=count(r,'reproved_existing_statement_checks');
  const fresh=count(r,'new_statement_checks',r.checked_modules-reused-reproved);
  insist(fresh+reused+reproved===r.checked_modules,`${name}: statement accounting`);
  receipts[name]=r;
  if(process.env.ACE_REPLAY_PROGRESS)console.error(`Passed ${name}: ${r.checked_modules} proofs, ${r.kernel_visits} visits, ${Math.round((Date.now()-started)/1000)} seconds`);
}
for(const [url,expected] of inputs)insist(hash(readFileSync(new URL(url)))===expected,`input changed during replay: ${url}`);

const all=Object.values(receipts),sum=key=>all.reduce((n,r)=>n+count(r,key),0);
const stats=r=>({
  checked_modules:r.checked_modules,
  new_statement_checks:count(r,'new_statement_checks',r.checked_modules-count(r,'reused_helper_checks')-count(r,'reproved_existing_statement_checks')),
  reproved_existing_statement_checks:count(r,'reproved_existing_statement_checks'),reused_helper_checks:count(r,'reused_helper_checks'),
  kernel_visits:r.kernel_visits,rejection_controls:r.negative_controls,
  independent_formula_interfaces:count(r,'independent_formula_interfaces'),
  logic_only_checks:count(r,'logic_only_checks',r.pure_logic_checks?.length??0)
});
const families=Object.fromEntries(names.map(name=>[name,stats(receipts[name])]));
console.log(JSON.stringify({
  experiment:'ACE-03X',part:'unique_successor_limit_and_coherent_order_history_replay',
  exact_receipt_comparisons:names.length,
  checked_modules:sum('checked_modules'),
  new_statement_checks:Object.values(families).reduce((n,r)=>n+r.new_statement_checks,0),
  reproved_existing_statement_checks:sum('reproved_existing_statement_checks'),reused_helper_checks:sum('reused_helper_checks'),
  independent_exact_goals:sum('independent_exact_goals'),kernel_visits:sum('kernel_visits'),
  proof_rejection_controls:sum('negative_controls'),independent_formula_interfaces:sum('independent_formula_interfaces'),
  logic_only_checks:Object.values(families).reduce((n,r)=>n+r.logic_only_checks,0),
  existing_statement_identity_checks:sum('existing_statement_identity_checks'),
  shared_well_order_layout_checks:sum('shared_well_order_layout_checks'),
  syntax_formula_link_checks:sum('syntax_formula_link_checks'),
  independent_product_specification_checks:sum('independent_product_specification_checks'),
  exact_pinned_Def_schema_comparisons:sum('exact_pinned_Def_schema_comparisons'),
  exact_pinned_L_schema_comparisons:sum('exact_pinned_L_schema_comparisons'),
  choice_axiom_imported:false,
  family_totals:families,
  prior_manifest_checks:priorManifestChecks,
  prior_source_hash_comparisons:priorSourceComparisons,prior_distinct_source_files:priorSourceFiles.size,
  prior_receipt_hash_comparisons:priorReceiptComparisons,prior_receipt_sha256:priorReceiptHashes,
  input_stability_hash_checks:inputs.size,expose_gc_for_phase_boundaries:true,replay_heap_limit_mib_by_part:heaps,replay_timeout_seconds:timeouts,
  receipt_sha256:receiptHashes,source_file_count:sources.size,
  source_files_sha256:Object.fromEntries([...sources].sort(([a],[b])=>a<b?-1:a>b?1:0)),
  static_local_imports:Object.fromEntries([...sourceImports].sort(([a],[b])=>a<b?-1:a>b?1:0)),
  scope:'unique canonical successor and limit operations, pure-formula ordinal recursion, coherent histories, their exact pinned-stage projection and ambient well-orderability of every constructible set with an actual restricted relation; internal constructibility of the order, the relativized Choice import and formal checker soundness remain separate obligations'
},null,2));
