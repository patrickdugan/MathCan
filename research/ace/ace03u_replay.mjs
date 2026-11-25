// Run every ACE-03U replay and compare its exact, separately pinned receipt.
// The aggregate records source bytes and totals; each child performs its own
// independent formula-interface and kernel checks or finite semantic checks.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const root = new URL('./', import.meta.url);
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const insist = (condition, message) => { if (!condition) throw Error(message); };
const names = ['canonical_relation', 'syntax_trace_adequacy',
  'finite_witness_selection', 'trace_code_bridge'];
const receipts = {}, receiptHashes = {};

for (const name of names) {
  const result = spawnSync(process.execPath, [fileURLToPath(new URL(`${name}_replay.mjs`, root))],
    { encoding: 'utf8', timeout: 120000, maxBuffer: 4 * 1024 * 1024 });
  insist(!result.error && result.status === 0,
    `${name} replay failed: ${result.error?.message || result.stderr || result.status}`);
  const expected = readFileSync(new URL(`${name}_receipt.json`, root), 'utf8');
  insist(result.stdout === expected, `${name} receipt differs`);
  receipts[name] = JSON.parse(expected);
  receiptHashes[`${name}_receipt.json`] = hash(expected);
}

// These modules use static local imports. Follow those imports to include the
// existing proof generators, interface builders and executable kernel.
const sources = new Map();
function collect(name) {
  insist(/^[A-Za-z0-9_]+\.mjs$/.test(name), `unexpected source path: ${name}`);
  if (sources.has(name)) return;
  const source = readFileSync(new URL(name, root), 'utf8');
  sources.set(name, hash(source));
  const imports = [...source.matchAll(/^\s*import\s+[\s\S]*?\sfrom\s*['"]([^'"]+)['"]/gm)];
  for (const match of imports) {
    if (match[1].startsWith('./')) collect(match[1].slice(2));
    else insist(match[1].startsWith('node:'), `unexpected import: ${match[1]}`);
  }
}
collect('ace03u_replay.mjs');
for (const name of names) collect(`${name}_replay.mjs`);
sources.set('L_formula.json', hash(readFileSync(new URL('L_formula.json', root))));

const proofs = names.slice(0, 3).map(name => receipts[name]);
for (const receipt of proofs) {
  insist(receipt.pinned_L_unchanged === true, 'pinned L changed');
  insist(receipt.checked_modules === receipt.checks.length, 'module count mismatch');
  insist(receipt.kernel_visits === receipt.checks.reduce((n, item) => n + item.nodes, 0), 'visit count mismatch');
  insist(receipt.independent_exact_goals === receipt.checked_modules, 'missing exact goal checks');
  insist(receipt.negative_controls === receipt.controls.length, 'control count mismatch');
  insist(receipt.checks.every(item => !item.ambient_axioms.includes('choice')), 'Choice import');
}
const total = key => proofs.reduce((n, receipt) => n + receipt[key], 0);
const reused = proofs.reduce((n, receipt) => n + (receipt.reused_helper_checks || 0), 0);
const finite = receipts.trace_code_bridge;
insist(finite.pinned_L_sha256 === sources.get('L_formula.json'), 'finite pinned L differs');
insist(finite.accepted_valid_traces + finite.rejected_invalid_traces === finite.exhaustive_raw_traces,
  'finite trace accounting mismatch');

console.log(JSON.stringify({
  experiment: 'ACE-03U',
  part: 'combined_replay_and_source_receipt',
  exact_receipt_comparisons: names.length,
  checked_modules: total('checked_modules'),
  new_statement_checks: total('checked_modules') - reused,
  reused_helper_checks: reused,
  independent_exact_goals: total('independent_exact_goals'),
  kernel_visits: total('kernel_visits'),
  proof_rejection_controls: total('negative_controls'),
  finite_malformed_or_corrupt_controls: finite.malformed_or_corrupt_controls,
  exhaustive_raw_traces: finite.exhaustive_raw_traces,
  rejected_invalid_traces: finite.rejected_invalid_traces,
  receipt_sha256: receiptHashes,
  source_file_count: sources.size,
  source_files_sha256: Object.fromEntries([...sources].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)),
  scope: 'four exact replay receipts, checked proof totals and static source-import closure; formal kernel soundness and full syntax-code adequacy remain open'
}, null, 2));
