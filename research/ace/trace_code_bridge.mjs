// ACE-03U: finite semantic traces and deterministic instruction decorations.
// Bounds apply to this executable model. Object-language proofs live in the
// companion modules and state their own unrestricted quantifiers.
import { validateProgram, member, evaluate } from './well_order_codes.mjs';

const fail = message => { throw Error(message); };
const exact = (x, keys) => x !== null && typeof x === 'object' && !Array.isArray(x) &&
  Object.keys(x).sort().join('|') === [...keys].sort().join('|');
const nat = x => Number.isSafeInteger(x) && x >= 0;
const OPCODES = ['eq', 'mem', 'not', 'and', 'exists'];

function environment(carrier, arity) {
  if (!Array.isArray(carrier) || carrier.length > 8 ||
      !Array.from(carrier).every(x => nat(x) && x <= 31) ||
      new Set(carrier).size !== carrier.length) fail('finite carrier');
  if (!nat(arity) || arity < 1 || arity > 8) fail('positive finite width');
  if (carrier.length ** arity > 256) fail('assignment resource bound');
  let tuples = [[]];
  for (let i = 0; i < arity; i++) tuples = tuples.flatMap(xs => carrier.map(x => [...xs, x]));
  return { carrier, arity, tuples, index: new Map(tuples.map((xs, i) => [xs.join(','), i])) };
}

function validateTrace(carrier, trace) {
  if (!exact(trace, ['arity', 'rows']) || !Array.isArray(trace.rows) ||
      trace.rows.length < 1 || trace.rows.length > 64) fail('trace shape');
  const env = environment(carrier, trace.arity);
  for (const row of trace.rows) {
    if (!Array.isArray(row) || row.length !== env.tuples.length ||
        !Array.from(row).every(x => typeof x === 'boolean')) fail('semantic row shape');
  }
  return env;
}

function instructionRow(instruction, rows, env) {
  const [op, a, b] = instruction;
  if (op === 'eq') return env.tuples.map(xs => xs[a] === xs[b]);
  if (op === 'mem') return env.tuples.map(xs => member(xs[a], xs[b]));
  if (op === 'not') return rows[a].map(x => !x);
  if (op === 'and') return rows[a].map((x, i) => x && rows[b][i]);
  if (op === 'exists') return env.tuples.map(xs => env.carrier.some(x => {
    const next = [...xs]; next[b] = x;
    return rows[a][env.index.get(next.join(','))];
  }));
  fail('instruction');
}

function semanticTrace(carrier, program) {
  validateProgram(program);
  const env = environment(carrier, program.arity), rows = [];
  for (const instruction of program.steps) rows.push(instructionRow(instruction, rows, env));
  return { arity: program.arity, rows };
}

// A finite order of tagged operands. A tag fixes the number of operands.
// This order chooses a decoration of one semantic trace. It does not minimize
// the separate natural-number encoding of complete programs from ACE-03T.
function* candidates(arity, rowIndex) {
  for (const op of ['eq', 'mem']) for (let a = 0; a < arity; a++)
    for (let b = 0; b < arity; b++) yield [op, a, b];
  for (let a = 0; a < rowIndex; a++) yield ['not', a];
  for (let a = 0; a < rowIndex; a++) for (let b = 0; b < rowIndex; b++) yield ['and', a, b];
  for (let a = 0; a < rowIndex; a++) for (let b = 0; b < arity; b++) yield ['exists', a, b];
}

function compareInstructions(left, right) {
  const a = [OPCODES.indexOf(left[0]), ...left.slice(1)], b = [OPCODES.indexOf(right[0]), ...right.slice(1)];
  for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i];
  return a.length - b.length;
}

function recoverProgram(carrier, trace) {
  const env = validateTrace(carrier, trace), steps = [];
  for (let k = 0; k < trace.rows.length; k++) {
    let witness;
    for (const instruction of candidates(trace.arity, k)) {
      const row = instructionRow(instruction, trace.rows, env);
      if (row.every((x, i) => x === trace.rows[k][i])) { witness = instruction; break; }
    }
    if (!witness) fail(`row ${k} has no permitted instruction`);
    steps.push(witness);
  }
  const program = { arity: trace.arity, steps };
  validateProgram(program);
  return program;
}

// Verification uses the separate scalar evaluator for each program prefix.
// Neither the decoder nor the relation-table interpreter decides acceptance.
function checkDecoration(carrier, trace, program) {
  try {
    const env = validateTrace(carrier, trace);
    validateProgram(program);
    if (program.arity !== trace.arity || program.steps.length !== trace.rows.length) return false;
    for (let k = 0; k < program.steps.length; k++) {
      const prefix = { arity: program.arity, steps: program.steps.slice(0, k + 1) };
      for (let i = 0; i < env.tuples.length; i++)
        if (evaluate(prefix, env.tuples[i], carrier) !== trace.rows[k][i]) return false;
    }
    return true;
  } catch { return false; }
}

function sliceTrace(carrier, trace, baseTuple) {
  const env = validateTrace(carrier, trace);
  if (!Array.isArray(baseTuple) || baseTuple.length !== trace.arity ||
      !Array.from(baseTuple).every(x => carrier.includes(x))) fail('base tuple');
  const last = trace.rows.at(-1);
  return carrier.filter(x => last[env.index.get([x, ...baseTuple.slice(1)].join(','))]);
}

export { environment, validateTrace, semanticTrace, recoverProgram, checkDecoration,
  sliceTrace, candidates, compareInstructions };
