import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { definition } from './constructible_definition.mjs';
import { programCode, decodeProgram } from './well_order_codes.mjs';
import { semanticTrace, recoverProgram, checkDecoration, sliceTrace,
  candidates } from './trace_code_bridge.mjs';

const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const insist = (x, message) => { if (!x) throw Error(message); };
const rowsFromMasks = (masks, size) => masks.map(mask =>
  Array.from({ length: size }, (_, i) => Boolean(mask >> BigInt(i) & 1n)));
const maskFromRow = row => row.reduce((s, v, i) => v ? s | 1n << BigInt(i) : s, 0n);

// Independent bitset semantics for the five pinned operations. Coordinates
// come from mixed-radix digits, independently of the tuple-table evaluator.
function referenceInstructions(carrier, width, earlier) {
  const m = carrier.length, size = m ** width;
  const coordinate = (index, slot) => carrier[Math.floor(index / m ** (width - slot - 1)) % m];
  const masks = new Map(), all = (1n << BigInt(size)) - 1n;
  function keep(instruction, mask) {
    const key = mask.toString();
    if (!masks.has(key)) masks.set(key, []);
    masks.get(key).push(instruction);
  }
  function atom(test) {
    let mask = 0n;
    for (let s = 0; s < size; s++) if (test(s)) mask |= 1n << BigInt(s);
    return mask;
  }
  for (let i = 0; i < width; i++) for (let j = 0; j < width; j++)
    keep(['eq', i, j], atom(s => coordinate(s, i) === coordinate(s, j)));
  for (let i = 0; i < width; i++) for (let j = 0; j < width; j++)
    keep(['mem', i, j], atom(s => Math.floor(coordinate(s, j) / 2 ** coordinate(s, i)) % 2 === 1));
  for (let i = 0; i < earlier.length; i++) keep(['not', i], all ^ earlier[i]);
  for (let i = 0; i < earlier.length; i++) for (let j = 0; j < earlier.length; j++)
    keep(['and', i, j], earlier[i] & earlier[j]);
  for (let i = 0; i < earlier.length; i++) for (let slot = 0; slot < width; slot++) {
    const place = m ** (width - slot - 1);
    const mask = atom(s => {
      const current = Math.floor(s / place) % m;
      for (let value = 0; value < m; value++) {
        const changed = s + (value - current) * place;
        if (earlier[i] >> BigInt(changed) & 1n) return true;
      }
      return false;
    });
    keep(['exists', i, slot], mask);
  }
  return masks;
}

function rng(seed) {
  let state = seed >>> 0;
  return n => { state ^= state << 13; state ^= state >>> 17; state ^= state << 5; return (state >>> 0) % n; };
}

function run() {
  const pinned = readFileSync(new URL('./L_formula.json', import.meta.url));
  insist(same(JSON.parse(pinned), definition('v', true).L), 'pinned L mismatch');
  let rawTraces = 0, validTraces = 0, invalidTraces = 0, recoveredRows = 0;
  let ambiguousRows = 0, scalarTruthChecks = 0, slices = 0, changedPrograms = 0, negative = 0;
  const fixtures = [];
  function reject(fn) { let caught = false; try { fn(); } catch { caught = true; } insist(caught, 'negative accepted'); negative++; }
  function rejectDecoration(carrier, trace, program) {
    insist(!checkDecoration(carrier, trace, program), 'bad decoration accepted'); negative++;
  }

  function verifyValid(carrier, trace, expectedSteps) {
    const decoded = recoverProgram(carrier, trace);
    insist(same(decoded.steps, expectedSteps), 'least admissible instruction mismatch');
    insist(checkDecoration(carrier, trace, decoded), 'independent scalar check failed');
    const again = semanticTrace(carrier, decoded);
    insist(same(again, trace), 'decoded program changes trace');
    insist(same(recoverProgram(carrier, again), decoded), 'decoration not idempotent');
    insist(same(decodeProgram(programCode(decoded)), decoded), 'natural syntax-code round trip');
    scalarTruthChecks += carrier.length ** trace.arity * trace.rows.length;
    recoveredRows += trace.rows.length;
    return decoded;
  }

  // Exhaust every Boolean semantic trace through three rows in these carriers.
  for (const [carrier, width] of [[[], 1], [[0], 2], [[0, 1], 1], [[0, 1], 2]]) {
    const tupleCount = carrier.length ** width, rowCount = 2 ** tupleCount;
    let accepted = 0, rejected = 0;
    for (let length = 1; length <= 3; length++) for (let serial = 0; serial < rowCount ** length; serial++) {
      const masks = []; let remainder = serial;
      for (let i = 0; i < length; i++) { masks.push(BigInt(remainder % rowCount)); remainder = Math.floor(remainder / rowCount); }
      const expected = []; let valid = true;
      for (let k = 0; k < length; k++) {
        const matches = referenceInstructions(carrier, width, masks.slice(0, k)).get(masks[k].toString());
        if (!matches) { valid = false; break; }
        expected.push(matches[0]);
      }
      const trace = { arity: width, rows: rowsFromMasks(masks, tupleCount) };
      rawTraces++;
      if (valid) {
        verifyValid(carrier, trace, expected); validTraces++; accepted++;
        for (let k = 0; k < length; k++)
          if (referenceInstructions(carrier, width, masks.slice(0, k)).get(masks[k].toString()).length > 1) ambiguousRows++;
      } else {
        let caught = false; try { recoverProgram(carrier, trace); } catch { caught = true; }
        insist(caught, 'decoder accepted semantically invalid trace'); invalidTraces++; rejected++;
      }
    }
    fixtures.push({ carrier, width, valid_traces: accepted, invalid_traces: rejected });
  }

  const stress = [], opCounts = Object.fromEntries(['eq', 'mem', 'not', 'and', 'exists'].map(x => [x, 0]));
  for (const seed of [109, 113, 127]) {
    const next = rng(seed); let rows = 0;
    for (let trial = 0; trial < 64; trial++) {
      const carrier = [[], [0], [0, 1], [0, 1, 2, 3], [1, 3]][trial % 5];
      const arity = 1 + next(3), length = 1 + next(16), steps = [];
      for (let k = 0; k < length; k++) {
        const options = [...candidates(arity, k)], instruction = options[next(options.length)];
        steps.push(instruction); opCounts[instruction[0]]++;
      }
      const program = { arity, steps }, trace = semanticTrace(carrier, program), masks = trace.rows.map(maskFromRow);
      const expected = masks.map((mask, k) => {
        const matches = referenceInstructions(carrier, arity, masks.slice(0, k)).get(mask.toString());
        insist(matches, 'source program violates reference semantics');
        if (matches.length > 1) ambiguousRows++;
        return matches[0];
      });
      insist(checkDecoration(carrier, trace, program), 'original program scalar disagreement');
      scalarTruthChecks += carrier.length ** arity * length;
      const decoded = verifyValid(carrier, trace, expected);
      if (!same(decoded, program)) changedPrograms++;
      // Check every available full base tuple, including all choices of the
      // unused coordinate zero, against a direct read of the last bitset.
      const size = carrier.length ** arity;
      for (let index = 0; index < size; index++) {
        const base = Array.from({ length: arity }, (_, j) => carrier[Math.floor(index / carrier.length ** (arity - j - 1)) % carrier.length]);
        const expectedSlice = carrier.filter((_, j) => {
          const tail = index % carrier.length ** (arity - 1), at = j * carrier.length ** (arity - 1) + tail;
          return Boolean(masks.at(-1) >> BigInt(at) & 1n);
        });
        insist(same(sliceTrace(carrier, trace, base), expectedSlice), 'parameter slice mismatch');
        slices++;
      }
      rows += length;
    }
    stress.push({ seed, programs: 64, rows });
  }
  insist(Object.values(opCounts).every(n => n > 0), 'missing opcode coverage');

  const simple = { arity: 1, steps: [['eq', 0, 0]] }, good = semanticTrace([0], simple);
  for (const trace of [null, {}, { ...good, extra: true }, { arity: 0, rows: [[true]] },
    { arity: 1, rows: [] }, { arity: 1, rows: Array(1) }, { arity: 1, rows: [Array(1)] },
    { arity: 1, rows: [[1]] }, { arity: 1, rows: [[true, false]] },
    { arity: 1, rows: Array.from({ length: 65 }, () => [true]) }]) reject(() => recoverProgram([0], trace));
  for (const carrier of [null, [0, 0], [-1], [32], Array(1)]) reject(() => semanticTrace(carrier, simple));
  reject(() => semanticTrace([0, 1, 2, 3], { arity: 8, steps: [['eq', 0, 0]] }));
  reject(() => semanticTrace([0], { arity: 1, steps: [['not', 0]] }));
  reject(() => recoverProgram([0, 1], { arity: 2, rows: [[true, false, false, false]] }));
  rejectDecoration([0], good, { arity: 1, steps: [['mem', 0, 0]] });
  rejectDecoration([0], good, { arity: 2, steps: [['eq', 0, 0]] });
  rejectDecoration([0], good, { arity: 1, steps: [['eq', 0, 0], ['not', 0]] });
  rejectDecoration([0], good, { arity: 1, steps: Array(1) });
  const program = { arity: 1, steps: [['eq', 0, 0], ['not', 0], ['not', 1]] };
  const middleCorrupt = semanticTrace([0], program); middleCorrupt.rows[1][0] = true;
  rejectDecoration([0], middleCorrupt, program);
  reject(() => sliceTrace([0], good, []));
  reject(() => sliceTrace([0], good, [1]));
  reject(() => sliceTrace([0], good, Array(1)));
  reject(() => sliceTrace([], semanticTrace([], simple), [0]));

  return { experiment: 'ACE-03U', part: 'finite_syntax_trace_bridge',
    exhaustive_raw_traces: rawTraces, accepted_valid_traces: validTraces,
    rejected_invalid_traces: invalidTraces, exhaustive_fixtures: fixtures,
    stress, source_instruction_counts: opCounts, checked_recovered_rows: recoveredRows,
    independent_scalar_truth_checks: scalarTruthChecks, ambiguous_rows_with_multiple_instructions: ambiguousRows,
    source_programs_replaced_by_equivalent_decorations: changedPrograms,
    full_base_tuple_slice_checks: slices, malformed_or_corrupt_controls: negative,
    pinned_L_sha256: createHash('sha256').update(pinned).digest('hex'),
    selection_order: 'opcode then operand indices at each row; distinct from the full natural-number program-code order',
    scope: 'finite-carrier exact trace decoration and semantic replay; uniform internal coding and evaluation existence require object-language proofs' };
}

console.log(JSON.stringify(run(), null, 2));
