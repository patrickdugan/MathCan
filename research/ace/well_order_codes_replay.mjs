import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { definition } from "./constructible_definition.mjs";
import { validateProgram, programCode, decodeProgram, member, evaluate, describe,
  compareCodes, subsets, buildFiniteStage, checkFiniteStage, isInitialSegment,
  unionFiniteChain, chooseFromFiniteFamily } from "./well_order_codes.mjs";

const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const insist = (x, message) => { if (!x) throw Error(message); };
let negative = 0;
const reject = fn => { let rejected = false; try { fn(); } catch { rejected = true; } insist(rejected, "negative control accepted"); negative++; };
const badCertificate = (stage, codes, cert) => { insist(!checkFiniteStage(stage, codes, cert), "bad certificate accepted"); negative++; };

function tuples(stage, arity) {
  let result = [[]];
  for (let i = 0; i < arity; i++) result = result.flatMap(t => stage.map(x => [...t, x]));
  return result;
}

function smallPrograms() {
  const result = [];
  for (let arity = 1; arity <= 3; arity++) {
    const atoms = [];
    for (const op of ["eq", "mem"]) for (let a = 0; a < arity; a++)
      for (let b = 0; b < arity; b++) atoms.push([op, a, b]);
    const second = [...atoms, ["not", 0], ["and", 0, 0],
      ...Array.from({ length: arity }, (_, i) => ["exists", 0, i])];
    for (const atom of atoms) {
      result.push({ arity, steps: [atom] });
      for (const step of second) result.push({ arity, steps: [atom, step] });
    }
  }
  return result;
}

// Independent whole-relation interpreter, including projection by matching
// every assignment away from the quantified coordinate.
function relationTable(program, stage) {
  const assignments = tuples(stage, program.arity), rows = [];
  for (const [op, a, b] of program.steps) {
    if (op === "eq") rows.push(assignments.map(s => s[a] === s[b]));
    if (op === "mem") rows.push(assignments.map(s => member(s[a], s[b])));
    if (op === "not") rows.push(rows[a].map(x => !x));
    if (op === "and") rows.push(rows[a].map((x, i) => x && rows[b][i]));
    if (op === "exists") rows.push(assignments.map(s => assignments.some((t, i) =>
      rows[a][i] && s.every((x, j) => j === b || x === t[j]))));
  }
  return { assignments, truth: rows.at(-1) };
}

function subsetWitness(selected) {
  const steps = [["eq", 0, 0], ["not", 0]];
  let root = 1;
  for (let i = 0; i < selected.length; i++) {
    const atom = steps.length; steps.push(["eq", 0, i + 1]);
    const negOld = steps.length; steps.push(["not", root]);
    const negAtom = steps.length; steps.push(["not", atom]);
    const conjunction = steps.length; steps.push(["and", negOld, negAtom]);
    root = steps.length; steps.push(["not", conjunction]);
  }
  return { program: { arity: selected.length + 1, steps }, params: selected };
}

function witnesses(stage) {
  const out = [{ kind: "empty" }];
  if (stage.length === 0) return out;
  for (let mask = 0; mask < 2 ** stage.length; mask++)
    out.push(subsetWitness(stage.filter((_, i) => mask >> i & 1)));
  return out;
}

function permutations(xs) {
  if (!xs.length) return [[]];
  return xs.flatMap((x, i) => permutations(xs.filter((_, j) => j !== i)).map(t => [x, ...t]));
}

function run() {
  const pinnedBytes = readFileSync(new URL("./L_formula.json", import.meta.url));
  insist(same(definition("v", true).L, JSON.parse(pinnedBytes)), "pinned L mismatch");
  const programs = smallPrograms(), syntax = new Map();
  let semanticChecks = 0, presentedCodes = 0, selectedOutputs = 0, leastSubsetChecks = 0;
  for (const program of programs) {
    validateProgram(program);
    const code = programCode(program);
    insist(!syntax.has(code), "syntax encoding collision");
    syntax.set(code, program);
    insist(same(decodeProgram(code), program), "syntax round trip");
  }

  const stageRuns = [];
  for (const stage of [[], [0], [0, 1], [0, 1, 2, 3]]) {
    const codes = witnesses(stage);
    for (const program of programs) {
      const table = relationTable(program, stage);
      for (let i = 0; i < table.assignments.length; i++) {
        insist(evaluate(program, table.assignments[i], stage) === table.truth[i], "two evaluators disagree");
        semanticChecks++;
      }
      if (stage.length) for (const params of tuples(stage, program.arity - 1)) codes.push({ program, params });
    }
    const cert = buildFiniteStage(stage, codes);
    insist(checkFiniteStage(stage, codes, cert), "finite certificate rejected");
    insist(isInitialSegment(stage, cert.order), "old stage changed");
    const selected = new Map(cert.selectors.map(s => [s.value, describe(codes[s.presentation], stage)]));
    const expectedValues = subsets(stage);
    insist(new Set(cert.order).size === expectedValues.length && expectedValues.every(x => cert.order.includes(x)), "coverage");
    // Every nonempty subset of the full successor carrier has exactly one
    // least element in the emitted order. This includes all 65,535 subsets
    // when the successor carrier has sixteen elements.
    for (let mask = 1; mask < 2 ** cert.order.length; mask++) {
      const subset = expectedValues.filter((_, i) => mask >> i & 1);
      const minima = subset.filter(x => subset.every(y => cert.order.indexOf(x) <= cert.order.indexOf(y)));
      insist(minima.length === 1, "least element failure");
      const chosen = chooseFromFiniteFamily(cert.order, [subset]);
      insist(chosen[0] === minima[0], "choice minimum disagreement");
      leastSubsetChecks++;
    }
    for (const p of codes) {
      const descriptor = describe(p, stage);
      insist(compareCodes(selected.get(descriptor.value), descriptor) <= 0, "nonleast selected code");
    }
    presentedCodes += codes.length; selectedOutputs += cert.order.length;
    stageRuns.push({ stage_size: stage.length, presented_codes: codes.length, successor_order: cert.order });

    badCertificate(stage, codes, { ...cert, extra: true });
    badCertificate(stage, codes, { ...cert, order: [...cert.order, cert.order[0]] });
    badCertificate(stage, codes, { ...cert, selectors: cert.selectors.map((s, i) => i ? s : { ...s, presentation: codes.length }) });
    if (stage.length > 1) {
      const order = [...cert.order]; [order[0], order[1]] = [order[1], order[0]];
      badCertificate(stage, codes, { ...cert, order });
    }
  }

  // Vary the incoming well-order while keeping the same transitive carrier.
  let incomingOrders = 0;
  for (const stage of permutations([0, 1, 2, 3])) {
    const codes = witnesses(stage);
    const p = { arity: 2, steps: [["eq", 0, 1]] };
    for (const x of stage) codes.push({ program: p, params: [x] });
    const cert = buildFiniteStage(stage, codes);
    insist(checkFiniteStage(stage, codes, cert) && isInitialSegment(stage, cert.order), "incoming order coherence");
    incomingOrders++;
  }

  const chain = [[]];
  for (let i = 0; i < 4; i++) {
    const stage = chain.at(-1), codes = witnesses(stage);
    const cert = buildFiniteStage(stage, codes);
    insist(checkFiniteStage(stage, codes, cert), "stage chain check");
    chain.push(cert.order);
  }
  insist(same(unionFiniteChain(chain), chain.at(-1)), "chain union");

  // Local least-code orders do not imply old-stage coherence.
  const old = [0, 1], resorted = [1, 0, 2];
  insist(!isInitialSegment(old, resorted), "resorting counterexample missing");
  reject(() => unionFiniteChain([old, resorted]));

  // Coherent restrictions can still insert new predecessors. The infinite
  // continuation is reverse omega; the written proof gives its failure.
  const reversed = Array.from({ length: 9 }, (_, n) => Array.from({ length: n }, (_, i) => n - i - 1));
  for (let n = 1; n < reversed.length; n++)
    insist(same(reversed[n].filter(x => x < n - 1), reversed[n - 1]), "reverse restriction witness");
  reject(() => unionFiniteChain(reversed));

  // Raw lex across variable widths admits this descending finite prefix.
  const words = Array.from({ length: 9 }, (_, i) => [...Array(i).fill(0), 1]);
  const rawLex = (a, b) => {
    for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i];
    return a.length - b.length;
  };
  for (let i = 1; i < words.length; i++) insist(rawLex(words[i], words[i - 1]) < 0, "lex descending witness");

  const valid = { arity: 1, steps: [["eq", 0, 0]] };
  for (const p of [null, { ...valid, arity: 0 }, { ...valid, extra: true },
    { ...valid, steps: [] }, { ...valid, steps: [["eq", 0, 1]] },
    { ...valid, steps: [["not", 0]] }, { ...valid, steps: [["eq", 0, 0], ["and", 0, 1]] },
    { ...valid, steps: [["eq", 0, 0], ["exists", 0, 1]] }, { ...valid, steps: Array(1) }]) reject(() => programCode(p));
  for (const code of [0n, 1n, -1n, 2n, "100", programCode(valid) * 2n]) reject(() => decodeProgram(code));
  reject(() => buildFiniteStage([1], witnesses([1])));
  reject(() => buildFiniteStage([0, 0], witnesses([0])));
  reject(() => buildFiniteStage(Array(1), [{ kind: "empty" }]));
  reject(() => buildFiniteStage([0], [{ kind: "empty" }]));
  reject(() => buildFiniteStage([], [{ kind: "empty" }, { program: valid, params: [] }]));
  reject(() => buildFiniteStage([0], [{ program: { arity: 2, steps: [["eq", 0, 0]] }, params: Array(1) }]));
  reject(() => chooseFromFiniteFamily([0, 1], [[]]));
  reject(() => chooseFromFiniteFamily([0, 1], [[2]]));
  reject(() => chooseFromFiniteFamily([0, 1], [Array(1)]));
  reject(() => chooseFromFiniteFamily([0, 1], Array(1)));
  reject(() => unionFiniteChain([Array(1)]));
  const holeCodes = [{ kind: "empty" }]; holeCodes.length = 2;
  badCertificate([], holeCodes, buildFiniteStage([], [{ kind: "empty" }]));
  reject(() => buildFiniteStage([], holeCodes));
  insist(same(chooseFromFiniteFamily([0, 1], []), []), "empty family");
  const shared = { arity: 1, steps: [["eq", 0, 0]] };
  for (let i = 1; i < 64; i++) shared.steps.push(["and", i - 1, i - 1]);
  validateProgram(shared);
  insist(evaluate(shared, [0], [0]), "shared program DAG evaluation");

  return {
    experiment: "ACE-03T", part: "finite_code_and_coherence", syntax_programs: programs.length,
    syntax_roundtrips: syntax.size, independent_truth_checks: semanticChecks,
    presented_codes: presentedCodes, selected_outputs: selectedOutputs,
    exhaustive_nonempty_subsets_and_choice_checks: leastSubsetChecks,
    incoming_stage_orders: incomingOrders, stage_runs: stageRuns,
    coherent_chain_sizes: chain.map(x => x.length), negative_controls: negative,
    adversarial_examples: { old_order_resorting: { old, resorted },
      coherent_reverse_orders: reversed, variable_width_lex_descent: words },
    pinned_L_sha256: createHash("sha256").update(pinnedBytes).digest("hex"),
    scope: "finite explicit syntax carriers and HF stages; infinite well-order proofs and pinned-Def adequacy require object-language derivations"
  };
}

console.log(JSON.stringify(run(), null, 2));
