// ACE-03T finite syntax-code and coherent-stage model.
// The carrier of presented programs is finite and explicit. Its least code
// is a test fixture, not the least code among every definition in L.
const OPS = { eq: 0, mem: 1, not: 2, and: 3, exists: 4 };
const NAMES = Object.keys(OPS);
const fail = message => { throw Error(message); };
const exact = (x, keys) => x !== null && typeof x === "object" &&
  !Array.isArray(x) && Object.keys(x).sort().join("|") === [...keys].sort().join("|");
const nat = n => Number.isSafeInteger(n) && n >= 0;

function validateProgram(program) {
  if (!exact(program, ["arity", "steps"]) || !nat(program.arity) ||
      program.arity < 1 || program.arity > 8 || !Array.isArray(program.steps) ||
      program.steps.length < 1 || program.steps.length > 64) fail("program shape or fixture resource bound");
  for (let i = 0; i < program.steps.length; i++) {
    const step = program.steps[i];
    if (!Array.isArray(step)) fail("instruction shape");
    const [op, a, b] = step;
    const variable = x => nat(x) && x < program.arity;
    const prior = x => nat(x) && x < i;
    if (op === "eq" || op === "mem") {
      if (step.length !== 3 || !variable(a) || !variable(b)) fail("atom scope");
    } else if (op === "not") {
      if (step.length !== 2 || !prior(a)) fail("negation reference");
    } else if (op === "and") {
      if (step.length !== 3 || !prior(a) || !prior(b)) fail("conjunction reference");
    } else if (op === "exists") {
      if (step.length !== 3 || !prior(a) || !variable(b)) fail("quantifier reference");
    } else fail("unknown instruction");
  }
}

// Leading 1 followed by Elias-gamma codes for each natural plus one.
// The width and instruction count determine all subsequent field lengths.
function programCode(program) {
  validateProgram(program);
  const fields = [program.arity, program.steps.length];
  for (const [op, ...args] of program.steps) fields.push(OPS[op], ...args);
  const gamma = n => { const bits = BigInt(n + 1).toString(2); return "0".repeat(bits.length - 1) + bits; };
  return BigInt("0b1" + fields.map(gamma).join(""));
}

function decodeProgram(code) {
  if (typeof code !== "bigint" || code <= 1n) fail("syntax code");
  const bits = code.toString(2); let at = 1;
  const read = () => {
    let zeros = 0;
    while (at < bits.length && bits[at] === "0") { at++; zeros++; }
    if (at + zeros >= bits.length) fail("truncated gamma code");
    const value = BigInt("0b" + bits.slice(at, at + zeros + 1)) - 1n;
    at += zeros + 1;
    if (value > BigInt(Number.MAX_SAFE_INTEGER)) fail("field bound");
    return Number(value);
  };
  const arity = read(), count = read();
  if (arity < 1 || arity > 8 || count < 1 || count > 64) fail("fixture resource bound");
  const steps = [];
  for (let i = 0; i < count; i++) {
    const op = NAMES[read()];
    if (op === undefined) fail("opcode");
    const args = op === "not" ? [read()] : [read(), read()];
    steps.push([op, ...args]);
  }
  if (at !== bits.length) fail("trailing code fields");
  const program = { arity, steps };
  validateProgram(program);
  return program;
}

// Natural-number encodings of hereditarily finite sets: bit x of y means x∈y.
const member = (x, y) => (BigInt(y) >> BigInt(x) & 1n) === 1n;
function validateStage(stage) {
  if (!Array.isArray(stage) || stage.length > 8 || new Set(stage).size !== stage.length ||
      !Array.from(stage).every(x => nat(x) && x <= 31)) fail("finite stage carrier");
  const carrier = new Set(stage);
  for (const x of stage) for (let y = 0; 2 ** y <= x; y++)
    if (member(y, x) && !carrier.has(y)) fail("stage is not transitive");
}

function evaluate(program, assignment, stage) {
  const memo = new Map();
  function run(i, env) {
    const key = `${i}:${env.join(",")}`;
    if (memo.has(key)) return memo.get(key);
    const [op, a, b] = program.steps[i];
    let value;
    if (op === "eq") value = env[a] === env[b];
    else if (op === "mem") value = member(env[a], env[b]);
    else if (op === "not") value = !run(a, env);
    else if (op === "and") value = run(a, env) && run(b, env);
    else if (op === "exists") value = stage.some(x => { const next = env.slice(); next[b] = x; return run(a, next); });
    else fail("instruction");
    memo.set(key, value);
    return value;
  }
  return run(program.steps.length - 1, assignment);
}

function describe(presentation, stage, index = 0) {
  if (exact(presentation, ["kind"]) && presentation.kind === "empty")
    return { syntax: 0n, tuple: [], value: 0, index };
  if (stage.length === 0) fail("empty stage requires the distinguished empty code");
  if (!exact(presentation, ["program", "params"])) fail("presentation shape");
  const { program, params } = presentation, syntax = programCode(program);
  if (!Array.isArray(params) || params.length !== program.arity - 1 ||
      !Array.from(params).every(x => stage.includes(x))) fail("parameter tuple");
  const tuple = params.map(x => stage.indexOf(x));
  let value = 0;
  for (const x of stage) if (evaluate(program, [x, ...params], stage)) value += 2 ** x;
  if (!Number.isSafeInteger(value)) fail("HF encoding overflow");
  return { syntax, tuple, value, index };
}

function compareCodes(a, b) {
  if (a.syntax !== b.syntax) return a.syntax < b.syntax ? -1 : 1;
  if (a.tuple.length !== b.tuple.length) fail("one syntax code has two arities");
  for (let i = 0; i < a.tuple.length; i++)
    if (a.tuple[i] !== b.tuple[i]) return a.tuple[i] < b.tuple[i] ? -1 : 1;
  return 0;
}

function subsets(stage) {
  let out = [0];
  for (const x of stage) out = [...out, ...out.map(y => y + 2 ** x)];
  return out;
}

function buildFiniteStage(stage, presentations) {
  validateStage(stage);
  if (!Array.isArray(presentations)) fail("presentation list");
  const codes = Array.from(presentations, (p, i) => describe(p, stage, i)).sort(compareCodes);
  const selectors = new Map();
  for (const c of codes) if (!selectors.has(c.value)) selectors.set(c.value, c);
  const expected = subsets(stage);
  if (expected.some(x => !selectors.has(x)) || selectors.size !== expected.length) fail("incomplete finite definition carrier");
  // The old stage stays an initial segment. Only fresh sets use the new order.
  const fresh = [...selectors.values()].filter(c => !stage.includes(c.value));
  const order = [...stage, ...fresh.map(c => c.value)];
  return { kind: "ACE-03T-finite-stage-v1", stage: [...stage], order,
    selectors: order.map(value => ({ value, presentation: selectors.get(value).index })) };
}

function checkFiniteStage(stage, presentations, certificate) {
  try {
    validateStage(stage);
    if (!Array.isArray(presentations) || !exact(certificate, ["kind", "stage", "order", "selectors"]) ||
        certificate.kind !== "ACE-03T-finite-stage-v1" ||
        JSON.stringify(certificate.stage) !== JSON.stringify(stage)) return false;
    const { order, selectors } = certificate;
    if (!Array.isArray(order) || !Array.isArray(selectors) || new Set(order).size !== order.length ||
        order.length !== 2 ** stage.length || selectors.length !== order.length) return false;
    const wanted = subsets(stage);
    if (!order.every(x => wanted.includes(x)) || !stage.every((x, i) => order[i] === x)) return false;
    const codes = Array.from(presentations, (p, i) => describe(p, stage, i));
    const chosen = [];
    for (let i = 0; i < order.length; i++) {
      const s = selectors[i];
      if (!exact(s, ["value", "presentation"]) || s.value !== order[i] ||
          !nat(s.presentation) || s.presentation >= codes.length) return false;
      const c = codes[s.presentation];
      if (c.value !== s.value) return false;
      // Scan every code in the declared finite carrier independently of sorting.
      if (codes.some(other => other.value === s.value && compareCodes(other, c) < 0)) return false;
      chosen.push(c);
    }
    for (let i = stage.length; i < order.length; i++)
      for (let j = i + 1; j < order.length; j++) if (compareCodes(chosen[i], chosen[j]) >= 0) return false;
    return true;
  } catch { return false; }
}

function isInitialSegment(earlier, later) {
  return earlier.length <= later.length && Array.from(earlier).every((x, i) => nat(x) && later[i] === x);
}

function unionFiniteChain(orders) {
  if (!Array.isArray(orders)) fail("order chain");
  let result = [];
  for (const order of orders) {
    if (!Array.isArray(order) || !Array.from(order).every(nat) || new Set(order).size !== order.length || !isInitialSegment(result, order)) fail("initial-segment extension");
    result = [...order];
  }
  return result;
}

function chooseFromFiniteFamily(order, family) {
  if (!Array.isArray(order) || !Array.from(order).every(nat) || new Set(order).size !== order.length || !Array.isArray(family)) fail("choice input");
  return Array.from(family, row => {
    if (!Array.isArray(row) || !row.length || !Array.from(row).every(x => order.includes(x))) fail("nonempty subset premise");
    return order.find(x => row.includes(x));
  });
}

export { validateProgram, programCode, decodeProgram, member, evaluate, describe,
  compareCodes, subsets, buildFiniteStage, checkFiniteStage, isInitialSegment,
  unionFiniteChain, chooseFromFiniteFamily };
