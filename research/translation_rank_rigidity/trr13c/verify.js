#!/usr/bin/env node
'use strict';
/*
 * verify.js — exact checks for
 *
 *     m = deg gcd( N + (X-1) * sum_j c_j X^{i_j} ,  X^N - 1 ),      N prime, char K not dividing N.
 *
 * No dependencies. Everything is exact arithmetic (bitsets over F_2, table-based F_{p^d}, BigInt).
 * X^N - 1 is separable, so m is also the number of N-th roots of unity z with H(z) = 0;
 * both ways of computing m are used below and cross-checked.
 *
 *   node verify.js            default checks, about 10 seconds (k = 1 sweep: 1082 pairs (p, N))
 *   node verify.js --full     large sweeps, about 20 minutes and 1 GB of memory:
 *                             k = 1 over every field F_{p^d} with p^d <= 2^26 (p = 2), 2^24 (p = 3, 5, 7),
 *                             2^22 (7 < p < 4000) and N <= 140000 (1706 pairs (p, N));
 *                             exhaustive k = 2 up to N = 257.
 *
 * Sections: 1 stated example and lemma · 2 equality family N = 4^e + 2^e + 1 · 3 cofactor-7 sections ·
 *           4 Frobenius orbits, Mersenne primes, binary trinomials · 5 k = 1 sweep · 6 k = 2 ·
 *           7 odd characteristic · 8 a vanishing Fourier minor.
 * Notation: m(N, i, c) = deg gcd(N + c X^i (X - 1), X^N - 1); in characteristic 2 with c = 1 this is
 *           deg gcd(1 + X^i + X^{i+1}, X^N - 1).
 */

const FULL = process.argv.includes('--full');
let failures = 0, passes = 0;
function check(name, ok, detail) {
  console.log((ok ? 'PASS  ' : 'FAIL  ') + name + (detail ? '   [' + detail + ']' : ''));
  if (ok) passes++; else failures++;
}
function section(t) { console.log('\n=== ' + t + ' ==='); }

// ----------------------------------------------------------------------------------------------
// Elementary number theory
// ----------------------------------------------------------------------------------------------
function modpow(b, e, m) { b %= m; let r = 1n; while (e > 0n) { if (e & 1n) r = r * b % m; b = b * b % m; e >>= 1n; } return r; }
const MR_BASES = [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n];
// deterministic Miller–Rabin for n < 3.3e24 (first 13 primes as bases)
function isPrimeBig(n) {
  n = BigInt(n);
  if (n < 2n) return false;
  for (const p of MR_BASES) { if (n % p === 0n) return n === p; }
  let d = n - 1n, s = 0; while ((d & 1n) === 0n) { d >>= 1n; s++; }
  for (const a of MR_BASES) {
    let x = modpow(a, d, n);
    if (x === 1n || x === n - 1n) continue;
    let comp = true;
    for (let r = 1; r < s; r++) { x = x * x % n; if (x === n - 1n) { comp = false; break; } }
    if (comp) return false;
  }
  return true;
}
function isPrime(n) { if (n < 2) return false; for (let f = 2; f * f <= n; f++) if (n % f === 0) return false; return true; }
function primesUpTo(n) { const out = []; for (let k = 2; k <= n; k++) if (isPrime(k)) out.push(k); return out; }
function ordMod(a, N) { let t = a % N, k = 1; while (t !== 1) { t = (t * a) % N; k++; if (k > N) return -1; } return k; }
function invMod(a, N) { let [r0, r1, s0, s1] = [N, ((a % N) + N) % N, 0, 1]; while (r1) { const q = Math.floor(r0 / r1); [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; } return ((s0 % N) + N) % N; }
function primeFactors(n) { const fs = []; for (let f = 2; f * f <= n; f++) if (n % f === 0) { fs.push(f); while (n % f === 0) n /= f; } if (n > 1) fs.push(n); return fs; }

// Uniform bounds proved in the write-up
function capK1(N) { let m = 1; while ((m + 1) * m <= N - 1) m++; return m; }             // m(m-1) <= N-1
function capK2(N) {                                                                      // both k = 2 inequalities
  let m = 2;
  for (;;) {
    const t = m + 1, P = BigInt(t) * BigInt(t - 1), n1 = BigInt(N - 1);
    const first = P * BigInt(t - 2) <= 2n * n1 * BigInt(N - 2);
    const second = P < 2n * n1 || (P - n1) * (P - 2n * n1) <= BigInt(t - 2) * n1 * n1;   // (rho-1)(rho-2) <= m-2
    if (!(first && second) || t > N - 1) break;
    m = t;
  }
  return m;
}

// ----------------------------------------------------------------------------------------------
// F_2[X] as bitsets
// ----------------------------------------------------------------------------------------------
function p2zero(nbits) { return new Uint32Array((nbits >>> 5) + 2); }
function p2flip(a, k) { a[k >>> 5] ^= (1 << (k & 31)); }
function p2bit(a, k) { return (a[k >>> 5] >>> (k & 31)) & 1; }
function p2deg(a, hint) {
  let w = hint === undefined ? a.length - 1 : Math.min(a.length - 1, hint >>> 5);
  while (w >= 0 && a[w] === 0) w--;
  return w < 0 ? -1 : w * 32 + 31 - Math.clz32(a[w]);
}
function p2fromExps(exps) { const a = p2zero(Math.max(...exps) + 1); for (const e of exps) p2flip(a, e); return a; }
function p2exps(a) { const out = []; const d = p2deg(a); for (let k = d; k >= 0; k--) if (p2bit(a, k)) out.push(k); return out; }
function p2str(a) { const e = p2exps(a); return e.length ? e.map(k => k === 0 ? '1' : k === 1 ? 'X' : 'X^' + k).join(' + ') : '0'; }
function p2xorShift(a, b, db, s) {                       // a ^= b << s
  const ws = s >>> 5, bs = s & 31, nb = (db >>> 5) + 1;
  if (bs === 0) { for (let j = 0; j < nb; j++) a[j + ws] ^= b[j]; }
  else { const rs = 32 - bs; for (let j = 0; j < nb; j++) { const v = b[j]; a[j + ws] ^= (v << bs); a[j + ws + 1] ^= (v >>> rs); } }
}
function p2gcd(a, b) {
  a = a.slice(); b = b.slice();
  let da = p2deg(a), db = p2deg(b);
  while (db >= 0) {
    while (da >= db) { p2xorShift(a, b, db, da - db); da = p2deg(a, da); }
    const t = a; a = b; b = t; const td = da; da = db; db = td;
  }
  return { poly: a, deg: da };
}
// remainder of a (degree da) modulo a sparse polynomial given by its exponents: O(da * #terms)
function p2remSparse(a, da, hexps) {
  const dh = Math.max(...hexps), low = hexps.filter(e => e !== dh);
  for (let k = da; k >= dh; k--) {
    if ((a[k >>> 5] >>> (k & 31)) & 1) {
      const s = k - dh; a[k >>> 5] ^= (1 << (k & 31));
      for (let j = 0; j < low.length; j++) { const t = s + low[j]; a[t >>> 5] ^= (1 << (t & 31)); }
    }
  }
  return p2deg(a, Math.max(dh - 1, 0));
}
function reduceExps(exps) { const c = new Map(); for (const e of exps) c.set(e, (c.get(e) || 0) ^ 1); return [...c].filter(x => x[1]).map(x => x[0]); }
// gcd over F_2 of a sparse H (exponent list, repeated exponents cancel) with X^N - 1
function gcd2(hexpsRaw, N) {
  const hexps = reduceExps(hexpsRaw), dh = Math.max(...hexps);
  const R = p2zero(Math.max(N, dh) + 1); p2flip(R, N); p2flip(R, 0);
  if (N >= dh) p2remSparse(R, N, hexps);
  return p2gcd(p2fromExps(hexps), R);
}
const hK1 = i => [0, i, i + 1];                                       // 1 + X^i (X + 1)      (char 2, c = 1)
const hK2 = (i1, i2) => [0, i1, i1 + 1, i2, i2 + 1];                  // 1 + (X + 1)(X^i1 + X^i2)

// ----------------------------------------------------------------------------------------------
// F_{p^d} with exp/log tables; elements are integers whose base-p digits are polynomial coefficients
// ----------------------------------------------------------------------------------------------
function makeField(p, d) {
  let Q = 1; for (let j = 0; j < d; j++) Q *= p;
  const QM = Q - 1, exp = new Uint32Array(Q), log = new Int32Array(Q), f = new Array(d).fill(0);
  let seed = (12345 + 131 * p + d) >>> 0;
  const rnd = () => { seed = (Math.imul(seed, 1103515245) + 12345) >>> 0; return (seed >>> 8) % p; };
  const top = Q / p;
  let fb = 0;
  const mulx = (p === 2)
    ? e => { e <<= 1; if (e & Q) e ^= (Q | fb); return e; }
    : e => {
        const t = Math.floor(e / top), low = (e % top) * p;
        if (!t) return low;
        let res = 0, pw = 1, x = low;
        for (let j = 0; j < d; j++) { const dg = x % p; x = (x - dg) / p; res += ((dg + p * p - t * f[j]) % p) * pw; pw *= p; }
        return res;
      };
  for (let trial = 0; trial < 1e6; trial++) {
    for (let j = 0; j < d; j++) f[j] = rnd();
    if (f[0] === 0) continue;
    fb = 0; if (p === 2) for (let j = 0; j < d; j++) fb |= f[j] << j;
    let ok = true, e, k;
    if (d === 1) { const g = f[0]; e = 1; for (k = 0; k < QM; k++) { exp[k] = e; e = (e * g) % p; if (e === 1 && k + 1 < QM) { ok = false; break; } } }
    else { e = p; exp[0] = 1; for (k = 1; k < QM; k++) { if (e === 1) { ok = false; break; } exp[k] = e; e = mulx(e); } }
    if (!ok || e !== 1) continue;
    for (k = 0; k < QM; k++) log[exp[k]] = k;
    log[0] = -1;
    break;
  }
  const sub = (p === 2) ? (a, b) => a ^ b : (a, b) => {
    let res = 0, pw = 1;
    for (let j = 0; j < d; j++) { const x = a % p, y = b % p; a = (a - x) / p; b = (b - y) / p; res += ((x + p - y) % p) * pw; pw *= p; }
    return res;
  };
  const mul = (a, b) => (a && b) ? exp[(log[a] + log[b]) % QM] : 0;
  const neg = a => sub(0, a), add = (a, b) => sub(a, sub(0, b));
  const minus1 = e => (e % p) ? e - 1 : e + p - 1;
  return { p, d, Q, QM, exp, log, sub, add, neg, mul, minus1 };
}
// data attached to a prime N | Q - 1:  zeta = g^M,  L[a] = log(zeta^a - 1)
function rootsData(F, N) {
  const M = F.QM / N, L = new Int32Array(N), ell = new Int32Array(N);
  for (let a = 1; a < N; a++) { L[a] = F.log[F.minus1(F.exp[(M * a) % F.QM])]; ell[a] = L[a] % M; }
  return { N, M, L, ell };
}
const logF = (F, D, a, i) => (D.M * ((a * i) % D.N) + D.L[a]) % F.QM;      // log of zeta^{a i}(zeta^a - 1)
// all fibres of z -> z^i (z - 1) on mu_N \ {1}, by direct evaluation
function fibresDirect(F, D, i) {
  const cnt = new Map();
  for (let a = 1; a < D.N; a++) { const l = logF(F, D, a, i); cnt.set(l, (cnt.get(l) || 0) + 1); }
  let best = 0, lam = -1; const hist = new Map();
  for (const [l, c] of cnt) { hist.set(c, (hist.get(c) || 0) + 1); if (c > best) { best = c; lam = l; } }
  return { best, lam, hist, lamInPrimeField: lam >= 0 && lam % (F.QM / (F.p - 1)) === 0 };
}
// exponents a (mod N) of the roots zeta^a of  N + (X - 1) * sum_j c_j X^{i_j}  (c_j field elements)
function rootSet(F, D, is, cs) {
  const target = F.neg(F.exp[0] * 0 + nTimesOne(F, D.N)), Z = [];
  for (let a = 1; a < D.N; a++) {
    let s = 0;
    for (let j = 0; j < is.length; j++) s = F.add(s, F.mul(cs[j], F.exp[logF(F, D, a, is[j])]));
    if (s === target) Z.push(a);
  }
  return Z;
}
function nTimesOne(F, N) { return N % F.p; }                  // N * 1 lies in the prime field: digit 0

// ----------------------------------------------------------------------------------------------
// k = 1: exhaustive maximum fibre for one (field, N), via the collision identity
//   ordered collision pairs for exponent i  <->  b in Z/N \ {0} with ell(b) = ell(r b),  r = 1 + 1/i.
// ----------------------------------------------------------------------------------------------
function k1Max(F, N, countArr) {
  const D = rootsData(F, N), { M, L, ell } = D, QM = F.QM;
  const inv = new Int32Array(N); inv[1] = 1; for (let a = 2; a < N; a++) inv[a] = (N - Math.floor(N / a) * inv[N % a] % N) % N;
  // size of the pair set
  const order = Array.from({ length: N - 1 }, (_, k) => k + 1).sort((x, y) => ell[x] - ell[y] || x - y);
  let sumsq = 0; for (let s = 0; s < N - 1;) { let e = s; while (e < N - 1 && ell[order[e]] === ell[order[s]]) e++; sumsq += (e - s) * (e - s - 1); s = e; }
  let best = 1, bestI = -1, bestLam = -1, pairsMax = 0;
  const consider = (c, i, lam) => { let m = 1; while (m * (m - 1) < c) m++; if (m * (m - 1) !== c) throw new Error('pair count is not m(m-1)'); if (m > best) { best = m; bestI = i; bestLam = lam; } };
  if (sumsq <= 2e7) {
    const keys = new Float64Array(sumsq); let nk = 0;
    for (let s = 0; s < N - 1;) {
      let e = s; while (e < N - 1 && ell[order[e]] === ell[order[s]]) e++;
      for (let x = s; x < e; x++) for (let y = s; y < e; y++) if (x !== y) {
        const b = order[x], bp = order[y], r = (bp * inv[b]) % N, i = inv[(r + N - 1) % N];
        const ew = (((L[b] - L[bp]) % QM + QM) % QM) / M, ll = (M * ((ew * i) % N) + L[ew]) % QM;
        keys[nk++] = i * F.Q + ll;
      }
      s = e;
    }
    keys.sort();
    for (let s = 0; s < nk;) { let e = s; while (e < nk && keys[e] === keys[s]) e++; consider(e - s, Math.floor(keys[s] / F.Q), keys[s] % F.Q); s = e; }
  } else {
    const C = countArr, touched = new Int32Array(N);
    for (let r = 2; r < N; r++) {
      const i = inv[r - 1]; let nt = 0, bp = 0;
      for (let b = 1; b < N; b++) {
        bp += r; if (bp >= N) bp -= N;
        if (ell[b] !== ell[bp]) continue;
        let lw = L[b] - L[bp]; if (lw < 0) lw += QM;
        const ew = lw / M; let ll = M * ((ew * i) % N) + L[ew]; if (ll >= QM) ll -= QM;
        if (C[ll] === 0) touched[nt++] = ll;
        C[ll]++;
      }
      for (let k = 0; k < nt; k++) { const c = C[touched[k]]; C[touched[k]] = 0; consider(c, i, touched[k]); }
    }
  }
  return { N, M, best, i: bestI, lamInPrimeField: best > 1 && bestLam % (QM / (F.p - 1)) === 0 };
}

// ----------------------------------------------------------------------------------------------
// k = 2: exhaustive maximum over (i1, i2, c1, c2), c1 c2 != 0.
//   Points P_a = (A_a, B_a) = ((z-1) z^i1, (z-1) z^i2), z = zeta^a; lines c1' A + c2' B = 1.
// ----------------------------------------------------------------------------------------------
function k2Max(F, N) {
  const D = rootsData(F, N), QM = F.QM, n = N - 1;
  const Al = new Int32Array(N), Bl = new Int32Array(N), Ae = new Int32Array(N), Be = new Int32Array(N);
  const keys = new Float64Array(n * (n - 1) / 2);
  let best = 1, arg = null;
  for (let i1 = 0; i1 < N; i1++) {
    for (let a = 1; a < N; a++) { Al[a] = logF(F, D, a, i1); Ae[a] = F.exp[Al[a]]; }
    for (let i2 = i1 + 1; i2 < N; i2++) {
      for (let a = 1; a < N; a++) { Bl[a] = logF(F, D, a, i2); Be[a] = F.exp[Bl[a]]; }
      let nk = 0;
      for (let a = 1; a < N; a++) for (let b = a + 1; b < N; b++) {
        const dB = F.sub(Be[b], Be[a]); if (!dB) continue;
        const dA = F.sub(Ae[a], Ae[b]); if (!dA) continue;
        const det = F.sub(F.exp[(Al[a] + Bl[b]) % QM], F.exp[(Al[b] + Bl[a]) % QM]); if (!det) continue;
        const ld = F.log[det];
        keys[nk++] = ((F.log[dB] + QM - ld) % QM) * F.Q + ((F.log[dA] + QM - ld) % QM);
      }
      const view = keys.subarray(0, nk); view.sort();
      let run = 0, runKey = -1;
      for (let s = 0; s < nk;) { let e = s; while (e < nk && view[e] === view[s]) e++; if (e - s > run) { run = e - s; runKey = view[s]; } s = e; }
      let m = run ? 2 : 1; while (m * (m - 1) / 2 < run) m++;
      if (m > best) { best = m; arg = { i1, i2, c1log: Math.floor(runKey / F.Q), c2log: runKey % F.Q }; }
    }
  }
  return { best, arg };
}
// tau(s,t) = #{w : w, sw, tw roots} and the two counting identities used in the k = 2 theorem
function tripleStats(Z, N) {
  const inZ = new Uint8Array(N); for (const a of Z) inZ[a] = 1;
  const m = Z.length, r = new Int32Array(N);
  for (let s = 1; s < N; s++) for (const w of Z) if (inZ[(w + s) % N]) r[s]++;
  let maxTau = 0, A1 = 0, A2 = 0, grid = 0, sumR = 0;
  for (let s = 1; s < N; s++) {
    grid += r[s] * (r[s] - 1) * (r[s] - 2); sumR += r[s];
    for (let t = 1; t < N; t++) if (t !== s) {
      let tau = 0; for (const w of Z) if (inZ[(w + s) % N] && inZ[(w + t) % N]) tau++;
      if (tau > maxTau) maxTau = tau; if (tau === 1) A1++; if (tau === 2) A2++;
    }
  }
  return { m, maxTau, ok: maxTau <= 2 && sumR === m * (m - 1) && A1 + 2 * A2 === m * (m - 1) * (m - 2) && grid === 2 * A2 && grid <= m * (m - 1) * (m - 2) };
}

// ==============================================================================================
section('1. The stated example and the ratio lemma');
{
  const g = gcd2(hK1(13), 31);
  check('gcd(1 + X^13 + X^14, X^31 - 1) = X^5 + X^2 + 1 over F_2', p2str(g.poly) === 'X^5 + X^2 + 1', p2str(g.poly));
  // lemma: every pair of distinct roots (w, t w) satisfies (t^{i+1} - 1) w = t^i - 1  (checked in F_32)
  const F = makeField(2, 5), D = rootsData(F, 31), Z = rootSet(F, D, [13], [1]);
  let ok = Z.length === 5;
  const z = a => F.exp[(D.M * (((a % 31) + 31) % 31)) % F.QM];
  for (const a of Z) for (const b of Z) if (a !== b) {
    const t = a - b;                                   // z_a = t z_b
    ok = ok && F.mul(F.sub(z(t * 14), 1), z(b)) === F.sub(z(t * 13), 1);
  }
  check('ratio lemma holds on all 20 ordered pairs of the 5 common roots', ok, 'root exponents ' + Z.join(','));
  check('m(m-1) = 20 <= N - 1 = 30', 20 <= 30);
}

// ==============================================================================================
section('2. Equality m(m-1) = N-1: characteristic 2, N = q^2+q+1, q = 2^e, i = q^2 or q, c = 1');
for (const e of [1, 2, 3, 4, 5, 9]) {
  const q = 2 ** e, n = q * q + q + 1;
  const g1 = gcd2(hK1(q * q), n), g2 = gcd2(hK1(q), n);
  const ok1 = g1.deg === q + 1 && p2exps(g1.poly).join() === [q + 1, 1, 0].join();
  const ok2 = g2.deg === q + 1 && p2exps(g2.poly).join() === [q + 1, q, 0].join();
  const prime = isPrimeBig(n);
  check(`e=${e}: n=${n}${prime ? ' (prime)' : ' (composite; identity still holds)'}: gcd(1+X^{q^2}+X^{q^2+1}, X^n-1) = X^{q+1}+X+1 and gcd(1+X^q+X^{q+1}, X^n-1) = 1+X^q+X^{q+1}`,
    ok1 && ok2 && (q + 1) * q === n - 1, `m=${g1.deg}, m(m-1)=${(q + 1) * q}=n-1`);
}
{
  const fac = { 27: 2593n, 81: 487n, 243: 80191n, 729: 39367n, 2187: 209953n, 6561: 141560137n, 19683: 472393n };
  let ok = [1, 3, 9].every(e => isPrimeBig(4n ** BigInt(e) + 2n ** BigInt(e) + 1n));
  for (const [e, f] of Object.entries(fac)) { const E = BigInt(e); ok = ok && isPrimeBig(f) && (modpow(4n, E, f) + modpow(2n, E, f) + 1n) % f === 0n; }
  check('4^e+2^e+1 is prime for e = 1, 3, 9 (7, 73, 262657) and composite for e = 3^3 .. 3^9 (explicit prime factors)', ok,
    Object.entries(fac).map(([e, f]) => `e=${e}: ${f}`).join('; '));
}

// ==============================================================================================
section('3. Sections of the Singer line: N = (4^e+2^e+1)/7, exact count (2^e + 1 + 3(-1)^(e-1) V_e)/7');
const Vseq = e => { let a = 2n, b = -1n; for (let k = 0; k < e; k++) [a, b] = [b, -b - 2n * a]; return a; };      // V_e = eta^e + conj(eta)^e, eta^2 + eta + 2 = 0
const sub7 = e => (2n ** BigInt(e) + 1n + 3n * (e % 2 ? 1n : -1n) * Vseq(e)) / 7n;
for (const e of FULL ? [2, 4, 5, 7, 8, 10, 11, 13, 14] : [2, 4, 5, 7, 8, 10, 11]) {
  const q = 2 ** e, U = (q * q + q + 1) / 7, g = gcd2(hK1(q), U);
  check(`e=${e}: deg gcd(1 + X^q + X^{q+1}, X^U - 1), U=${U}${isPrime(U) ? ' prime' : ''}`, BigInt(g.deg) === sub7(e), `gcd degree ${g.deg}, closed form ${sub7(e)}`);
}
for (const e of [11, 23, 31]) {
  const N = (4n ** BigInt(e) + 2n ** BigInt(e) + 1n) / 7n, m = sub7(e);
  const ratio = Number(m * (m - 1n) * 100000n / (N - 1n)) / 100000;
  check(`e=${e}: N=${N} is prime; m = ${m} is a multiple of ord_N(2) = ${3 * e}`, isPrimeBig(N) && m % BigInt(3 * e) === 0n && modpow(2n, BigInt(3 * e), N) === 1n && modpow(2n, BigInt(e), N) !== 1n,
    `m(m-1)/(N-1) = ${ratio}  (1/7 = 0.14286)`);
}

// ==============================================================================================
section('4. Frobenius orbits in characteristic 2 (c = 1): Mersenne primes and the rigidity corollary');
for (const [d, i, mExp] of [[5, 13, 5], [7, 6, 7], [13, 17, 13], [17, 12753, 51], [19, 921, 57]]) {
  const N = 2 ** d - 1, g = gcd2(hK1(i), N);
  check(`N=2^${d}-1=${N}: deg gcd(1 + X^${i} + X^${i + 1}, X^N - 1) = ${mExp} (${mExp / d} orbit${mExp > d ? 's' : ''} of size ${d})`, g.deg === mExp, `cap from m(m-1)<=N-1: ${capK1(N)}`);
}
{
  // Corollary: a binary trinomial 1 + X^i + X^{i+1} can meet X^N - 1 only if d = ord_N(2) satisfies d(d-1) <= N-1.
  const hit = [], allowed = [];
  let ok = true;
  for (const N of primesUpTo(700).filter(x => x > 2)) {
    const d = ordMod(2, N); let best = 0;
    for (let i = 1; i <= N - 2; i++) best = Math.max(best, gcd2(hK1(i), N).deg);
    if (d * (d - 1) <= N - 1) allowed.push(`${N}(d=${d})`);
    if (best) { hit.push(`${N}:${best}`); if (d * (d - 1) > N - 1 || best % d !== 0) ok = false; }
  }
  check('odd primes N < 700 with some gcd(1 + X^i + X^{i+1}, X^N - 1) != 1 are exactly 3, 7, 31, 73, 127; each has d(d-1) <= N-1 and degree divisible by d',
    ok && hit.join() === '3:2,7:3,31:5,73:9,127:7', 'N:max degree = ' + hit.join(' '));
  console.log('      primes N < 700 with d(d-1) <= N-1 (the only ones the corollary does not exclude): ' + allowed.join(' '));
}

// ==============================================================================================
section('5. k = 1, all coefficients c: exhaustive maxima over small fields (collision identity)');
{
  const jobs = [];
  for (const p of primesUpTo(4000)) {
    const lim = FULL ? (p === 2 ? 2 ** 26 : p <= 7 ? 2 ** 24 : 2 ** 22) : (p <= 7 ? 2 ** 16 : 2 ** 12);
    for (let d = 1, Q = p; Q <= lim; d++, Q *= p) if (!(p === 2 && d === 1)) jobs.push([Q, p, d]);
  }
  jobs.sort((a, b) => a[0] - b[0]);
  let pairs = 0, viol = 0; const eq = [], distinctN = new Set(), byChar = new Map();
  let transferOK = true, transferCases = 0, primRoot2OK = true, primRoot2Cases = 0, rigidOK = true;
  const char2Big = [], char2Two = [];
  for (const [Q, p, d] of jobs) {
    const Ns = primeFactors(Q - 1).filter(N => N !== p && N >= 3 && ordMod(p, N) === d && (FULL ? N <= 140000 : N <= 9000));
    if (!Ns.length) continue;
    const F = makeField(p, d), C = new Uint16Array(Q);
    for (const N of Ns) {
      const R = k1Max(F, N, C); pairs++; distinctN.add(N);
      const m = R.best;
      if (m * (m - 1) > N - 1) viol++;
      if (m >= 2 && m * (m - 1) === N - 1) eq.push(`(p=${p},N=${N},m=${m},i=${R.i})`);
      if (R.lamInPrimeField && m % d !== 0) rigidOK = false;
      const cur = byChar.get(p); if (!cur || m > cur.m) byChar.set(p, { m, N, d });
      if (p === 2) (m >= 3 ? char2Big : char2Two).push(m >= 3 ? `${N}:${m}` : N);
      if (N >= 5 && d * Math.log(p) >= (N - 1) * Math.log(3) - 1e-9) { transferCases++; if (m > 1) transferOK = false; }
      if (p === 2 && N >= 5 && d === N - 1) { primRoot2Cases++; if (m !== 2) primRoot2OK = false; }
    }
  }
  check(`sweep over ${pairs} pairs (p, N), ${distinctN.size} distinct primes N: m(m-1) <= N-1 never violated`, viol === 0);
  check('equality m(m-1) = N-1 occurs only for p = 2, N in {3, 7, 73}', eq.length === 3 && eq.every(s => s.startsWith('(p=2,')) && ['N=3,', 'N=7,', 'N=73,'].every(t => eq.some(s => s.includes(t))), eq.join(' '));
  check('fibres over the prime field have size divisible by ord_N(p)', rigidOK);
  check(`p^ord_N(p) >= 3^(N-1), N >= 5  =>  all fibres are singletons (${transferCases} cases)`, transferOK && transferCases > 0);
  check(`p = 2 a primitive root mod N >= 5  =>  largest fibre is exactly 2 (${primRoot2Cases} cases)`, primRoot2OK && primRoot2Cases > 0);
  console.log(`      characteristic 2: ${char2Big.length + char2Two.length} primes N in range; largest fibre is exactly 2 for ${char2Two.length} of them; the others (N:max) are ${char2Big.join(' ')}`);
  console.log('      largest fibre by characteristic: ' + [...byChar].sort((a, b) => a[0] - b[0]).slice(0, 8).map(([p, v]) => `p=${p}: m=${v.m} at N=${v.N}`).join('; '));
}

// ==============================================================================================
section('6. k = 2: structure lemma, bounds, exact maxima');
{
  // explicit examples over F_2 (c1 = c2 = 1): H = 1 + (X+1)(X^i1 + X^i2)
  for (const [N, d, i1, i2, mExp] of [[5, 4, 1, 3, 4], [17, 8, 6, 10, 8], [31, 5, 2, 24, 10], [73, 9, 0, 9, 9], [89, 11, 3, 72, 11], [127, 7, 1, 56, 14], [151, 15, 5, 50, 15]]) {
    const g = gcd2(hK2(i1, i2), N), F = makeField(2, d), D = rootsData(F, N), Z = rootSet(F, D, [i1, i2], [1, 1]), st = tripleStats(Z, N);
    check(`N=${N}: deg gcd(1 + (X+1)(X^${i1} + X^${i2}), X^N - 1) = ${mExp}; any three translates of the root set share <= 2 points; counting identities hold`,
      g.deg === mExp && Z.length === mExp && st.ok, `max triple intersection ${st.maxTau}; cap ${capK2(N)}`);
  }
  // coefficients in F_4 \ F_2
  for (const [N, d, i1, i2, e1, e2, mExp] of [[11, 10, 2, 8, 1, 2, 5], [43, 14, 4, 38, 1, 2, 7], [257, 16, 120, 136, 1, 1, 24]]) {
    const F = makeField(2, d), D = rootsData(F, N), w = F.exp[F.QM / 3];
    const Z = rootSet(F, D, [i1, i2], [e1 === 1 ? w : F.mul(w, w), e2 === 1 ? w : F.mul(w, w)]), st = tripleStats(Z, N);
    check(`N=${N}, c1 = w${e1 === 2 ? '^2' : ''}, c2 = w${e2 === 2 ? '^2' : ''} (w^2+w+1=0), (i1,i2)=(${i1},${i2}): ${mExp} common roots; triple intersections <= 2`, Z.length === mExp && st.ok, `cap ${capK2(N)}`);
  }
  { // characteristic 3: H = 13 + (X-1)(2 X^3 + X^9) over F_3
    const F = makeField(3, 3), D = rootsData(F, 13), Z = rootSet(F, D, [3, 9], [2, 1]), st = tripleStats(Z, 13);
    check('N=13 over F_3: 13 + (X-1)(2X^3 + X^9) has 6 roots in mu_13; triple intersections <= 2', Z.length === 6 && st.ok, `cap ${capK2(13)}`);
  }
  // exhaustive maxima
  const expected = [[2, 4, 5, 4], [2, 3, 7, 3], [2, 10, 11, 5], [3, 5, 11, 5], [23, 1, 11, 4], [2, 12, 13, 4], [3, 3, 13, 6], [2, 8, 17, 8], [2, 18, 19, 3], [7, 3, 19, 4], [2, 5, 31, 10], [5, 3, 31, 6]]
    .concat(FULL ? [[2, 14, 43, 7], [7, 6, 43, 6], [2, 9, 73, 9], [2, 11, 89, 11], [2, 7, 127, 14], [2, 15, 151, 15], [2, 16, 257, 24]] : []);
  const rows = [];
  let allOK = true;
  for (const [p, d, N, mExp] of expected) {
    const F = makeField(p, d), R = k2Max(F, N), cap = capK2(N);
    if (R.best !== mExp || R.best > cap) allOK = false;
    rows.push(`(p=${p},N=${N}): ${R.best}/${cap}`);
  }
  check('exhaustive k = 2 maxima over all (i1, i2, c1, c2) agree with the table and never exceed the cap', allOK, 'exact max / cap: ' + rows.join('  '));
  check('the cap is attained at N = 5 and N = 17 (characteristic 2)', capK2(5) === 4 && capK2(17) === 8);
  let ok = true; for (const N of primesUpTo(5000)) if (N >= 5 && capK2(N) >= Math.cbrt(N) ** 2 + Math.cbrt(N) + 1) ok = false;
  check('cap < N^(2/3) + N^(1/3) + 1 for all primes 5 <= N < 5000', ok);
}

// ==============================================================================================
section('7. Odd characteristic');
{
  const cases = [[3, 3, 13, 4, 3, 'ord_13(3) = 3'], [23, 1, 11, 2, 3, 'prime field F_23'], [17, 5, 88741, 83537, 20, '4 Frobenius orbits; N = (17^5-1)/16']];
  for (const [p, d, N, i, mExp, note] of cases) {
    const F = makeField(p, d), D = rootsData(F, N), R = fibresDirect(F, D, i);
    check(`p=${p}, N=${N}, i=${i}: largest fibre of z -> z^i(z-1) on mu_N is ${mExp}`, R.best === mExp && R.best * (R.best - 1) < N - 1, note + `; m(m-1)/(N-1) = ${(mExp * (mExp - 1) / (N - 1)).toFixed(4)}`);
  }
  // projective lines of PG(4,q) as fibres: N = (q^5-1)/(q-1) prime, i = q^r, fibre sizes in {0, 1, q+1}
  for (const [q, N] of FULL ? [[7, 2801], [13, 30941], [17, 88741]] : [[7, 2801], [13, 30941]]) {
    const F = makeField(q, 5), D = rootsData(F, N); let ok = true, lines = 0;
    for (let r = 1; r <= 4; r++) { const R = fibresDirect(F, D, (q ** r) % N); for (const [size, cnt] of R.hist) { if (size !== 1 && size !== q + 1) ok = false; if (size === q + 1) lines += cnt; } }
    check(`q=${q}, N=${N}: for i = q, q^2, q^3, q^4 every fibre has size 1 or q+1 = ${q + 1}`, ok && lines > 0, `${lines} fibres of size ${q + 1}; N^(1/4) = ${(N ** 0.25).toFixed(1)}`);
  }
  // N = q^2+q+1 in odd characteristic: i = q, q^2 give no collisions at all
  for (const [q, d, N] of [[3, 3, 13], [5, 3, 31], [17, 3, 307], [27, 9, 757]]) {
    const p = primeFactors(q)[0], F = makeField(p, d), D = rootsData(F, N);
    check(`q=${q}, N=${N}=q^2+q+1: z -> z^i(z-1) is injective on mu_N for i = q and i = q^2`, fibresDirect(F, D, q % N).best === 1 && fibresDirect(F, D, (q * q) % N).best === 1);
  }
}

// ==============================================================================================
section('8. A vanishing minor of the Fourier matrix of order 7 over F_8 (Chebotarev fails in characteristic 2)');
{
  const F = makeField(2, 3), z = k => F.exp[((k % 7) + 7) % 7];
  const det3 = M => { const [a, b, c] = M[0], [d, e, f] = M[1], [g, h, i] = M[2]; const m = F.mul, x = F.add;
    return x(x(m(a, x(m(e, i), m(f, h))), m(b, x(m(d, i), m(f, g)))), m(c, x(m(d, h), m(e, g)))); };
  const Z = rootSet(F, rootsData(F, 7), [4], [1]);                              // roots of 1 + X^4 + X^5 in mu_7
  const minor = [0, 4, 5].map(r => Z.map(a => z(r * a)));
  check('rows {0,4,5}, columns = the three common roots of 1 + X^4 + X^5 and X^7 - 1: determinant 0', Z.length === 3 && det3(minor) === 0, 'columns zeta^a, a = ' + Z.join(','));
  check('|supp f| + |supp f^| = 3 + 4 = 7 < N + 1 = 8 for f = coefficient vector of 1 + X^4 + X^5', 3 + (7 - Z.length) === 7);
}

console.log(`\n${passes} checks passed, ${failures} failed.` + (FULL ? '' : '  (run with --full for the large sweeps)'));
process.exit(failures ? 1 : 0);
