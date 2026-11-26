#!/usr/bin/env node
// verify.mjs — dependency-free checker for the order-N interpolation-obstruction certificate.
//
//   node verify.mjs [certificate.json] [orders...]        (default orders: 7 11 13 17)
//
// Everything is recomputed here from the stated model, in exact BigInt arithmetic:
//   R      = Z[t][r]/(f)              (f monic in r, rank d over Z[t])
//   R_loc  = R[1/(t(t-1))]            (t and t-1 divide the recurrence denominator x_5 = r t (t-1))
//   recurrence for (x_i, y_i), A_i, lambda_i = 1/A_i, H, u_i = (H lambda)_i / lambda_i.
// The only data taken from the certificate file are
//   * the Bezout cofactors W_i and the integer n0 with  sum_i W_i P_i = n0,
//   * for each prime p | n0, the irreducible factors of gcd_i(P_i mod p) and the roots of the fibre gcd.
// The g_i and P_i stored in the file (computed independently with PARI) are only compared against
// the values recomputed here.

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const certPath = args.length && !/^\d+$/.test(args[0]) ? args.shift() : join(here, 'certificate.json');
const ORDERS = args.length ? args.map(Number) : [7, 11, 13, 17];
const CERT = JSON.parse(readFileSync(certPath, 'utf8'));

let failures = 0;
function check(label, cond) {
  if (!cond) failures++;
  console.log(`  [${cond ? 'ok' : 'FAIL'}] ${label}`);
  return cond;
}

// ---------------------------------------------------------------------------------------------
// Z[t]: arrays of BigInt, low degree first, no trailing zeros ([] is 0)
// ---------------------------------------------------------------------------------------------
function ztrim(a) { let n = a.length; while (n > 0 && a[n - 1] === 0n) n--; a.length = n; return a; }
const zfrom = (arr) => ztrim(arr.map((x) => BigInt(x)));
const zconst = (k) => (BigInt(k) === 0n ? [] : [BigInt(k)]);
function zadd(a, b) {
  const n = Math.max(a.length, b.length), c = new Array(n);
  for (let i = 0; i < n; i++) c[i] = (i < a.length ? a[i] : 0n) + (i < b.length ? b[i] : 0n);
  return ztrim(c);
}
function zsub(a, b) {
  const n = Math.max(a.length, b.length), c = new Array(n);
  for (let i = 0; i < n; i++) c[i] = (i < a.length ? a[i] : 0n) - (i < b.length ? b[i] : 0n);
  return ztrim(c);
}
const zneg = (a) => a.map((x) => -x);
function zmul(a, b) {
  if (!a.length || !b.length) return [];
  const c = new Array(a.length + b.length - 1).fill(0n);
  for (let i = 0; i < a.length; i++) {
    const ai = a[i];
    if (ai === 0n) continue;
    for (let j = 0; j < b.length; j++) c[i + j] += ai * b[j];
  }
  return ztrim(c);
}
const zscal = (a, k) => (k === 0n ? [] : a.map((x) => x * k));
function zeq(a, b) {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}
const zshift = (a, k) => (a.length && k > 0 ? new Array(k).fill(0n).concat(a) : a.slice());
function zmulT1(a) { // (t-1) * a
  if (!a.length) return [];
  const c = new Array(a.length + 1).fill(0n);
  for (let i = 0; i < a.length; i++) { c[i + 1] += a[i]; c[i] -= a[i]; }
  return ztrim(c);
}
const zeval1 = (a) => a.reduce((s, x) => s + x, 0n);
function zdivT1(a) { // exact division by (t-1); null if not divisible
  if (!a.length) return [];
  const n = a.length - 1, q = new Array(n);
  let carry = 0n;
  for (let i = n; i >= 1; i--) { carry = a[i] + carry; q[i - 1] = carry; }
  if (a[0] + (n >= 1 ? q[0] : 0n) !== 0n) return null;
  return ztrim(q);
}
function zdivInt(a, k) { // exact division by a nonzero integer; null if not exact
  const q = new Array(a.length);
  for (let i = 0; i < a.length; i++) { if (a[i] % k !== 0n) return null; q[i] = a[i] / k; }
  return q;
}
const zdeg = (a) => a.length - 1;
function zstr(a) {
  if (!a.length) return '0';
  const parts = [];
  for (let i = a.length - 1; i >= 0; i--) {
    if (a[i] === 0n) continue;
    const s = a[i] < 0n ? '-' : '+', v = a[i] < 0n ? -a[i] : a[i];
    const mon = i === 0 ? '' : i === 1 ? 't' : `t^${i}`;
    parts.push(`${s} ${v === 1n && i > 0 ? '' : v + (i > 0 ? '*' : '')}${mon}`);
  }
  return parts.join(' ').replace(/^\+ /, '').replace(/^- /, '-');
}
// strip all factors t and (t-1): a = t^e0 (t-1)^e1 * q
function zstrip(a) {
  let q = a.slice(), e0 = 0, e1 = 0;
  if (!q.length) throw new Error('zstrip(0)');
  while (q[0] === 0n) { q = q.slice(1); e0++; }
  while (zeval1(q) === 0n) { q = zdivT1(q); e1++; }
  return { q, e0, e1 };
}

// ---------------------------------------------------------------------------------------------
// Z[t][r] (free bivariate polynomials, used only to build f from its definition)
// ---------------------------------------------------------------------------------------------
function btrim(A) { let n = A.length; while (n > 0 && A[n - 1].length === 0) n--; A.length = n; return A; }
const B = {
  r: [[], [1n]],
  t: [[0n, 1n]],
  c: (k) => btrim([zconst(k)]),
  add(a, b) { const n = Math.max(a.length, b.length), c = []; for (let i = 0; i < n; i++) c.push(zadd(a[i] ?? [], b[i] ?? [])); return btrim(c); },
  sub(a, b) { const n = Math.max(a.length, b.length), c = []; for (let i = 0; i < n; i++) c.push(zsub(a[i] ?? [], b[i] ?? [])); return btrim(c); },
  mul(a, b) {
    if (!a.length || !b.length) return [];
    const c = Array.from({ length: a.length + b.length - 1 }, () => []);
    for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) c[i + j] = zadd(c[i + j], zmul(a[i], b[j]));
    return btrim(c);
  },
  pow(a, k) { let res = B.c(1); for (let i = 0; i < k; i++) res = B.mul(res, a); return res; },
};
function definingPolynomial(N) {
  const { r, t } = B, one = B.c(1);
  const h = B.add(B.sub(B.mul(r, t), B.mul(B.c(2), r)), one);                       // rt - 2r + 1
  const j = B.sub(B.add(B.sub(r, B.mul(t, t)), t), one);                              // r - t^2 + t - 1
  const k = B.add(B.add(B.sub(B.mul(r, B.mul(t, t)), B.mul(B.c(3), B.mul(r, t))), r), B.mul(t, t)); // rt^2 - 3rt + r + t^2
  switch (N) {
    case 17: return B.sub(B.mul(B.mul(r, B.sub(r, t)), B.pow(j, 3)), B.mul(B.mul(t, B.pow(h, 3)), k)); // r(r-t)j^3 - t h^3 k
    case 13: return B.sub(B.pow(B.sub(r, t), 3), B.mul(B.mul(r, B.pow(B.sub(t, one), 3)), h));          // (r-t)^3 - r(t-1)^3 h
    case 11: { // r^2 - (t^3 - 3t^2 + 4t) r + t
      const q = B.add(B.sub(B.pow(t, 3), B.mul(B.c(3), B.pow(t, 2))), B.mul(B.c(4), t));
      return B.add(B.sub(B.mul(r, r), B.mul(q, r)), t);
    }
    case 7: return B.sub(r, t);
    default: throw new Error(`no model for N=${N}`);
  }
}

// ---------------------------------------------------------------------------------------------
// R = Z[t][r]/(f): elements are arrays of d polynomials in Z[t] (coefficients of 1, r, ..., r^(d-1))
// ---------------------------------------------------------------------------------------------
class Ring {
  constructor(f) {
    this.d = f.length - 1;
    const d = this.d;
    if (!(f[d].length === 1 && f[d][0] === 1n)) throw new Error('f is not monic in r');
    this.red = []; // red[k] = r^(d+k) mod f, k = 0..d-2
    let cur = f.slice(0, d).map(zneg);
    this.red.push(cur);
    for (let k = 1; k <= d - 2; k++) {
      const top = cur[d - 1], nxt = new Array(d);
      nxt[0] = zmul(top, this.red[0][0]);
      for (let i = 1; i < d; i++) nxt[i] = zadd(cur[i - 1], zmul(top, this.red[0][i]));
      this.red.push(nxt);
      cur = nxt;
    }
    this.rClass = d === 1 ? [zneg(f[0])] : Array.from({ length: d }, (_, i) => (i === 1 ? [1n] : []));
    // traces of the basis: tr(r^k)
    this.tau = [zconst(d)];
    for (let k = 1; k < d; k++) {
      let s = [];
      for (let jj = d - k; jj < d; jj++) s = zadd(s, this.red[k + jj - d][jj]);
      this.tau.push(s);
    }
  }
  zero() { return Array.from({ length: this.d }, () => []); }
  fromZ(z) { const a = this.zero(); a[0] = z.slice(); return a; }
  one() { return this.fromZ([1n]); }
  add(a, b) { return a.map((c, i) => zadd(c, b[i])); }
  sub(a, b) { return a.map((c, i) => zsub(c, b[i])); }
  neg(a) { return a.map(zneg); }
  scal(a, z) { return a.map((c) => zmul(c, z)); }
  isZero(a) { return a.every((c) => c.length === 0); }
  eq(a, b) { return a.every((c, i) => zeq(c, b[i])); }
  mul(a, b) {
    const d = this.d, c = Array.from({ length: 2 * d - 1 }, () => []);
    for (let i = 0; i < d; i++) {
      if (!a[i].length) continue;
      for (let jj = 0; jj < d; jj++) if (b[jj].length) c[i + jj] = zadd(c[i + jj], zmul(a[i], b[jj]));
    }
    const res = c.slice(0, d);
    for (let m = d; m <= 2 * d - 2; m++) {
      if (!c[m].length) continue;
      const rd = this.red[m - d];
      for (let i = 0; i < d; i++) if (rd[i].length) res[i] = zadd(res[i], zmul(c[m], rd[i]));
    }
    return res;
  }
  trace(a) { let s = []; for (let k = 0; k < this.d; k++) s = zadd(s, zmul(a[k], this.tau[k])); return s; }
  // Faddeev–LeVerrier in the algebra: returns adj, norm with  a * adj = norm  (norm = N_{R/Z[t]}(a) in Z[t])
  adjNorm(a) {
    const d = this.d;
    let nu = this.one(), ck = null, anu = null;
    for (let k = 1; k <= d; k++) {
      anu = this.mul(a, nu);
      ck = zdivInt(zneg(this.trace(anu)), BigInt(k));
      if (ck === null) throw new Error('inexact division in Faddeev-LeVerrier');
      if (k < d) nu = this.add(anu, this.fromZ(ck));
    }
    if (!this.eq(anu, this.fromZ(zneg(ck)))) throw new Error('Cayley-Hamilton check failed');
    const sgn = d % 2 === 0 ? 1n : -1n; // (-1)^d
    const norm = zscal(ck, sgn), adj = nu.map((c) => zscal(c, -sgn));
    if (!this.eq(this.mul(a, adj), this.fromZ(norm))) throw new Error('adjugate check failed');
    return { adj, norm };
  }
  // matrix of multiplication by a on the basis 1, r, ..., r^(d-1): column j holds the coordinates of a * r^j
  mulMatrix(a) {
    const d = this.d, cols = [];
    let cur = a;
    for (let j = 0; j < d; j++) {
      cols.push(cur);
      if (j < d - 1) cur = this.mul(cur, this.rClass);
    }
    return Array.from({ length: d }, (_, i) => Array.from({ length: d }, (_, j) => cols[j][i]));
  }
  bidegree(a) {
    let dr = -1, dt = -1;
    a.forEach((c, i) => { if (c.length) { dr = i; dt = Math.max(dt, c.length - 1); } });
    return [dr, dt];
  }
}

// ---------------------------------------------------------------------------------------------
// R_loc = R[1/(t(t-1))]: { num in R, a, b } stands for num / (t^a (t-1)^b)
// ---------------------------------------------------------------------------------------------
class Loc {
  constructor(R) { this.R = R; }
  norm(x) {
    let { num, a, b } = x;
    if (this.R.isZero(num)) return { num, a: 0, b: 0 };
    while (a > 0 && num.every((c) => c.length === 0 || c[0] === 0n)) { num = num.map((c) => c.slice(1)); a--; }
    while (b > 0 && num.every((c) => zeval1(c) === 0n)) { num = num.map((c) => zdivT1(c)); b--; }
    return { num, a, b };
  }
  fromR(num) { return { num, a: 0, b: 0 }; }
  int(k) { return this.fromR(this.R.fromZ(zconst(k))); }
  scaleNum(x, A, Bq) { // numerator of x over the denominator t^A (t-1)^Bq  (A >= x.a, Bq >= x.b)
    let num = x.num;
    if (A > x.a) num = num.map((c) => zshift(c, A - x.a));
    for (let i = x.b; i < Bq; i++) num = num.map(zmulT1);
    return num;
  }
  add(x, y) {
    const A = Math.max(x.a, y.a), Bq = Math.max(x.b, y.b);
    return this.norm({ num: this.R.add(this.scaleNum(x, A, Bq), this.scaleNum(y, A, Bq)), a: A, b: Bq });
  }
  neg(x) { return { num: this.R.neg(x.num), a: x.a, b: x.b }; }
  sub(x, y) { return this.add(x, this.neg(y)); }
  mul(x, y) { return this.norm({ num: this.R.mul(x.num, y.num), a: x.a + y.a, b: x.b + y.b }); }
  eq(x, y) {
    const A = Math.max(x.a, y.a), Bq = Math.max(x.b, y.b);
    return this.R.eq(this.scaleNum(x, A, Bq), this.scaleNum(y, A, Bq));
  }
  isZero(x) { return this.R.isZero(x.num); }
  // inverse; throws unless x is a unit of R_loc, i.e. N(num) = ± t^A (t-1)^B
  inv(x) {
    const { adj, norm } = this.R.adjNorm(x.num);
    if (!norm.length) throw new Error('zero divisor');
    const { q, e0, e1 } = zstrip(norm);
    if (!(q.length === 1 && (q[0] === 1n || q[0] === -1n))) throw new Error('not a unit of R_loc: norm = ' + zstr(norm));
    let num = adj.map((c) => zscal(c, q[0]));
    num = this.scaleNum({ num, a: 0, b: 0 }, x.a, x.b);
    const res = this.norm({ num, a: e0, b: e1 });
    if (!this.eq(this.mul(x, res), this.int(1))) throw new Error('inverse check failed');
    return res;
  }
}

// ---------------------------------------------------------------------------------------------
// The stated model in R_loc
// ---------------------------------------------------------------------------------------------
function buildModel(N, f) {
  const n = (N - 1) / 2;
  const R = new Ring(f), L = new Loc(R);
  const tZ = [0n, 1n];
  const r = L.fromR(R.rClass), t = L.fromR(R.fromZ(tZ)), one = L.int(1);
  const rm1 = L.sub(r, one);
  const b = L.mul(L.mul(r, t), rm1), c = L.mul(t, rm1);
  const a1 = L.sub(one, c);
  const X = [null, L.int(0), b], Y = [null, L.int(0), L.mul(b, c)];
  for (let i = 2; i <= n; i++) {
    const m = L.mul(Y[i], L.inv(X[i])); // x_i is a unit of R_loc (inv throws otherwise)
    X[i + 1] = L.sub(L.add(L.add(L.mul(m, m), L.mul(a1, m)), b), X[i]);
    Y[i + 1] = L.sub(b, L.mul(L.add(m, a1), X[i + 1]));
  }
  const orderEq = L.eq(X[n], X[n + 1]);
  const xx = (k) => { const kk = ((k % N) + N) % N; return kk === 0 ? L.int(0) : kk > n ? X[N - kk] : X[kk]; };
  const xp = [null], A = [null], lam = [null];
  for (let i = 1; i <= n; i++) xp[i] = L.sub(L.add(L.mul(L.int(2), Y[i]), L.mul(a1, X[i])), b);
  const dinv = {}; // inverses of x_i - x_j, i < j
  for (let i = 1; i <= n; i++) for (let j = i + 1; j <= n; j++) dinv[`${i},${j}`] = L.inv(L.sub(X[i], X[j]));
  const xpinv = [null];
  for (let i = 1; i <= n; i++) xpinv[i] = L.inv(xp[i]);
  for (let i = 1; i <= n; i++) {
    let Ai = xp[i], li = xpinv[i];
    for (let j = 1; j <= n; j++) {
      if (j === i) continue;
      Ai = L.mul(Ai, L.sub(X[i], X[j]));
      li = L.mul(li, i < j ? dinv[`${i},${j}`] : L.neg(dinv[`${j},${i}`]));
    }
    A[i] = Ai; lam[i] = li;
  }
  const lamOK = A.slice(1).every((Ai, idx) => L.eq(L.mul(Ai, lam[idx + 1]), one));
  const u = [null];
  for (let i = 1; i <= n; i++) {
    let s = L.int(0);
    for (let j = 1; j <= n; j++) s = L.add(s, L.mul(L.sub(xx(i + j), xx(i - j)), lam[j]));
    u[i] = L.mul(s, A[i]); // (H lambda)_i / lambda_i
  }
  // structural identity (not used in the proof): 8(u_i - u_1) = (E_i^2 - 4N x_i) - (E_1^2 - 4N x_1),
  // E_i = 2 e_1(iP) = -2 x'_i sum_{j != i} 1/(x_i - x_j) - x''_i / x'_i
  const a2 = L.neg(b), a3 = L.neg(b);
  const b2 = L.add(L.mul(a1, a1), L.mul(L.int(4), a2)), b4 = L.mul(a1, a3);
  const Tq = [null];
  for (let i = 1; i <= n; i++) {
    let s = L.int(0);
    for (let j = 1; j <= n; j++) if (j !== i) s = L.add(s, i < j ? dinv[`${i},${j}`] : L.neg(dinv[`${j},${i}`]));
    const xpp = L.add(L.add(L.mul(L.int(6), L.mul(X[i], X[i])), L.mul(b2, X[i])), b4);
    const E = L.neg(L.add(L.mul(L.mul(L.int(2), xp[i]), s), L.mul(xpp, xpinv[i])));
    Tq[i] = L.sub(L.mul(E, E), L.mul(L.int(4 * N), X[i]));
  }
  let structOK = true;
  for (let i = 2; i <= n; i++) structOK = structOK && L.eq(L.mul(L.int(8), L.sub(u[i], u[1])), L.sub(Tq[i], Tq[1]));
  return { n, R, L, X, Y, A, lam, u, orderEq, lamOK, structOK };
}

// ---------------------------------------------------------------------------------------------
// Finite fields F_q = F_p[tau]/(phi) (phi monic over F_p; elements: Number arrays of length m)
// and polynomials over them (arrays of field elements, low degree first)
// ---------------------------------------------------------------------------------------------
class Fq {
  constructor(p, phi) { this.p = p; this.phi = phi.map((x) => ((x % p) + p) % p); this.m = phi.length - 1; }
  zero() { return new Array(this.m).fill(0); }
  int(k) { const a = this.zero(); a[0] = Number(((BigInt(k) % BigInt(this.p)) + BigInt(this.p)) % BigInt(this.p)); return a; }
  one() { return this.int(1); }
  tau() { if (this.m === 1) return [(this.p - this.phi[0]) % this.p]; const a = this.zero(); a[1] = 1; return a; }
  add(a, b) { return a.map((x, i) => (x + b[i]) % this.p); }
  sub(a, b) { return a.map((x, i) => (x - b[i] + this.p) % this.p); }
  neg(a) { return a.map((x) => (this.p - x) % this.p); }
  isZero(a) { return a.every((x) => x === 0); }
  eq(a, b) { return a.every((x, i) => x === b[i]); }
  mul(a, b) {
    const m = this.m, p = this.p, c = new Array(2 * m - 1).fill(0);
    for (let i = 0; i < m; i++) { if (!a[i]) continue; for (let j = 0; j < m; j++) c[i + j] = (c[i + j] + a[i] * b[j]) % p; }
    for (let i = 2 * m - 2; i >= m; i--) {
      const co = c[i];
      if (!co) continue;
      c[i] = 0;
      for (let j = 0; j < m; j++) c[i - m + j] = (c[i - m + j] + (p - co) * this.phi[j]) % p;
    }
    return c.slice(0, m);
  }
  pow(a, e) { let res = this.one(), base = a; e = BigInt(e); while (e > 0n) { if (e & 1n) res = this.mul(res, base); base = this.mul(base, base); e >>= 1n; } return res; }
  inv(a) { if (this.isZero(a)) throw new Error('division by zero'); return this.pow(a, BigInt(this.p) ** BigInt(this.m) - 2n); }
  fromZPoly(z) { // evaluate an element of Z[t] at t = tau
    let acc = this.zero();
    const tau = this.tau();
    for (let i = z.length - 1; i >= 0; i--) acc = this.add(this.mul(acc, tau), this.int(z[i]));
    return acc;
  }
  str(a) {
    if (this.m === 1) return String(a[0]);
    const parts = a.map((x, i) => (x ? (i === 0 ? `${x}` : `${x === 1 ? '' : x}${i > 1 ? `τ^${i}` : 'τ'}`) : '')).filter(Boolean);
    return parts.length === 0 ? '0' : parts.length === 1 ? parts[0] : '(' + parts.join(' + ') + ')';
  }
}
const P = { // polynomials over a field K
  trim(K, a) { let n = a.length; while (n > 0 && K.isZero(a[n - 1])) n--; return a.slice(0, n); },
  add(K, a, b) { const n = Math.max(a.length, b.length), c = []; for (let i = 0; i < n; i++) c.push(K.add(a[i] ?? K.zero(), b[i] ?? K.zero())); return P.trim(K, c); },
  sub(K, a, b) { const n = Math.max(a.length, b.length), c = []; for (let i = 0; i < n; i++) c.push(K.sub(a[i] ?? K.zero(), b[i] ?? K.zero())); return P.trim(K, c); },
  mul(K, a, b) {
    if (!a.length || !b.length) return [];
    const c = Array.from({ length: a.length + b.length - 1 }, () => K.zero());
    for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) c[i + j] = K.add(c[i + j], K.mul(a[i], b[j]));
    return P.trim(K, c);
  },
  monic(K, a) { if (!a.length) return a; const li = K.inv(a[a.length - 1]); return a.map((x) => K.mul(x, li)); },
  rem(K, a, b) {
    a = a.slice();
    const db = b.length - 1, li = K.inv(b[db]);
    for (let i = a.length - 1; i >= db; i--) {
      if (K.isZero(a[i])) continue;
      const q = K.mul(a[i], li);
      for (let j = 0; j <= db; j++) a[i - db + j] = K.sub(a[i - db + j], K.mul(q, b[j]));
    }
    return P.trim(K, a.slice(0, db));
  },
  gcd(K, a, b) { a = P.trim(K, a); b = P.trim(K, b); while (b.length) { const r = P.rem(K, a, b); a = b; b = r; } return P.monic(K, a); },
  eq(K, a, b) { return a.length === b.length && a.every((x, i) => K.eq(x, b[i])); },
  eval(K, a, x) { let acc = K.zero(); for (let i = a.length - 1; i >= 0; i--) acc = K.add(K.mul(acc, x), a[i]); return acc; },
  pow(K, a, e) { let res = [K.one()]; for (let i = 0; i < e; i++) res = P.mul(K, res, a); return res; },
};
// Rabin irreducibility test for a monic phi over F_p
function isIrreducible(p, phi) {
  const m = phi.length - 1;
  if (m === 1) return true;
  const Q = new Fq(p, phi), Fp = new Fq(p, [0, 1]);
  const frob = (a) => Q.pow(a, p);
  const tau = Q.tau();
  const iter = (k) => { let a = tau; for (let i = 0; i < k; i++) a = frob(a); return a; };
  if (!Q.eq(iter(m), tau)) return false;
  const primes = []; let mm = m;
  for (let l = 2; l <= mm; l++) if (mm % l === 0) { primes.push(l); while (mm % l === 0) mm /= l; }
  const lift = (a) => a.map((x) => [x]);
  for (const l of primes) {
    const g = P.gcd(Fp, lift(phi), P.trim(Fp, lift(Q.sub(iter(m / l), tau))));
    if (g.length !== 1) return false;
  }
  return true;
}
// Evaluate the stated model at a point (rho, tau) of a field K, straight from the definitions.
function evalModel(K, N, rho, tau) {
  const n = (N - 1) / 2, one = K.one(), I = (k) => K.int(k);
  const b = K.mul(K.mul(rho, tau), K.sub(rho, one)), c = K.mul(tau, K.sub(rho, one));
  const a1 = K.sub(one, c), a2 = K.neg(b), a3 = K.neg(b);
  const b2 = K.add(K.mul(a1, a1), K.mul(I(4), a2)), b4 = K.mul(a1, a3), b6 = K.mul(a3, a3), b8 = K.mul(a2, K.mul(a3, a3));
  // disc = -b2^2 b8 - 8 b4^3 - 27 b6^2 + 9 b2 b4 b6 ;  c4 = b2^2 - 24 b4
  let disc = K.neg(K.mul(K.mul(b2, b2), b8));
  disc = K.sub(disc, K.mul(I(8), K.mul(b4, K.mul(b4, b4))));
  disc = K.sub(disc, K.mul(I(27), K.mul(b6, b6)));
  disc = K.add(disc, K.mul(I(9), K.mul(b2, K.mul(b4, b6))));
  const c4 = K.sub(K.mul(b2, b2), K.mul(I(24), b4));
  const X = [null, K.zero(), b], Y = [null, K.zero(), K.mul(b, c)];
  for (let i = 2; i <= n; i++) {
    if (K.isZero(X[i])) return { defined: false, reason: `x_${i} = 0`, disc, c4 };
    const m = K.mul(Y[i], K.inv(X[i]));
    X[i + 1] = K.sub(K.add(K.add(K.mul(m, m), K.mul(a1, m)), b), X[i]);
    Y[i + 1] = K.sub(b, K.mul(K.add(m, a1), X[i + 1]));
  }
  const orderEq = K.eq(X[n], X[n + 1]);
  const A = [null], lam = [null];
  for (let i = 1; i <= n; i++) {
    let Ai = K.sub(K.add(K.mul(I(2), Y[i]), K.mul(a1, X[i])), b);
    for (let j = 1; j <= n; j++) if (j !== i) Ai = K.mul(Ai, K.sub(X[i], X[j]));
    if (K.isZero(Ai)) return { defined: false, reason: `A_${i} = 0`, disc, c4, orderEq };
    A[i] = Ai; lam[i] = K.inv(Ai);
  }
  const xx = (k) => { const kk = ((k % N) + N) % N; return kk === 0 ? K.zero() : kk > n ? X[N - kk] : X[kk]; };
  const u = [null];
  for (let i = 1; i <= n; i++) {
    let s = K.zero();
    for (let j = 1; j <= n; j++) s = K.add(s, K.mul(K.sub(xx(i + j), xx(i - j)), lam[j]));
    u[i] = K.mul(s, A[i]);
  }
  let eigen = true;
  for (let i = 2; i <= n; i++) eigen = eigen && K.eq(u[i], u[1]);
  return { defined: true, orderEq, disc, c4, eigen, lam, u: u[1] };
}

// ---------------------------------------------------------------------------------------------
// Verification of one order
// ---------------------------------------------------------------------------------------------
function verifyOrder(N) {
  const cert = CERT[String(N)];
  console.log(`\n================ order N = ${N} ================`);
  const t0 = Date.now();
  const f = definingPolynomial(N);
  check(`f built from its definition is monic of degree ${f.length - 1} in r and equals the stored f`,
    f.length === cert.f.length && f.every((c, i) => zeq(c, zfrom(cert.f[i]))));
  let M;
  try { M = buildModel(N, f); } catch (e) { check(`model could not be built in R_loc: ${e.message}`, false); return null; }
  const { n, R, L } = M;
  console.log(`  model built in R_loc = R[1/(t(t-1))], rank ${R.d} over Z[t]  (${Date.now() - t0} ms)`);
  check(`x_2..x_${n}, all x_i - x_j and all 2y_i+(1-c)x_i-b are units of R_loc (norms ± t^a (t-1)^b, inverses verified)`, true);
  { // closed forms of the first steps: t and t-1 divide recurrence denominators
    const r = L.fromR(R.rClass), t = L.fromR(R.fromZ([0n, 1n])), one = L.int(1);
    const rm1 = L.sub(r, one), tm1 = L.sub(t, one);
    let ok = L.eq(M.X[2], L.mul(L.mul(r, t), rm1)) && L.eq(M.X[3], L.mul(t, rm1)) && L.eq(M.X[4], L.mul(r, rm1));
    if (n >= 5) ok = ok && L.eq(M.X[5], L.mul(L.mul(r, t), tm1));
    check(`x_2 = rt(r-1), x_3 = t(r-1), x_4 = r(r-1)${n >= 5 ? ', x_5 = rt(t-1)' : ' (and r = t, so x_2 = t^2 (t-1))'} in R_loc`, ok);
  }
  if (N === 17) { // the closed forms quoted in the request
    const r = L.fromR(R.rClass), t = L.fromR(R.fromZ([0n, 1n])), one = L.int(1), I = (k) => L.int(k);
    const h = L.add(L.sub(L.mul(r, t), L.mul(I(2), r)), one);
    const j = L.sub(L.add(L.sub(r, L.mul(t, t)), t), one);
    const k = L.add(L.add(L.sub(L.mul(r, L.mul(t, t)), L.mul(I(3), L.mul(r, t))), r), L.mul(t, t));
    const rm1 = L.sub(r, one);
    const x8 = L.mul(L.mul(L.mul(r, rm1), L.sub(r, t)), j), x9 = L.mul(L.mul(L.mul(t, rm1), h), k);
    check('x_8 h^2 = r(r-1)(r-t)j and x_9 j^2 = t(r-1)hk in R_loc (closed forms as stated)',
      L.eq(L.mul(M.X[8], L.mul(h, h)), x8) && L.eq(L.mul(M.X[9], L.mul(j, j)), x9));
  }
  check(`order equation x_${n} = x_${n + 1} holds in R_loc`, M.orderEq);
  check(`A_i * lambda_i = 1 in R_loc for i = 1..${n}`, M.lamOK);
  check(`structural identity 8(u_i - u_1) = (E_i^2 - 4N x_i) - (E_1^2 - 4N x_1) (not used in the proof)`, M.structOK);

  // compressed equations g_i := t^a (t-1)^b (u_i - u_1), a, b minimal
  const g = {}, Pn = {}, adjs = {}, exps = {};
  let gMatch = true, pMatch = true, normOK = true;
  for (let i = 2; i <= n; i++) {
    const di = L.sub(M.u[i], M.u[1]);
    g[i] = di;
    const cg = cert.g[String(i)];
    gMatch = gMatch && di.a === cg.den_exp_t && di.b === cg.den_exp_t1 && R.eq(di.num, cg.num.map(zfrom));
    const { adj, norm } = R.adjNorm(di.num); // adjNorm verifies g_i * adj_i = norm
    const { q, e0, e1 } = zstrip(norm);
    Pn[i] = q; adjs[i] = adj; exps[i] = [e0, e1];
    const ce = cert.norm_exp[String(i)];
    pMatch = pMatch && zeq(q, zfrom(cert.P[String(i)])) && e0 === ce[0] && e1 === ce[1];
    normOK = normOK && zdeg(q) >= 0;
    console.log(`    g_${i}: u_${i}-u_1 = g_${i}/(t^${di.a}(t-1)^${di.b}),  (deg_r, deg_t) of g_${i} = (${R.bidegree(di.num)}),  N(g_${i}) = t^${e0}(t-1)^${e1} P_${i},  deg P_${i} = ${zdeg(q)}`);
  }
  check('g_i recomputed here agree with the stored (PARI) g_i and denominators', gMatch);
  check('norms: g_i * adj(g_i) = t^a (t-1)^b P_i(t) in R, and P_i agree with the stored (PARI) P_i', normOK && pMatch);

  // integral elimination: sum W_i P_i = n0
  let acc = [];
  for (let i = 2; i <= n; i++) acc = zadd(acc, zmul(zfrom(cert.W[String(i)]), Pn[i]));
  const n0 = BigInt(cert.n0);
  const maxW = Math.max(...Object.values(cert.W).map((w) => w.length - 1));
  check(`integral elimination: sum_i W_i(t) P_i(t) = ${n0}  (deg W_i <= ${maxW})`, acc.length === 1 && acc[0] === n0 && n0 > 0n);
  // the same statement as one ideal-membership identity in R, and in matrix form:
  //   sum_i c_i g_i = n0 t^E0 (t-1)^E1,   c_i = W_i t^(E0-e0_i) (t-1)^(E1-e1_i) adj(g_i)
  //   sum_i W_i t^(E0-e0_i) (t-1)^(E1-e1_i) adj(M_i) M_i = n0 t^E0 (t-1)^E1 Id
  {
    const E0 = Math.max(...Object.values(exps).map((e) => e[0])), E1 = Math.max(...Object.values(exps).map((e) => e[1]));
    const mono = (a, b) => { let z = zshift([1n], a); for (let i = 0; i < b; i++) z = zmulT1(z); return z; };
    let lhs = R.zero();
    const d = R.d;
    let matSum = Array.from({ length: d }, () => Array.from({ length: d }, () => []));
    for (let i = 2; i <= n; i++) {
      const w = zmul(zfrom(cert.W[String(i)]), mono(E0 - exps[i][0], E1 - exps[i][1]));
      const ci = R.scal(adjs[i], w);
      lhs = R.add(lhs, R.mul(ci, g[i].num));
      const Mi = R.mulMatrix(g[i].num), Ai = R.mulMatrix(adjs[i]);
      for (let a = 0; a < d; a++) for (let b = 0; b < d; b++) {
        let e = [];
        for (let c = 0; c < d; c++) e = zadd(e, zmul(Ai[a][c], Mi[c][b]));
        matSum[a][b] = zadd(matSum[a][b], zmul(w, e));
      }
    }
    const rhs = zscal(mono(E0, E1), n0);
    check(`ideal membership in R: sum_i c_i g_i = ${n0} * t^${E0} (t-1)^${E1}  with c_i = W_i t^(${E0}-e0_i) (t-1)^(${E1}-e1_i) adj(g_i)`, R.eq(lhs, R.fromZ(rhs)));
    check(`matrix form: sum_i W_i t^(${E0}-e0_i) (t-1)^(${E1}-e1_i) adj(M_i) M_i = ${n0} * t^${E0} (t-1)^${E1} * Id_${d}`,
      matSum.every((row, a) => row.every((e, b) => zeq(e, a === b ? rhs : []))));
  }
  const primes = [];
  { let m = n0; for (let p = 2n; p * p <= m; p++) if (m % p === 0n) { let e = 0; while (m % p === 0n) { m /= p; e++; } primes.push([Number(p), e]); } if (m > 1n) primes.push([Number(m), 1]); }
  console.log(`    n0 = ${primes.map(([p, e]) => (e > 1 ? `${p}^${e}` : `${p}`)).join(' * ')}`);
  check(`prime set of n0 equals the stored list {${Object.keys(cert.primes).join(', ')}}`,
    primes.length === Object.keys(cert.primes).length && primes.every(([p]) => String(p) in cert.primes));

  // resolution of each prime p | n0 over the algebraic closure
  const summary = [];
  for (const [p] of primes) {
    const pc = cert.primes[String(p)];
    const Fp = new Fq(p, [0, 1]);
    const modp = (z) => P.trim(Fp, z.map((x) => [Number(((x % BigInt(p)) + BigInt(p)) % BigInt(p))]));
    let D = [];
    for (let i = 2; i <= n; i++) D = P.gcd(Fp, D, modp(Pn[i]));
    let prod = [Fp.one()];
    let irr = true;
    for (const fac of pc.factors) {
      const phi = fac.phi.map(Number);
      irr = irr && isIrreducible(p, phi);
      prod = P.mul(Fp, prod, P.pow(Fp, phi.map((x) => [x]), fac.mult));
    }
    console.log(`  p = ${p}:`);
    check(`gcd_i(P_i mod ${p}) has degree ${D.length - 1} and equals the product of the listed irreducible factors`, irr && P.eq(Fp, D, prod));
    for (const fac of pc.factors) {
      const phi = fac.phi.map(Number);
      const K = new Fq(p, phi), tau = K.tau();
      const fbar = f.map((c) => K.fromZPoly(c));
      let Gam = P.trim(K, fbar);
      for (let i = 2; i <= n; i++) Gam = P.gcd(K, Gam, P.trim(K, g[i].num.map((c) => K.fromZPoly(c))));
      let prodR = [K.one()];
      const roots = fac.roots.map((rt) => ({ rho: K.zero().map((_, i) => Number(rt.rho[i] ?? 0)), mult: rt.mult }));
      for (const rt of roots) prodR = P.mul(K, prodR, P.pow(K, [K.neg(rt.rho), K.one()], rt.mult));
      const tOK = !K.isZero(tau) && !K.isZero(K.sub(tau, K.one()));
      check(`fibre over a root τ of ${zstr(phi.map(BigInt))} (F_${p}${K.m > 1 ? '^' + K.m : ''}, t(t-1) != 0: ${tOK}): gcd_r(f, g_i) = ${roots.map((rt) => `(r - ${K.str(rt.rho)})^${rt.mult}`).join(' ')}`,
        P.eq(K, Gam, prodR));
      for (const rt of roots) {
        const ev = evalModel(K, N, rt.rho, tau);
        const kind = K.isZero(ev.disc) ? (K.isZero(ev.c4) ? 'cuspidal cubic (disc = c4 = 0)' : 'nodal cubic (disc = 0, c4 != 0)') : 'SMOOTH';
        console.log(`      point r = ${K.str(rt.rho)}, t = ${K.str(tau)}: model defined: ${ev.defined}${ev.defined ? `, eigen-relation holds: ${ev.eigen}` : ` (${ev.reason})`}, curve: ${kind}`);
        check(`this common zero has discriminant 0, so it is not on the open locus`, K.isZero(ev.disc));
        summary.push({ p, deg: K.m, kind, eigen: ev.defined && ev.eigen, smooth: !K.isZero(ev.disc) });
      }
    }
  }
  console.log(`  order ${N} done in ${Date.now() - t0} ms`);
  return { N, n0, primes, summary };
}

// ---------------------------------------------------------------------------------------------
// Independent brute-force sanity check (definitions only): all F_p-points of f = 0 for small p
// ---------------------------------------------------------------------------------------------
function bruteForce(N, pmax) {
  const f = definingPolynomial(N);
  let smoothHits = 0, pts = 0;
  const degenerate = [];
  for (let p = 5; p <= pmax; p++) {
    let isP = true;
    for (let q = 2; q * q <= p; q++) if (p % q === 0) { isP = false; break; }
    if (!isP) continue;
    const K = new Fq(p, [0, 1]);
    const fp = f.map((c) => c.map((x) => Number(((x % BigInt(p)) + BigInt(p)) % BigInt(p))));
    for (let t = 0; t < p; t++) {
      const co = fp.map((c) => { let a = 0; for (let i = c.length - 1; i >= 0; i--) a = (a * t + c[i]) % p; return a; });
      for (let r = 0; r < p; r++) {
        let v = 0;
        for (let i = co.length - 1; i >= 0; i--) v = (v * r + co[i]) % p;
        if (v !== 0) continue;
        const ev = evalModel(K, N, [r], [t]);
        if (!ev.defined) continue;
        pts++;
        if (ev.eigen) { if (K.isZero(ev.disc)) degenerate.push(`p=${p}: (r,t)=(${r},${t})`); else smoothHits++; }
      }
    }
  }
  return { smoothHits, pts, degenerate };
}

// ---------------------------------------------------------------------------------------------
const results = ORDERS.map(verifyOrder).filter(Boolean);
console.log('\n================ brute-force sanity check (definitions only) ================');
for (const N of ORDERS) {
  const bf = bruteForce(N, 211);
  check(`N = ${N}: over F_p, 5 <= p <= 211, ${bf.pts} points with the model defined; smooth solutions of Hλ = uλ: ${bf.smoothHits}; solutions with disc = 0: [${bf.degenerate.join('; ')}]`, bf.smoothHits === 0);
}
console.log('\n================ summary ================');
for (const res of results) {
  const ps = res.primes.map(([p, e]) => (e > 1 ? `${p}^${e}` : `${p}`)).join(' * ');
  console.log(`order ${res.N}: n0 = ${res.n0} = ${ps}`);
  for (const s of res.summary) console.log(`    p = ${s.p}: common zero over F_${s.p}${s.deg > 1 ? '^' + s.deg : ''} on a ${s.kind}; eigen-relation there: ${s.eigen}`);
  const smooth = res.summary.some((s) => s.smooth);
  console.log(`    => ${smooth ? 'SMOOTH EXCEPTIONAL POINT FOUND' : 'no solution of Hλ = uλ on the open locus in characteristic 0 or any p (all common zeros have disc = 0)'}`);
}
console.log(failures === 0 ? '\nALL CHECKS PASSED' : `\n${failures} CHECK(S) FAILED`);
process.exit(failures === 0 ? 0 : 1);
