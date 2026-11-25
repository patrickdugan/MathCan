"""Exact small finite fields and short Weierstrass arithmetic, no dependencies.

Elements are integers with base-p digits, least significant coefficient first.
The selected irreducible modulus and primitive element are written to receipts.
Tables accelerate multiplication; polynomial arithmetic independently checks them.
"""
from math import isqrt
from functools import lru_cache


def prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_factors(n):
    out = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def _trim(a):
    while a and not a[-1]:
        a.pop()
    return a


def _pmod(a, b, p):
    a = _trim(a[:]); inv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        v = a[-1]*inv % p; k = len(a)-len(b)
        for i, c in enumerate(b):
            a[i+k] = (a[i+k] - v*c) % p
        _trim(a)
    return a


def _pmul(a, b, f, p):
    out = [0]*(len(a)+len(b)-1) if a and b else []
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i+j] = (out[i+j]+u*v) % p
    return _pmod(out, f, p)


def _ppow(a, n, f, p):
    out = [1]
    while n:
        if n & 1:
            out = _pmul(out, a, f, p)
        a = _pmul(a, a, f, p); n >>= 1
    return out


def _pgcd(a, b, p):
    while b:
        a, b = b, _pmod(a, b, p)
    return a


def irreducible(f, p):
    """Rabin criterion, with the Frobenius powers computed by long reduction."""
    n = len(f)-1
    x = [0, 1]; v = x
    tests = {n//ell for ell in prime_factors(n)}
    for i in range(1, n+1):
        v = _ppow(v, p, f, p)
        w = v[:] + [0]*max(0, 2-len(v))
        w[1] = (w[1]-1) % p; _trim(w)
        if i in tests and len(_pgcd(f, w, p)) > 1:
            return False
    return not w


class Field:
    def __init__(self, p, degree=1):
        assert prime(p) and p > 3 and degree >= 1
        self.p, self.degree, self.q = p, degree, p**degree
        assert self.q <= 65536
        if degree == 1:
            self.modulus = [0, 1]; self.primitive = None
            self.neg_table = [(-a) % p for a in range(p)]
            self.inv_table = [0] + [pow(a, -1, p) for a in range(1, p)]
        else:
            for code in range(1, self.q):
                f = self.digits(code) + [1]
                if f[0] and irreducible(f, p):
                    self.modulus = f; break
            else:
                raise AssertionError("irreducible search exhausted")
            factors = prime_factors(self.q-1)
            for gen in range(2, self.q):
                if all(self.polynomial_power(gen, (self.q-1)//ell) != 1 for ell in factors):
                    self.primitive = gen; break
            else:
                raise AssertionError("primitive search exhausted")
            exp = [1]
            for _ in range(self.q-2):
                exp.append(self.polynomial_mul(exp[-1], self.primitive))
            assert len(set(exp)) == self.q-1
            assert self.polynomial_mul(exp[-1], self.primitive) == 1
            self.exp = exp*2
            self.log = [-1]*self.q
            for i, a in enumerate(exp): self.log[a] = i
            self.neg_table = [self.encode([(-c) % p for c in self.digits(a)]) for a in range(self.q)]
            self.inv_table = [0] + [exp[(-self.log[a]) % (self.q-1)] for a in range(1, self.q)]
        self.squares = {}
        for y in range(self.q):
            self.squares.setdefault(self.mul(y,y), []).append(y)
        self.iso_cache = {}

    def const(self, x): return x % self.p
    def digits(self, x):
        out = []
        for _ in range(self.degree):
            out.append(x % self.p); x //= self.p
        return out
    def encode(self, coeff):
        out = 0
        for c in reversed(coeff): out = out*self.p+c
        return out
    def add(self, a, b):
        if self.degree == 1: return (a+b) % self.p
        p = self.p; out = 0; place = 1
        for _ in range(self.degree):
            out += ((a % p + b % p) % p)*place
            a //= p; b //= p; place *= p
        return out
    def neg(self, a): return self.neg_table[a]
    def sub(self, a, b): return self.add(a, self.neg_table[b])
    def mul(self, a, b):
        if self.degree == 1: return a*b % self.p
        return 0 if not a or not b else self.exp[self.log[a]+self.log[b]]
    def inv(self, a):
        if not a: raise ZeroDivisionError("zero in finite field")
        return self.inv_table[a]
    def div(self, a, b): return self.mul(a, self.inv(b))
    def pow(self, a, n):
        if n == 0: return 1
        if not a:
            if n < 0: raise ZeroDivisionError("negative power of zero")
            return 0
        if self.degree == 1: return pow(a, n, self.p)
        return self.exp[(self.log[a]*n) % (self.q-1)]
    def polynomial_mul(self, a, b):
        return self.encode(_pmul(self.digits(a), self.digits(b), self.modulus, self.p))
    def polynomial_power(self, a, n):
        return self.encode(_ppow(self.digits(a), n, self.modulus, self.p))
    def sum(self, xs):
        s = 0
        for x in xs: s = self.add(s, x)
        return s
    def metadata(self):
        return dict(p=self.p, degree=self.degree, q=self.q,
                    modulus_low_first=self.modulus, primitive_element=self.primitive,
                    representation="integer with base-p polynomial coefficients")
    def isomorphism_key(self, a, b):
        """F_q-isomorphism class of short equations, by all u^4/u^6 scalings."""
        if (a,b) in self.iso_cache: return self.iso_cache[a,b]
        orbit = {(self.mul(a,self.pow(u,4)), self.mul(b,self.pow(u,6))) for u in range(1,self.q)}
        representative = min(orbit)
        for point in orbit: self.iso_cache[point] = representative
        return representative


class Curve:
    def __init__(self, F, a, b):
        self.F, self.a, self.b = F, a, b
        m, add, c = F.mul, F.add, F.const
        den = add(m(c(4), F.pow(a,3)), m(c(27), m(b,b)))
        assert den, "singular short equation"
        self.discriminant = m(c(-16), den)
        self.j = F.div(m(c(1728*4), F.pow(a,3)), den)
        self.points = [None]
        for x in range(F.q):
            rhs = add(add(m(m(x,x),x),m(a,x)),b)
            self.points.extend((x,y) for y in F.squares.get(rhs, []))
        self.order = len(self.points)
        self.trace = F.q+1-self.order
        assert self.trace**2 <= 4*F.q
    def add(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        F = self.F; x,y = P; u,v = Q
        if x == u and F.add(y,v) == 0: return None
        m = F.div(F.sub(v,y),F.sub(u,x)) if x != u else F.div(F.add(F.mul(F.const(3),F.mul(x,x)),self.a),F.mul(F.const(2),y))
        z = F.sub(F.sub(F.mul(m,m),x),u)
        return z, F.sub(F.mul(m,F.sub(x,z)),y)
    def mul(self, k, P):
        if k < 0: return self.mul(-k, (P[0],self.F.neg(P[1])) if P is not None else None)
        out = None
        while k:
            if k & 1: out = self.add(out,P)
            P = self.add(P,P); k >>= 1
        return out
    def sequence(self, P, n):
        seq = [None]; Q = P
        for _ in range(n-1):
            assert Q is not None
            seq.append(Q); Q = self.add(Q,P)
        assert Q is None and len(set(seq)) == n
        return seq
    def subgroups(self, n):
        assert prime(n) and self.order % n == 0
        if self.order % (n*n) or (self.F.q-1) % n:
            for P in self.points[1:]:
                Q = self.mul(self.order//n, P)
                if Q is not None:
                    seq = self.sequence(Q,n)
                    yield self.sequence(min(seq[1:]),n)
                    return
            raise AssertionError("unique n-torsion subgroup was not found")
        seen = set()
        for P in self.points[1:]:
            if P in seen or self.mul(n,P) is not None: continue
            seq = self.sequence(P,n); seen.update(seq[1:])
            yield self.sequence(min(seq[1:]),n)


class Basis:
    def __init__(self,F): self.F=F; self.rows={}
    def reduce(self,v):
        F=self.F; v=list(v)
        for k,w in sorted(self.rows.items()):
            c=v[k]
            if c: v=[F.sub(a,F.mul(c,b)) for a,b in zip(v,w)]
        return v
    def add(self,v):
        v=self.reduce(v); k=next((i for i,x in enumerate(v) if x),None)
        if k is None:return False
        a=self.F.inv(v[k]); self.rows[k]=[self.F.mul(x,a) for x in v]; return True
    def contains(self,v):return not any(self.reduce(v))
    def __len__(self):return len(self.rows)


def residue_profile(C,seq,complete=False):
    F=C.F; n=len(seq); m=(n-1)//2; roots=[seq[i][0] for i in range(1,m+1)]
    assert len(set(roots))==m
    derivatives={}
    for x in roots:
        d=1
        for z in roots:
            if x!=z:d=F.mul(d,F.sub(x,z))
        derivatives[x]=d
    lam=[0]+[F.inv(F.mul(F.mul(F.const(2),y),derivatives[x])) for x,y in seq[1:]]
    assert all(lam[n-i]==F.neg(lam[i]) for i in range(1,n))
    f=[0]+[P[0] for P in seq[1:]]
    values=[]
    for i in range(1,n):
        values.append(F.div(F.sum(F.mul(f[(i+j)%n],lam[j]) for j in range(1,n)),lam[i]))
        if not complete and len(values)>1 and values[-1]!=values[0]:break
    constant=values[0] if all(v==values[0] for v in values) else None
    return constant,values,lam


def direct_matrix_check(C,seq):
    """Obtain annihilator from monomials by elimination, without residue weights.

    Its equations against every target column determine all possible pole values.
    The codimension and each annihilator identity are checked by field arithmetic.
    """
    F=C.F; n=len(seq); pts=seq[1:]; d=n//3; U=Basis(F)
    for i in range(d+1):
        for j in range(d+1-i):
            U.add([F.mul(F.pow(x,i),F.pow(y,j)) for x,y in pts])
    assert len(U)==n-2
    free=next(k for k in range(n-1) if k not in U.rows)
    z=[0]*(n-1); z[free]=1
    for k,w in sorted(U.rows.items(),reverse=True):
        z[k]=F.neg(F.sum(F.mul(w[j],z[j]) for j in range(k+1,n-1)))
    assert all(F.sum(F.mul(a,b) for a,b in zip(w,z))==0 for w in U.rows.values())
    f=[0]+[P[0] for P in pts]; candidate=None; consistent=True
    for i in range(1,n):
        row=F.sum(F.mul(f[(i+j)%n],z[j-1]) for j in range(1,n))
        coefficient=z[n-i-1]
        if coefficient:
            value=F.neg(F.div(row,coefficient))
            if candidate is None:candidate=value
            elif value!=candidate:consistent=False
        elif row:consistent=False
    return candidate if consistent else None
