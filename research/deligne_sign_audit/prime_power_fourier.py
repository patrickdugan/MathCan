"""Exact cyclotomic character sums on small prime-power finite fields.

DEL-02 tests field-trace additive characters, changing bilinear forms,
and cyclotomic-valued local weights. For p=2,3,5 all norm comparisons
are exact integer arithmetic in Q or Q(sqrt(5)).
This finite oracle is not a formal proof of Lemma 3 for arbitrary fields.
"""
from dataclasses import dataclass
from itertools import product

KNOWN_MODULI = frozenset({
 (2, (0,1)), (2, (1,1,1)), (2, (1,1,0,1)), (2, (1,1,0,0,1)),
 (3, (0,1)), (3, (1,0,1)), (3, (1,2,0,1)),
 (5, (0,1)), (5, (2,0,1))
})

@dataclass(frozen=True)
class SmallField:
    p: int
    modulus: tuple[int, ...]
    def __post_init__(self):
        if self.p not in (2,3,5):
            raise ValueError("only p=2,3,5 exact comparisons")
        if len(self.modulus)<2 or self.modulus[-1]!=1:
            raise ValueError("monic modulus required")
        if any(not 0<=a<self.p for a in self.modulus):
            raise ValueError("modulus coefficients")
        if (self.p,self.modulus) not in KNOWN_MODULI:
            raise ValueError("irreducibility not certified")
    @property
    def degree(self):
        return len(self.modulus)-1
    @property
    def q(self):
        return self.p**self.degree
    def digits(self,x):
        if not 0<=x<self.q:
            raise ValueError("field element out of range")
        return [(x//(self.p**i))%self.p for i in range(self.degree)]
    def encode(self,coeffs):
        return sum((a%self.p)*(self.p**i) for i,a in enumerate(coeffs))
    def add(self,x,y):
        return self.encode(a+b for a,b in zip(self.digits(x),self.digits(y)))
    def neg(self,x):
        return self.encode(-a for a in self.digits(x))
    def sub(self,x,y):
        return self.add(x,self.neg(y))
    def mul(self,x,y):
        a,b=self.digits(x),self.digits(y)
        m=self.degree
        w=[0]*(2*m-1)
        for i in range(m):
            for j in range(m):
                w[i+j]+=a[i]*b[j]
        for k in range(2*m-2,m-1,-1):
            t=w[k]%self.p
            for j in range(m):
                w[k-m+j]-=t*self.modulus[j]
        return self.encode(w[:m])
    def pow(self,x,n):
        if n<0:
            if x==0: raise ZeroDivisionError
            return self.pow(self.pow(x,self.q-2),-n)
        z=1
        while n:
            if n&1: z=self.mul(z,x)
            x=self.mul(x,x)
            n//=2
        return z
    def inv(self,x):
        if x==0: raise ZeroDivisionError
        return self.pow(x,self.q-2)
    def trace(self,x):
        acc,z=0,x
        for _ in range(self.degree):
            acc=self.add(acc,z)
            z=self.pow(z,self.p)
        if acc>=self.p:
            raise AssertionError("trace must lie in prime field")
        return acc
    def vectors(self,d):
        if d<1: raise ValueError("d>=1")
        return tuple(product(range(self.q),repeat=d))

FIELDS={
 "F2": SmallField(2,(0,1)), "F4": SmallField(2,(1,1,1)),
 "F8": SmallField(2,(1,1,0,1)), "F16": SmallField(2,(1,1,0,0,1)),
 "F3": SmallField(3,(0,1)), "F9": SmallField(3,(1,0,1)),
 "F27": SmallField(3,(1,2,0,1)), "F5": SmallField(5,(0,1)),
 "F25": SmallField(5,(2,0,1))
}

def identity_matrix(d):
    return tuple(tuple(int(i==j) for j in range(d)) for i in range(d))

def bilinear(field,x,y,matrix):
    total=0
    for i in range(len(x)):
        for j in range(len(y)):
            total=field.add(total,field.mul(field.mul(x[i],matrix[i][j]),y[j]))
    return total

def is_nondegenerate(field,matrix):
    d=len(matrix)
    if d<1 or any(len(row)!=d for row in matrix):
        raise ValueError("square nonempty matrix required")
    a=[list(row) for row in matrix]
    for i in range(d):
        pivot=next((j for j in range(i,d) if a[j][i]),None)
        if pivot is None: return False
        a[i],a[pivot]=a[pivot],a[i]
        v=field.inv(a[i][i])
        for c in range(i,d):
            a[i][c]=field.mul(a[i][c],v)
        for j in range(i+1,d):
            factor=a[j][i]
            for c in range(i,d):
                a[j][c]=field.sub(a[j][c],field.mul(factor,a[i][c]))
    return True

def orthogonality_fiber_certificate(field,matrix,h):
    """Each nonzero linear form's trace character has p balanced fibers."""
    if h==0: raise ValueError("h must be nonzero")
    space=field.vectors(len(matrix))
    target=len(space)//field.p
    for x in space:
        if all(v==0 for v in x): continue
        counts=[0]*field.p
        for y in space:
            exponent=field.trace(field.mul(h,bilinear(field,x,y,matrix)))
            counts[exponent]+=1
        if tuple(counts)!=(target,)*field.p:
            return {"balanced":False,"bad_vector":x,"fibers":tuple(counts),
                    "nondegenerate":is_nondegenerate(field,matrix)}
    return {"balanced":True,"nondegenerate":is_nondegenerate(field,matrix),
            "vectors_checked":len(space)-1,"fiber_size":target}

def zero(p): return (0,)*p
def one(p): return (1,)+(0,)*(p-1)
def scalar(a,p): return (a,)+(0,)*(p-1)
def add_poly(a,b): return tuple(x+y for x,y in zip(a,b))
def shift_poly(a,e):
    p=len(a); e%=p
    return tuple(a[(i-e)%p] for i in range(p))
def mul_poly(a,b):
    p=len(a)
    if p!=len(b): raise ValueError("incompatible cyclotomic rings")
    out=[0]*p
    for i in range(p):
        for j in range(p):
            out[(i+j)%p]+=a[i]*b[j]
    return tuple(out)

def norm_certificate(coeffs):
    """(r,s,den) for |sum c_j*zeta_p^j|^2=(r+s*sqrt(5))/den."""
    p=len(coeffs)
    if p==2: return ((coeffs[0]-coeffs[1])**2,0,1)
    if p==3:
        a,b=coeffs[0]-coeffs[2],coeffs[1]-coeffs[2]
        return (a*a-a*b+b*b,0,1)
    if p==5:
        diag=sum(c*c for c in coeffs)
        adj=sum(coeffs[i]*coeffs[j] for i in range(5) for j in range(i+1,5)
                if j-i in (1,4))
        second=sum(coeffs[i]*coeffs[j] for i in range(5) for j in range(i+1,5)
                   if j-i in (2,3))
        return (2*diag-adj-second,adj-second,2)
    raise ValueError("only p=2,3,5")

def norm_sq_le_integer(coeffs,cap):
    r,s,den=norm_certificate(coeffs)
    u=den*cap-r
    if s==0: return u>=0
    if s>0: return u>=0 and u*u>=5*s*s
    return u>=0 or (u*u<=5*s*s)

def weight_bound(weights,p):
    t=0
    for weight in weights:
        for coeffs in weight.values():
            while not norm_sq_le_integer(coeffs,t*t):
                t+=1
    return t

def weights_from_ints(weights,p):
    return tuple({x:scalar(v,p) for x,v in w.items()} for w in weights)

def path_sum_contract(field,d,weights,matrices,h,c):
    """Independent of enumeration of all |E|^(d*k) paths."""
    k=len(weights)
    if k<2 or len(matrices)!=k-1:
        raise ValueError("k>=2, exactly k-1 forms required")
    if h==0: raise ValueError("nontrivial scalar h required")
    space=field.vectors(d)
    if any(set(w)!=set(space) for w in weights):
        raise ValueError("weights must cover A")
    v=dict(weights[0])
    for i,matrix in enumerate(matrices):
        if len(matrix)!=d or any(len(row)!=d for row in matrix):
            raise ValueError("coupling matrix shape")
        nxt={}
        for y in space:
            tally=zero(field.p)
            for x in space:
                exponent=field.trace(field.mul(h,bilinear(field,x,y,matrix)))
                tally=add_poly(tally,shift_poly(v[x],exponent))
            nxt[y]=mul_poly(weights[i+1][y],tally)
        v=nxt
    total=zero(field.p)
    for x in space:
        total=add_poly(total,v[x])
    return shift_poly(total,field.trace(field.mul(h,c)))

def path_sum_direct(field,d,weights,matrices,h,c):
    space=field.vectors(d)
    total=zero(field.p)
    for path in product(space,repeat=len(weights)):
        exponent=field.mul(h,c)
        term=one(field.p)
        for i,x in enumerate(path):
            term=mul_poly(term,weights[i][x])
        for i,matrix in enumerate(matrices):
            exponent=field.add(exponent,
                field.mul(h,bilinear(field,path[i],path[i+1],matrix)))
        total=add_poly(total,shift_poly(term,field.trace(exponent)))
    return total

def verify_path_bound(field,d,weights,matrices,h,c,t_bound=None):
    k=len(weights)
    t=weight_bound(weights,field.p) if t_bound is None else t_bound
    if any(not norm_sq_le_integer(cfs,t*t) for w in weights for cfs in w.values()):
        raise ValueError("T does not bound all local weights")
    total=path_sum_contract(field,d,weights,matrices,h,c)
    ceiling=t**(2*k)*field.q**(d*(k+1))
    return {"ok":norm_sq_le_integer(total,ceiling),
        "coefficients":total,"norm_certificate":norm_certificate(total),
        "ceiling":ceiling,"field_order":field.q,"p":field.p,
        "d":d,"k":k,"T":t,
        "all_forms_nondegenerate":all(is_nondegenerate(field,b) for b in matrices)}
