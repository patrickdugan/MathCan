"""Exact Fraction oracle for OLM-16 (no Torch, no external packages)."""
from fractions import Fraction as Q


def F(x):
    return x if isinstance(x, Q) else Q(x)


def vec(x):
    return tuple(F(t) for t in x)


def dot(a, b):
    if len(a) != len(b):
        raise ValueError("dimension mismatch")
    return sum((x*y for x,y in zip(a,b)), Q(0))


def sqnorm(a):
    return dot(a,a)


def solve_square(matrix, rhs):
    n = len(rhs)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("square matrix required")
    m = [list(map(F,row)) + [F(b)] for row,b in zip(matrix,rhs)]
    for col in range(n):
        pivot = next((k for k in range(col,n) if m[k][col]), None)
        if pivot is None:
            raise ValueError("rank deficient")
        m[col],m[pivot] = m[pivot],m[col]
        scale = m[col][col]
        m[col] = [v/scale for v in m[col]]
        for row in range(n):
            if row==col:continue
            k=m[row][col]
            m[row]=[u-k*v for u,v in zip(m[row],m[col])]
    return tuple(row[-1] for row in m)


def project_null(rows, direction):
    """Exact orthogonal projection onto the kernel of independent rows."""
    a=vec(direction)
    O=tuple(vec(r) for r in rows)
    if not O:
        return a
    if any(len(r)!=len(a) for r in O):
        raise ValueError("row dimension mismatch")
    gram=[[dot(x,y) for y in O] for x in O]
    multipliers=solve_square(gram,[dot(x,a) for x in O])
    v=tuple(a[j]-sum((lam*r[j] for lam,r in zip(multipliers,O)),Q(0))
            for j in range(len(a)))
    assert all(dot(r,v)==0 for r in O)
    return v


def selective_kill(other_rows, target_row, z, tau):
    q=F(z)+F(tau)
    if F(z)<=0 or F(tau)<=0:
        raise ValueError("strictly active target and positive overshoot required")
    v=project_null(other_rows,target_row)
    s=sqnorm(v)
    if s==0:
        raise ValueError("target row lies in span of protected rows")
    delta=tuple(q*x/s for x in v)
    if dot(target_row,delta)!=q or any(dot(row,delta) for row in other_rows):
        raise AssertionError("kill constraints violated")
    return delta


def preactivations_after(rows, preactivations, displacement):
    if len(rows)!=len(preactivations):
        raise ValueError("preactivation length mismatch")
    return tuple(F(b)-dot(vec(a),vec(displacement))
                 for a,b in zip(rows,preactivations))


def strict_top4(rows, preactivations, displacement, selected):
    new=preactivations_after(rows,preactivations,displacement)
    S=set(selected)
    if len(S)!=4 or not S<=set(range(len(rows))):
        raise ValueError("exactly four selected rows required")
    smallest=min(new[i] for i in S)
    return smallest>0 and all(new[j]<smallest for j in range(len(rows)) if j not in S)


def affine_margin(x, offset, gradient):
    return F(offset)+dot(x,gradient)


def difference_from_margins(h, kill, sham, margin):
    return margin(tuple(x-y for x,y in zip(h,sham))) - margin(
        tuple(x-y for x,y in zip(h,kill)))


def sign_reversal_witness():
    e=lambda i:tuple(Q(int(k==i)) for k in range(5))
    h=vec((1,1,1,1,0))
    others=(e(0),e(1),e(2))
    a=e(3)
    kill=selective_kill(others,a,1,Q(1,4))
    sham=tuple(Q(5,4)*x for x in e(4))
    plus=lambda x:affine_margin(x,3,vec((0,0,0,1,-1)))
    minus=lambda x:affine_margin(x,3,vec((0,0,0,-1,1)))
    return {"kill":kill,"sham":sham,
            "clean_plus":plus(h),"clean_minus":minus(h),
            "effect_plus":difference_from_margins(h,kill,sham,plus),
            "effect_minus":difference_from_margins(h,kill,sham,minus)}


def small_dimensional_obstructions():
    out={}
    for d in (3,4,5,6):
        e=lambda i:tuple(Q(int(j==i)) for j in range(d))
        others=(e(0),e(1),e(2))
        # d=3 shows impossible kill; d=4 shows impossible nonzero sham.
        a=e(0) if d==3 else e(3)
        try:
            kill=selective_kill(others,a,1,Q(1,4))
            kill_possible=True
        except ValueError:
            kill=()
            kill_possible=False
        if d>=4:
            candidate=project_null((*others,a),e(d-1))
            sham_possible=sqnorm(candidate)>0
        else:
            sham_possible=False
        out[d]={"kill_possible":kill_possible,"nonzero_tangent_sham":sham_possible,
                "kill_sqnorm":sqnorm(kill)}
    return out


if __name__=="__main__":
    print(sign_reversal_witness())
    print(small_dimensional_obstructions())
