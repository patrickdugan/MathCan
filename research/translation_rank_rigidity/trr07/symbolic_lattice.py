"""Integral Bezout cofactors from a compact FLINT row-Hermite calculation."""
from flint import fmpz_mat, fmpz_poly, nmod_mat


def bezout(polynomials, degree=None):
    coefficients=[[int(c) for c in p] for p in polynomials]
    top=max(map(len,coefficients))-1

    def generators(k):
        return [list(reversed([0]*shift+p+[0]*(top+k+1-len(p)-shift)))
                for p in coefficients for shift in range(k+1)]

    if degree is None:
        # Full rank modulo this prime implies full rank over Q. It serves
        # only to select a small matrix, never as an exclusion certificate.
        for k in range(top+1):
            rows=generators(k)
            if len(rows)>=top+k+1 and nmod_mat(rows,1000000007).rank()==top+k+1:
                degree=k+1
                break
        else:
            raise ValueError("no full-rank bounded coefficient lattice")
    rows=generators(degree)
    matrix=fmpz_mat(rows)
    H,U=matrix.hnf(transform=True)
    assert H==U*matrix
    rank=top+degree+1
    assert H[rank-1,rank-1]>0
    assert all(H[rank-1,j]==0 for j in range(rank-1))
    integer=int(H[rank-1,rank-1])
    vector=[int(U[rank-1,j]) for j in range(len(rows))]
    initial_bits=max(abs(v).bit_length() for v in vector)
    if len(rows)>rank:
        kernel=fmpz_mat([[U[i,j] for j in range(len(rows))] for i in range(rank,len(rows))])
        reduced=kernel.lll()
        assert reduced*matrix==fmpz_mat(reduced.nrows(),matrix.ncols())
        gram=reduced*reduced.transpose()
        for _ in range(8):
            column=fmpz_mat([[v] for v in vector])
            projection=gram.solve(reduced*column)
            rounded=fmpz_mat([[round(projection[i,0])] for i in range(reduced.nrows())])
            correction=reduced.transpose()*rounded
            updated=[v-int(correction[i,0]) for i,v in enumerate(vector)]
            if updated==vector:
                break
            vector=updated
    cofactors=[vector[i*(degree+1):(i+1)*(degree+1)] for i in range(len(coefficients))]
    combined=sum((fmpz_poly(w)*fmpz_poly(p) for w,p in zip(cofactors,coefficients)),fmpz_poly())
    assert combined==fmpz_poly([integer])
    return integer,cofactors,degree,{"rows":len(rows),"columns":rank,
                                   "coefficient_bits_before_reduction":initial_bits,
                                   "coefficient_bits_after_reduction":max(abs(v).bit_length() for v in vector)}
