#!/usr/bin/env python3
"""derive_certificate.py — how the certificate data were found (PARI via cypari2).

    pip install cypari2
    python3 derive_certificate.py            # writes certificate.json, prints a summary

This is the search side only.  Nothing here needs to be trusted: verify.mjs recomputes the model,
the compressed equations g_i and the stripped norms P_i from the stated definitions, and checks the
cofactors W_i, the integer n0 and the per-prime data produced below.

Model (orders N = 2n+1 in {7, 11, 13, 17}):
    b = r t (r-1), c = t (r-1), R = Z[t][r]/(f_N),
    (x_1,y_1) = (0,0), (x_2,y_2) = (b, bc), m_i = y_i/x_i,
    x_{i+1} = m_i^2 + (1-c) m_i + b - x_i,  y_{i+1} = b - (m_i+1-c) x_{i+1},
    A_i = (2y_i + (1-c)x_i - b) prod_{j != i} (x_i - x_j),  lambda_i = 1/A_i,
    H_ij = x_{(i+j) mod N} - x_{(i-j) mod N}  (x_0 = 0, x_{N-i} = x_i),
    u_i = (H lambda)_i / lambda_i,   obstruction:  u_i = u_1 for i = 2..n.
"""
import json
import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10**9)
pari("r; t;")  # r is created first, so r is the main variable

# NB: a GP function definition swallows the rest of the string it sits in, so each one gets its own call.
FN = {
    7: "r - t",
    11: "r^2 - (t^3 - 3*t^2 + 4*t)*r + t",
    13: "(r-t)^3 - r*(t-1)^3*(r*t - 2*r + 1)",
    17: "r*(r-t)*(r - t^2 + t - 1)^3 - t*(r*t - 2*r + 1)^3*(r*t^2 - 3*r*t + r + t^2)",
}
KW = {7: 3, 11: 4, 13: 5, 17: 8}  # degree bound for the cofactors W_i


def setup(N):
    n = (N - 1) // 2
    pari("N = %d; n = %d;" % (N, n))
    pari("b = r*t*(r-1); c = t*(r-1); a1 = 1 - c; a3 = -b; a2 = -b;")
    pari("f = %s;" % FN[N])
    # generic recurrence over Q(r,t): f must divide the numerator of x_n - x_{n+1}
    pari("""Xg = vector(n+1); Yg = vector(n+1); Xg[1] = 0; Yg[1] = 0; Xg[2] = b; Yg[2] = b*c;
            for(i=2, n, m = Yg[i]/Xg[i]; Xg[i+1] = m^2 + (1-c)*m + b - Xg[i]; Yg[i+1] = b - (m+1-c)*Xg[i+1]);""")
    assert pari("numerator(Xg[n]-Xg[n+1]) % f == 0") and pari("pollead(f, r) == 1")
    # the same recurrence in the function field Q(t)[r]/(f)
    pari("""X = vector(n+1); Y = vector(n+1);
            X[1] = Mod(0, f); Y[1] = Mod(0, f); X[2] = Mod(b, f); Y[2] = Mod(b*c, f);
            for(i=2, n, m = Y[i]/X[i]; X[i+1] = m^2 + (1-c)*m + b - X[i]; Y[i+1] = b - (m+1-c)*X[i+1]);""")
    assert pari("X[n] == X[n+1]")
    pari("xx(k) = my(kk = k % N); if(kk == 0, return(Mod(0, f))); if(kk > n, kk = N - kk); X[kk]")
    pari("""xp = vector(n, i, 2*Y[i] + a1*X[i] + a3);
            A  = vector(n, i, xp[i] * prod(jj=1, n, if(jj==i, 1, X[i]-X[jj])));
            lam = vector(n, i, 1/A[i]);
            H = matrix(n, n, i, jj, xx(i+jj) - xx(i-jj));
            Hl = H * lam~;
            u = vector(n, i, Hl[i]/lam[i]);
            G = vector(n-1, i, u[i+1]-u[1]);""")
    # structural identity (not used in the proof): 2(u_i - u_1) = T_i - T_1, T_i = e1(iP)^2 - N x_i
    pari("""b2 = a1^2 + 4*a2; b4 = a1*a3;
            xpp = vector(n, i, 6*X[i]^2 + b2*X[i] + b4);
            e1 = vector(n, i, -xp[i]*sum(jj=1, n, if(jj==i, 0, 1/(X[i]-X[jj]))) - xpp[i]/(2*xp[i]));
            T = vector(n, i, e1[i]^2 - N*X[i]);""")
    assert pari("vector(n-1, i, 2*G[i] == T[i+1]-T[1]) == vector(n-1, i, 1)")
    # g_i = d_i(t) (u_i - u_1), d_i the common denominator (a monomial in t and t-1)
    pari("dG = vector(n-1, i, denominator(content(lift(G[i])))); g = vector(n-1, i, lift(G[i])*dG[i]);")
    return n


def zp(expr):
    out = [str(c) for c in pari("Vecrev(%s)" % expr)]
    while out and out[-1] == "0":
        out.pop()
    return out


def relt(expr, d):
    return [zp("polcoeff(%s, %d, r)" % (expr, k)) for k in range(d)]


pari("strip(q) = my(e0 = 0, e1 = 0); while(subst(q, t, 0) == 0, q = q/t; e0++); while(subst(q, t, 1) == 0, q = q/(t-1); e1++); [q, e0, e1]")
pari("lat(K) = my(M = matrix(dP+K+1, (n-1)*(K+1))); for(i=1, n-1, for(k=0, K, my(q = P[i]*t^k); for(e=0, dP+K, M[e+1, (i-1)*(K+1)+k+1] = polcoeff(q, e)))); M")
pari("tdeg(p) = my(m = 0, cf); for(i=0, poldegree(p, r), cf = polcoeff(p, i, r); if(cf != 0, m = max(m, i + poldegree(cf, t)))); m")
pari("xg(kk) = my(k2 = kk % N); if(k2 == 0, 0, if(k2 > n, Xg[N-k2], Xg[k2]))")

out = {}
for N in (7, 11, 13, 17):
    n = setup(N)
    d = int(pari("poldegree(f, r)"))
    # norms to Z[t] and their unit-free parts P_i
    pari("Nm = vector(n-1, i, polresultant(f, g[i], r)); S = vector(n-1, i, strip(Nm[i])); P = vector(n-1, i, S[i][1]); dP = poldegree(P[1]);")
    pari("sd = vector(n-1, i, strip(dG[i]));")
    assert pari("vector(n-1, i, sd[i][1] == 1) == vector(n-1, i, 1)"), "denominator of u_i - u_1 is not a monomial in t, t-1"
    cof = str(pari("factor(numerator(Xg[n]-Xg[n+1])/f)"))
    # integer Hermite normal form of the lattice spanned by t^k P_i: smallest n0 with n0 in (P_2..P_n), cofactors W_i
    K = KW[N]
    pari("K = %d; M = lat(K); HU = mathnf(M, 1); Hn = HU[1]; U = HU[2]; nk = matsize(M)[2] - matsize(Hn)[2]; n0 = Hn[1,1]; v = U[, nk+1];" % K)
    if int(pari("nk")) > 0:  # shrink the cofactors against an LLL-reduced kernel basis
        pari("Ker = matkerint(M); KL = Ker*qflll(Ker); for(it=1, 8, cc = matsolve(KL~*KL, KL~*v); v = v - KL*round(cc));")
    pari("W = vector(n-1, i, sum(k=0, K, v[(i-1)*(K+1)+k+1]*t^k));")
    assert pari("sum(i=1, n-1, W[i]*P[i]) == n0")
    n0 = int(pari("n0"))
    ent = {
        "N": N, "n": n, "rank": d,
        "f": relt("f", d + 1),
        "order_equation_cofactor": cof,
        "g": {str(i + 1): {"num": relt("g[%d]" % i, d), "den_exp_t": int(pari("sd[%d][2]" % i)), "den_exp_t1": int(pari("sd[%d][3]" % i))} for i in range(1, n)},
        "norm_exp": {str(i + 1): [int(pari("S[%d][2]" % i)), int(pari("S[%d][3]" % i))] for i in range(1, n)},
        "P": {str(i + 1): zp("P[%d]" % i) for i in range(1, n)},
        "W": {str(i + 1): zp("W[%d]" % i) for i in range(1, n)},
        "n0": str(n0),
        "n0_factorisation": str(pari("factor(n0)")),
        "primes": {},
    }
    # for each prime p | n0: common roots of the P_i mod p, and the common zeros of f, g_i in each fibre
    for a in range(1, int(pari("matsize(factor(n0))[1]")) + 1):
        p = int(pari("factor(n0)[%d,1]" % a))
        pari("p = %d; Dp = 0; for(i=1, n-1, Dp = gcd(Dp, P[i]*Mod(1,p))); Dp = lift(Dp / pollead(Dp)); FD = factor(Dp*Mod(1,p));" % p)
        pent = {"gcd_P": zp("Dp"), "factors": []}
        for bq in range(1, int(pari("matsize(FD)[1]")) + 1):
            pari("phi = lift(FD[%d,1]); dphi = poldegree(phi);" % bq)
            lin = int(pari("dphi")) == 1
            pari("t0 = Mod(-polcoeff(phi,0), p);" if lin else "t0 = ffgen(phi*Mod(1,p), 'a);")
            pari("Gam = subst(f, t, t0)*t0^0; for(i=1, n-1, Gam = gcd(Gam, subst(g[i], t, t0)*t0^0)); Gam = Gam/pollead(Gam); FG = factor(Gam);")
            roots = []
            for ci in range(1, int(pari("matsize(FG)[1]")) + 1):
                assert int(pari("poldegree(FG[%d,1])" % ci)) == 1, "fibre gcd has a non-linear factor"
                pari("rho = -polcoeff(FG[%d,1], 0);" % ci)
                co = [str(pari("lift(rho)"))] if lin else [str(x) for x in pari("lift(Vecrev(rho.pol))")]
                roots.append({"rho": co, "mult": int(pari("FG[%d,2]" % ci))})
            pent["factors"].append({"phi": zp("phi"), "mult": int(pari("FD[%d,2]" % bq)), "deg_Gamma": int(pari("poldegree(Gam)")), "roots": roots})
        ent["primes"][str(p)] = pent
    out[str(N)] = ent
    print("N=%d: rank %d, deg P_i = %s, n0 = %d = %s" % (N, d, pari("dP"), n0, ent["n0_factorisation"]))
    print("      u_i - u_1 = g_i / (t^a (t-1)^b), (a, b) =", [(ent["g"][k]["den_exp_t"], ent["g"][k]["den_exp_t1"]) for k in ent["g"]],
          "; (deg_r, deg_t) of g_i:", pari("vector(n-1, i, [poldegree(g[i], r), poldegree(g[i], t)])"))

    # structural remarks (checked here, not used in the proof)
    #  (1) modulo N the equations are proportional: (u_i - u_1)(j^2 - 1) = (u_j - u_1)(i^2 - 1) in F_N(t)[r]/(f)
    pari("chkN = vector(n-2, i, my(a = Mod(i+1, N)^2 - 1, bq = Mod(i+2, N)^2 - 1, e = (lift(G[i])*Mod(1,N))*bq - (lift(G[i+1])*Mod(1,N))*a); (e % (f*Mod(1,N))) == 0);")
    #  (2) at the nodal points in characteristic 0 (disc = 0, t(t-1) != 0): u_i - u_1 = N(N-1)/2 (x_i - x_1)
    pari("""bb2 = a1^2 + 4*a2; bb4 = a1*a3; bb6 = a3^2; bb8 = a2*a3^2;
            disc = -bb2^2*bb8 - 8*bb4^3 - 27*bb6^2 + 9*bb2*bb4*bb6;
            Fd = factor(polresultant(f, disc, r)); qn = 0;
            for(a=1, matsize(Fd)[1], if(poldegree(Fd[a,1]) == n, qn = Fd[a,1]));
            tau = Mod(t, qn); Gm = gcd(subst(lift(f), t, tau)*Mod(1,qn), subst(disc, t, tau)*Mod(1,qn));
            r0 = -polcoeff(Gm, 0)/polcoeff(Gm, 1);""")
    pari("ev(e) = subst(subst(lift(e), r, r0), t, tau)")
    pari("chkNod = vector(n-1, i, ev(G[i]) == (N*(N-1)/2) * ev(X[i+1]-X[1]));")
    print("      remark 1 (system collapses mod N):", pari("chkN"), "; remark 2 (nodal points, t a root of %s):" % pari("qn"), pari("chkNod"))

    if N == 17:
        # comparison with the original formulation: C = lcm of the generic numerators of A_i, L_i = C/A_i,
        # V = D H L, F_i = V_i L_1 - V_1 L_i  (reduced mod f).  Formally F_i = D L_1 L_i (u_i - u_1).
        pari("""Ag = vector(n, i, (2*Yg[i] + a1*Xg[i] + a3) * prod(jj=1, n, if(jj==i, 1, Xg[i]-Xg[jj])));
                C = 1; for(i=1, n, C = lcm(C, numerator(Ag[i])));
                L = vector(n, i, C/Ag[i]);
                Dm = (r-t)^2*(t-1)^2*(r*t-2*r+1)^2;
                Hg = matrix(n, n, i, jj, xg(i+jj) - xg(i-jj)); V = Dm * Hg * L~;
                F = vector(n-1, i, (V[i+1]*L[1] - V[1]*L[i+1]) % f);""")
        print("      original formulation: total degree of C =", pari("tdeg(C)"))
        print("      (deg_r, deg_t) of reduced F_i:", pari("vector(n-1, i, [poldegree(F[i], r), poldegree(F[i], t)])"))
        print("      bridge d_i F_i == D L_1 L_i g_i (mod f):", pari("vector(n-1, i, (dG[i]*F[i] - Dm*L[1]*L[i+1]*g[i]) % f == 0)"))
        for i in range(1, n):
            pari("Rf = polresultant(f, F[%d], r); SF = strip(Rf);" % i)
            print("      Res_r(f, F_%d): degree %s = t^%s (t-1)^%s * (+-P_%d: %s)" % (
                i + 1, pari("poldegree(Rf)"), pari("SF[2]"), pari("SF[3]"), i + 1, pari("SF[1] == P[%d] || SF[1] == -P[%d]" % (i, i))))

json.dump(out, open("certificate.json", "w"), indent=1)
print("wrote certificate.json")
