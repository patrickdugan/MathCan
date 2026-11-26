# TRR-12: high interpolation degree with a small evaluation circuit

## Statement and relation to TRR-11

Let K be a finite field of size q and characteristic greater than three. Let
E: y^2 = x^3 + Ax + B be smooth, let G be an odd-order subgroup, and put
S = G minus the identity. For any assigned scalar u, the map
(P,Q) -> f_u(P+Q) on S x S admits a division-free arithmetic circuit with
O(log q) binary field operations. The circuit uses the coordinates of P and
Q, the public field size and curve coefficient A, and u.

For comparison with TRR-11, assume in addition that G is cyclic. TRR-11
independently proves that every polynomial representing this map has
maximum ordinary degree in the two coordinate blocks at least ceil(N/3)
when N=|G|>=19 and N is nonzero in K. These statements hold simultaneously:
the circuit compactly evaluates a polynomial of high degree.

The following proof is written mathematics. The new circuit construction is
checked on exact prime-field fixtures; it has not been formalized in Lean.
TRR-11 retains its existing Lean verification and hypotheses.

## A polynomial that selects the group-law cases

For z in K define I(z)=z^(q-2) and Z(z)=1-z^(q-1). Since q>3,
I(0)=0, while I(z)=z^(-1) for nonzero z. Also Z(z)=1 exactly when z=0,
and is zero otherwise. These identities follow from the order q-1 of K*.

Write P=(x1,y1), Q=(x2,y2), a=x2-x1 and b=y2-y1. Put

\[
X_{sec}=(bI(a))^2-x_1-x_2,\qquad
X_{tan}=((3x_1^2+A)I(2y_1))^2-2x_1.
\]

Then define the single polynomial

\[
D=(1-Z(a))X_{sec}+Z(a)Z(b)X_{tan}
  +Z(a)(1-Z(b))u.
\]

If a is nonzero, its first selector is one and the other terms vanish.
The remaining expression is the ordinary secant formula for x(P+Q).

If a=0, the curve equation gives y2^2=y1^2. A nonidentity point in an
odd-order group has y1 nonzero: otherwise it equals its inverse and has
order two. Therefore y2=y1 and y2=-y1 are distinct possibilities. In the
first case b=0, the tangent selector is one and 2y1 is invertible. The
output is x(2P). In the other case b=-2y1 is nonzero, Q=-P, and the
identity selector returns precisely u. This proves the identity on all of
S x S, including every inverse pair.

## Count the circuit that evaluates this polynomial

Binary powering evaluates z^e with

\[
\ell(e)+\operatorname{popcount}(e)-2
\]

multiplications for a positive exponent e, where ell is bit length. The
implementation starts from z and processes the remaining exponent bits.
There is no unit-cost exponentiation instruction in its recorded circuit.

The circuit computes two powers with exponent q-2 and one with exponent
q-1. It obtains Z(a) as 1-aI(a), so a separate exponentiation for Z(a) is
unnecessary. The remaining expression costs fourteen multiplications and
twelve additions or subtractions. Thus the exact multiplication count is

\[
2(\ell(q-2)+\operatorname{popcount}(q-2)-2)
+\ell(q-1)+\operatorname{popcount}(q-1)-2+14.
\]

In particular it is at most 6 ceil(log2(q))+8. Multiplication by constants
is charged. All degree statements treat the assigned u as a coefficient;
it is an input parameter to the interpreter with block degree zero.

The gate-by-gate degree propagation gives upper bounds (4q-2, 3q-3) on the
ordinary degrees in the two coordinate pairs. Addition takes the maximum
of the two incoming bounds, and multiplication adds them. These are
syntactic upper bounds before cancellation or reduction by curve and
field equations. They are distinct from the minimum degree among all
polynomial representatives established by TRR-11.

For arbitrary finite extensions, field multiplication has its own bit
cost. The O(log q) count is a field-operation count, with the field
representation supplied. It concerns evaluation of the forward group
operation.

## What degree alone implies about circuit depth

For a division-free circuit whose input coordinates have degree one and whose
multiplication gates have fan-in two, a polynomial at multiplicative depth
h has degree at most 2^h. This follows by induction on gates: addition
preserves the maximum degree, and multiplication at the next level adds
two degrees bounded by 2^(h-1). Consequently TRR-11 implies

\[
h\ge\left\lceil\log_2\left\lceil N/3\right\rceil\right\rceil.
\]

At the published secp256k1 parameter sizes, this lower bound is 255. The
explicit circuit above has multiplicative depth 507, 1,523 multiplication
gates, and twelve addition/subtraction gates. These figures are exact
static accounting of a gate list built from the public p and n. The
script performs no point evaluation at that parameter size and does not
prove parameter primality. It imports the parameter values from
[SEC 2, section 2.4.1](https://www.secg.org/sec2-v2.pdf).

The exponential polynomial degree therefore supports a logarithmic depth
bound in this circuit model. A stronger attack-cost conclusion needs
additional assumptions about the permitted representation or algorithm.

## Executed controls

The checker independently enumerates complete smooth curves of prime
orders on six small prime fields. It verifies the marked point's exact
order by repeated addition and checks that its subgroup contains every
enumerated point. The rational reference evaluator uses modular inverse;
the circuit evaluator only replays input, constant, addition, subtraction
and multiplication nodes.

| p | A | B | T | N | Minimum degree from TRR-11 |
|---:|---:|---:|---|---:|---:|
| 17 | 2 | 2 | (0,6) | 19 | 7 |
| 19 | 2 | 9 | (0,3) | 23 | 8 |
| 23 | 1 | 4 | (0,2) | 29 | 10 |
| 29 | 1 | 12 | (2,14) | 23 | 8 |
| 31 | 0 | 3 | (1,2) | 43 | 15 |
| 37 | 1 | 12 | (0,7) | 29 | 10 |

All 4,624 input pairs were evaluated for every u in the corresponding
field, giving 130,464 checks. There are 160 inverse pairs and 160 tangent
pairs. A corrupted identity selector fails on all 320 of those pairs at
u=1. The receipt includes the small-field gate traces, source hash, degree
bounds and operation counts. Optimized Python execution is rejected before
writing a receipt, so assertion removal cannot silently accept the audit.

The mathematical construction applies over every finite field in the
stated characteristic range. The executable cohort uses the six listed
prime fields. An independent review traverses the frozen gate traces and
checks the circuit interpreter for hidden exponentiation operations.

## Connection required for a security claim

A scalar-recovery algorithm receives G and Q=[d]G and must return d. The
decoder evaluated here receives two points and returns one coordinate of
their sum. A claim about recovery cost must establish a reduction between
its computational model and the specific representation measured by
TRR-11. That reduction must charge coefficient construction, preprocessing,
auxiliary variables, branches, memory and arithmetic circuit sharing.

The circuit above is a required control for such a reduction. Any proposed
bound that would label this forward evaluation exponentially expensive
has failed to preserve the relevant computational cost.
