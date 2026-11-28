# AHR-09: reconstructing the cube gauge field from six measured face phases

**2026-11-23.** Project-specific constructive version of standard cubical cochain exactness. Includes a noise-reduction result. This is mathematical/numerical research with no Lean kernel proof and no quantum hardware data.

## Full U(1) reconstruction modulo vertex gauge

On the 3-cube there are eight vertices, twelve edges, six oriented faces and one 3-cell. Define torus-valued cubical cochains C^0=T^8, C^1=T^12, C^2=T^6, C^3=T, where T=R/(2pi Z). Let d0 send vertex phase to edge gradient, d1 send edge connection to face curl, and d2 sum oriented boundary faces. Their integer incidence matrices satisfy

\[
d_1d_0=0,\qquad d_2d_1=0,
\]

and have exact ranks

\[
\boxed{\operatorname{rank}d_0=7,\quad\operatorname{rank}d_1=5,\quad
\operatorname{rank}d_2=1.}
\tag{AHR-09A}
\]

The Smith normal form of d1 has nonzero diagonal (1,1,1,1,1). Thus a six-component face-flux vector F is the curl of an edge connection precisely when its one Bianchi constraint holds modulo 2pi, and two connections producing the same F differ only by vertex gauge.

Using ordered faces (01,z=0), (01,z=1), (02,y=0), (02,y=1), (12,x=0), (12,x=1), the Bianchi row is

\[
\boxed{b=(-1,+1,+1,-1,-1,+1),\quad bF=0\pmod{2\pi}.}
\tag{AHR-09B}
\]

The six phase measurements from AHR-08 contain exactly the five independent gauge-invariant cycle degrees of freedom. The sixth serves as an experimental consistency check.

## Explicit tree-gauge inverse

Take the seven-edge spanning tree

\[
T=\{(0,1),(0,2),(0,4),(1,3),(1,5),(2,6),(3,7)\}.
\]

Gauge all tree edges to phase zero by recursively assigning vertex phases. The remaining five chords are

\[
E\setminus T=\{(2,3),(4,5),(4,6),(5,7),(6,7)\}.
\]

Restrict d1 to these five chord columns, obtaining a 6x5 integer matrix M. For this tree, removing **any one** face row gives a 5x5 submatrix with determinant +1 or -1. Hence the gauge-fixed chord angles can be reconstructed from any five consistent measured face phases:

\[
\boxed{a_{\mathrm{chord}}=M_5^{-1}F_5\pmod{2\pi}.}
\tag{AHR-09C}
\]

This is a constructive inverse: every additional face flux becomes a Bianchi prediction once five independent values are known. The phase branches must be handled consistently when measurements carry noise.

## Bianchi-constrained noise projection

Let observed face phases be locally unwrapped on a consistent branch, with additive zero-mean error epsilon of covariance sigma^2 I_6. Define the wrapped Bianchi residual r=wrap(b F_obs) in (-pi,pi]. The minimum Euclidean adjustment is

\[
\boxed{F_{\mathrm{proj}}=F_{\mathrm{obs}}-\frac{b^T}{6}r.}
\tag{AHR-09D}
\]

The projection discards one of six independent noise directions. In the small-error, correct-branch regime its expected sum-squared mean-square error obeys

\[
\boxed{\frac{E\|F_{\mathrm{proj}}-F\|^2}{E\|F_{\mathrm{obs}}-F\|^2}
=\frac56.}
\tag{AHR-09E}
\]

For positive definite correlated covariance Sigma, the generalized least-squares correction is

\[
F_{\mathrm{proj}}=F_{\mathrm{obs}}-\Sigma b^T(b\Sigma b^T)^{-1}r.
\]

Large measurement noise or branch crossings require a wrapped-phase inference procedure. This projection improves stochastic errors; it does not cancel finite-time systematic bias from the AHR-08 local measurement.

## Reproducible numerical receipts

Run python ahr09_ci.py using NumPy and SymPy. It verifies the integer cochain products, ranks (7,5,1), Smith diagonal (1,1,1,1,1,0), the tree inverse on 100 random gauge fields, and 20,000 Gaussian-noise replicates at sigma=0.08 rad.

Maximum wrapped chord-reconstruction discrepancy: 2.6645352591003757e-15 rad.
Predicted MSE ratio 0.8333333333333334.
Simulated ratio 0.8348981513492993.
Raw sum-squared MSE 0.038685626602590326; projected 0.03229855813429194.

AHR-08's three programmable edges and 24 face-scan circuits supply the intended measurements, but compiled quantum gates, calibration, and hardware shot budgets remain separate research gates. The 2-qubit AHR-07 four-phase run is the lower-cost first hardware candidate. No RH or machine-consciousness claim follows from this cube cochain theorem.
