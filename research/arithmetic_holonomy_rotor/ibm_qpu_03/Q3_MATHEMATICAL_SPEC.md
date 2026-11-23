# Three-prime arithmetic cube

Let the vertex index be $v=x+2y+4z$. The site is $2^x3^y5^z$ with $x,y,z\in\{0,1\}$. Qiskit orders statevectors as $|zyx\rangle$ with $x=q_0$. The site energy is $E_v=x\log2+y\log3+z\log5$.

For each sorted edge $e=(u,v)$ in the cube set $H_{uv}=J_e e^{iA_e}$ and $H_{vu}=\overline{H_{uv}}$. Use $J_e=1$ for the standard protocol. Broken-cycle controls may remove edges. A vertex rephasing $D=\operatorname{diag}(e^{ig_u})$ sends $A\mapsto A-d_0g$ and $H\mapsto DHD^\dagger$, leaving every site return invariant. The merged QPU-01 code stores the forward phase in $H_{vu}$, so a sign conversion is required to compare matrices.

## Integer cochains

Orient edges from lower to higher vertex. Orient a face in axes $i<j$ as $u\to u\oplus 2^i\to u\oplus 2^i\oplus 2^j\to u\oplus 2^j\to u$. Face order is $xy_{z=0},xy_{z=1},xz_{y=0},xz_{y=1},yz_{x=0},yz_{x=1}$. With coboundaries $d_0,d_1,d_2$, the entries of $d_1$ are signed edge incidences and $d_2=b^T$ for $b=(-1,1,1,-1,-1,1)^T$.

Products $d_1d_0$ and $d_2d_1$ vanish over the integers. A rooted tree incidence minor has determinant ±1 and the constant vertex field is a null vector, so $\operatorname{rank}d_0=7$. The first five faces and the five chord columns form a square identity after multiplication by the implemented integer inverse. This unit minor, together with the Bianchi relation, proves rank 5 and fixes all five nonzero Smith factors to 1. The nonzero row $d_2$ has rank 1.

The tree uses $(0,1),(0,2),(0,4),(1,3),(1,5),(2,6),(3,7)$. In its gauge the remaining chords are $(2,3),(4,5),(4,6),(5,7),(6,7)$. Set the seven tree phases to zero and invert the first five oriented faces with the integer inverse stored in the provenance receipt. All angle comparisons are modulo $2\pi$.

## Local response and aliasing

For a marked face start at a vertex on that face away from the programmable edge. This vertex belongs to only one of the two squares incident on that edge. Add the offset $\delta$ with the sign of the marked edge in the oriented face. Take $P_x=|\langle x|e^{-itH}|x\rangle|^2$ and $Z_f=\frac12\sum_{j=0}^3P_x(\delta_j)e^{-i\delta_j}$ with $\delta_j=j\pi/2$.

The first marked-edge term in the site return comes from the two oriented four-step paths in $\langle x|H^4|x\rangle$. They contribute $2W_f\cos(F_f+\delta)$, where $W_f=\prod_{e\in\partial f}J_e$. The amplitude coefficient is $t^4/4!$ and taking the squared modulus doubles it, giving $W_ft^4\cos(F_f+\delta)/6$ in the probability. Since the probability is even in time, the next correction starts at order $t^6$. The stated Fourier normalization yields $Z_f=W_ft^4e^{iF_f}/6+O(t^6)$. A wrong start on the marked edge sees both incident face paths at leading order.

For a real periodic probability scan, the discrete four-phase coefficient aliases the negative-frequency third harmonic into the positive first harmonic. Eight phases remove this particular alias. Longer walks can still move the true first harmonic away from the target curvature. Richardson combines the two calibrated complex ratios $2R(t/\sqrt2)-R(t)$ under the local even expansion $R(t)=e^{iF}+O(t^2)$. Its small-time bias benefit can be offset by shot noise at the smaller time.

## Projection and likelihood

Local wrapped projection uses $r=\operatorname{wrap}(b^TF)\$ and $F'=\operatorname{wrap}(F-\Sigma b r/(b^T\Sigma b))$. Propagate $\Sigma'=\Sigma-\Sigma b b^T\Sigma/(b^T\Sigma b)$ and apply the integer chord inverse to the appropriate five entries. When the latent Bianchi residual can cross ±π, the nearest wrapped hypothesis can select a different branch. A zero projected residual follows algebraically. The raw residual and the controls provide compatibility diagnostics.

The likelihood fits five chord phases directly and therefore lives in the Bianchi-compatible subspace. It models each return as binomial about the exact eight-state response after the trained Aer transfer and shared nuisance perturbations. The spectral divided difference gives analytic derivatives through near-degenerate eigenvalues. The reported Fisher matrix includes the shared nuisance parameters and their Gaussian prior information. Numerical fit coverage is conditional on the prepared local chart and the held-out calibration stress model.
