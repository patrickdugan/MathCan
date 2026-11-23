# AHR-QPU-01 · Signed arithmetic-square holonomy

This package prepares a two-qubit IBM pilot to recover a phase relative to a calibrated reference. It records exact predictions, independently simulated compiled circuits, Aer noise forecasts, finite-shot intervals and a simulation-only extension to the three-prime cube. [Results](RESULTS.md) · [Hardware gate](HARDWARE_GATE.md)

## Square and four-phase readout

Qiskit uses $x=q_0$ and $y=q_1$. The string order $|yx\rangle$ gives sites $1,2,3,6$ for $00,01,10,11$. The diagonal is $x\log 2+y\log 3$, and the four hoppings have magnitude one. The forward matrix element from site 2 to site 6 is $e^{i\phi}$. This fixes the positive orientation as $1\to2\to6\to3\to1$.

Prepare $|00\rangle$, evolve under the square Hamiltonian and measure $P_{00}$. Take four return measurements with phase offsets $\delta_j=j\pi/2$ and compute

$$
Z_4=\tfrac12\sum_j P_{00}(t,\theta+\delta_j)e^{-i\delta_j}
=\tfrac12\big[(P_0-P_\pi)+i(P_{3\pi/2}-P_{\pi/2})\big].
$$

For the fixed cycle the return probability is even in the total phase, with cosine coefficients $a_k(t)$. Discrete orthogonality gives $Z_4=a_1e^{i\theta}+a_3e^{-3i\theta}+a_5e^{5i\theta}+\cdots$. The second harmonic cancels. A calibrated independent zero-phase arm removes the shared phase offset and the sign of the real first harmonic. The estimator uses $\arg(Z_{\rm signal}\overline{Z_{\rm reference}})$ and exposes the remaining alias bias through 8-, 16- and 64-phase simulations.

The fixed schedule uses $t=0.8,1.2,1.6$, with the primary complex harmonic at $t=1.6$. The programmed validation targets are $\theta=+0.73$ and $\theta=-0.73$ radians and the shared programmed offset is $0.19$ radians. The zero target gets its own four samples at each time. The phase estimator uses the reference counts to infer the relative angle. At the primary time, extra arms reverse the signed target, cut the top edge to form a tree, and substitute the generic diagonal $(0,\log 6,\log 3,\log 2)$, which preserves the energy multiset. Case order is fixed by a saved seed.

For an isolated cycle each proper edge mask puts the phase on a forest. Its offset-dependent Fourier sum vanishes. Summing all 16 masks gives exactly the same complex quadrature expectation as the intact square. On the intact Q3 cube overlapping faces can keep the probe edge in a loop after a different face edge is removed. The simulator tests this failure and checks the AHR-08 local starting-corner selection at fourth order.

## Synthesis and estimation

The compiler uses a compact target built from the calibrated adjacent physical pair. It compares a full exact unitary with second-order Suzuki–Trotter using 2, 4 and 8 steps. It chooses the shallowest suite among those with worst-case ideal probability error and primary complex harmonic error both at most 0.005. A product-formula circuit is decomposed before the independent statevector comparison. The exported QPY embeds the selected circuits onto the verified physical qubits with unchanged classical bit labels.

The readout calibration defines a joint assignment vector over the two compact bits. The Aer density-matrix run applies the calibrated gate channels, then uses the assignment vector to obtain the predicted return probability. One-at-a-time sensitivity cases halve or remove the readout error or mix the calibrated two-qubit error channel with identity. The statistical benchmark uses 2,500 binomial replicates at both shot levels. The exhaustive comparison has the same **total** signal-plus-reference shots as the intact four-phase comparison.

Clopper–Pearson intervals propagated through the two complex components yield a simultaneous primary rectangle. The declared systematics are the largest absolute modeled residual in each component plus a 0.003 fixed allowance. For angles, the calibration and signal rectangles are each 97.5% before propagation. If either rectangle is too close to the origin for the enclosing-disc angle bound, phase identification remains unresolved. The Fisher bound uses the exact phase derivative of each Bernoulli probability and includes the uncertainty of the independently measured shared reference offset. Its scope is the specified basis-return readout.

## Reproduce

Run from this directory in a Python 3.12 virtual environment. The committed snapshot contains the public two-qubit device calibration and a reduced Aer noise model. Simulation can run offline.

~~~shell
python -m pip install -r requirements.txt
python experiment.py simulate --out runs/reproduced
python -m pytest -q
~~~

To refresh the calibration before an approved run, first create the runs directory and pass the path to a local IBM credential, or use the default Qiskit account or supported environment variable. Keep credentials outside the repository.

~~~shell
python experiment.py capture --backend ibm_fez --output runs/current-calibration.json --token-file PATH_TO_KEY
python experiment.py simulate --snapshot runs/current-calibration.json --out runs/current
~~~

Submission is gated separately by explicit approval and a free-allocation, calibration and receipt check. The authorized command and the conditions for using it are in the [hardware gate](HARDWARE_GATE.md). The local simulation and calibration-capture commands use zero QPU execution time. [IBM client-side Sampler](https://quantum.cloud.ibm.com/docs/en/api/qiskit-ibm-runtime/executor-sampler-sampler)

## Audit baseline

The branch started at MathCan main commit **cdbbc3100a20ea61036b78ef049306ba507280b8**. All seven requested merge commits are ancestors. The audit uses [AHR-01](../ahr01/AHR01_math_note.md) for the square, [AHR-02](../ahr02/AHR02_mathematics.md) for graph gauge covariance, [AHR-03](../ahr03/AHR03_symplectic_holonomy.md) for local fourth moments, [AHR-04](../ahr04/AHR04_spectral_rigidity_tomography.md), [AHR-05](../ahr05/AHR05_six_cycle_wilson_loops.md) and [AHR-06](../ahr06/AHR06_local_return_probability.md) for mixed edge toggles, and [AHR-07](../ahr07/AHR07_four_phase_holonomy_tomography.md), [AHR-08](../ahr08/AHR08_addressable_plaquette_curvature.md) and [AHR-09](../ahr09/AHR09_gauge_reconstruction.md) for the estimators and cubical reconstruction.

Diagonal vertex rephasing preserves all site probabilities. It can change bipartite concurrence because a graph gauge need not factor into local qubit operations. The package reproduces this counterexample. The experimental claims concern signed phase recovery in the specified finite model and readout.
