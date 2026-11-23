# AHR-QPU-01 · Numerical audit and pilot predictions

All results in this report come from finite-dimensional calculation or local simulation. IBM authentication and the read-only calibration capture supplied the two-qubit noise model and resource snapshot. The hardware gate remains on hold pending explicit authorization. [Hardware gate](HARDWARE_GATE.md)

## Mathematics audit

The spectral decomposition and an independent literal matrix exponential agreed within $6.7\times10^{-16}$ on the square. Diagonal rephasing preserved the returns to that tolerance. All 15 proper edge masks were phase invariant to $8.9\times10^{-16}$. The masked and intact complex quadratures agreed to $6.6\times10^{-16}$ at the tested phases.

The first three cosine coefficients at $t=1.6$ were $-0.25509420$, $+0.03997757$, and $+0.00042753$, reproducing the AHR-07 benchmark. Synthetic harmonics independently verified the cancellation of the second and the conjugate alias of the third. For the primary programmed phase, the four-setting alias amplitude was $4.28\times10^{-4}$, with angular bias about $-0.049^\circ$ before reference correction. The eight-setting first DFT agreed with the dense 256-phase reference to floating-point precision in this fixture.

The exact positive and reversed targets give opposite relative signs after reference calibration. The calibrated Aer reversed angle is approximately −42.12°. The tree has constant exact $P_{00}=0.33278$ over the four primary offsets. The generic diagonal control preserves the four energy values and produces a different first-harmonic magnitude. An independent zero-detuning product state has gauge-copy concurrence $0.51460$ after a diagonal CZ rephasing even though the original state has concurrence zero. Its site probabilities are identical. [Math receipt](receipts/mathematical_audit.json) · [All Q2 phase data](receipts/q2_protocol.json)

## Q2 compilation and noise

| Synthesis | Total depth | Max depth | Native CZ count | Worst return error | Primary harmonic error |
| --- | ---: | ---: | ---: | ---: | ---: |
| **Exact** | **596** | 20 | **76** | $3.5\times10^{-15}$ | $2.1\times10^{-16}$ |
| Suzuki–Trotter 2 | 608 | 20 | 80 | 0.23378 | 0.09124 |
| Suzuki–Trotter 4 | 720 | 20 | 108 | 0.05684 | 0.02216 |
| Suzuki–Trotter 8 | 720 | 20 | 108 | 0.01395 | 0.00547 |

Exact synthesis passed both 0.005 accuracy gates and had the lowest aggregate depth. The compact compiled Aer statevector agreed with the independently evaluated, decomposed source circuit at every case. The selected full-width QPY encodes the physical pair $9,10$ with the original logical measurement bit order. [Circuit metrics](receipts/q2_compilation.json) · [Case probabilities](receipts/q2_cases.csv)

At $t=1.6$, the exact raw signal quadrature is $-0.154938-0.203113i$. Calibrated Aer gives $-0.152760-0.200135i$. The Aer reference-calibrated angle is $0.72565$ radians for the $0.73$-radian fixture. Synthetic counts rounded to the calibrated Aer means at 2,048 shots give this simultaneous raw-harmonic rectangle and planned allowance.

| Component | 95% counting rectangle | Added systematic allowance |
| --- | --- | ---: |
| Real | $[-0.17361,-0.13088]$ | 0.00518 |
| Imaginary | $[-0.22016,-0.17933]$ | 0.00598 |

The exact target falls in the expanded rectangle for that planning case. The allowance covers the maximum ideal-to-modeled shift across the nominal and sensitivity scenarios plus 0.003 per component. This defines an acceptance rule for new measurements. It does not bound unmodeled hardware drift. The reference-plus-signal conservative phase half-width for the planning case is about 15.1°. The corresponding Monte Carlo RMSE is smaller because it describes the typical error under a fixed simulator model rather than a simultaneous worst-case projection.

## Finite-shot angle forecasts

At the primary endpoint, 2,500 replicates per option give the following. Both estimators debit the signal and independently measured reference from the same total budget. The intact method uses eight settings across both arms. The exhaustive method uses 128.

| Per-setting intact shots | Total shots across both arms | Calibrated Aer angular bias | Calibrated Aer angular RMSE | Ideal intact RMSE | Ideal exhaustive RMSE | Conditional Fisher SD floor |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2,048 | 16,384 | −0.24° | 2.01° | 1.95° | 29.56° | 1.96° |
| 8,192 | 65,536 | −0.25° | 1.06° | 0.98° | 13.58° | 0.98° |

The two ideal methods have the same mean complex harmonic. Their phase estimators are nonlinear, so the noisier exhaustive estimates can wrap. The calibrated-noise Monte Carlo gives about 32.5° RMSE at $t=0.8$ and 8.35° at $t=1.2$ with 2,048 shots per setting. These early points test the model and the sign change of the first harmonic. They are secondary to the primary time.

At the primary endpoint, the modeled 2,048-shot RMSE ranges from about 1.97° with readout error removed to 2.01° under the nominal model. Removing the calibrated two-qubit channel alone gives about 2.02°. These closely spaced shot forecasts are sensitive to Monte Carlo sampling and describe the selected Aer model. They do not isolate coherent error in the device.

For a Bernoulli return probability $p_j(\theta)$ and allocation $n_j$, the phase-score variance is $I=\sum_j n_j(p_j')^2/[p_j(1-p_j)]$. Let $I_s$ be the signal information and $I_r$ the reference information. The signal depends on $\theta+\beta$ and the reference on $\beta$, so their combined Fisher matrix for $(\theta,\beta)$ is

$$
\begin{pmatrix}I_s & I_s\\ I_s & I_s+I_r\end{pmatrix}.
$$

Its inverse gives the conditional local variance floor $I_s^{-1}+I_r^{-1}$ for $\theta$. [Shot, noise and Fisher receipts](receipts/q2_protocol.json)

## Q3 local curvature and reconstruction

Three selectable probe edges, $(0,1),(2,6),(5,7)$, cover the six coordinate-oriented cube faces. The starting corner opposite each probe selects one face through fourth order. The independent NumPy, SciPy and Qiskit site probabilities agree within $1.3\times10^{-15}$. In the wrong-corner test, the normalized complex estimate differs from the requested face by 0.849 and converges to the other face. On the intact cube a surviving overlapping loop gives a 0.00390 failure of the unicyclic mask identity at the simulated test time.

| Face | True phase | Local estimate at 0.4 | Two-time estimate | Bianchi-projected estimate |
| --- | ---: | ---: | ---: | ---: |
| $xy,\ z=0$ | −1.73353 | −1.73232 | −1.73336 | −1.73397 |
| $xy,\ z=1$ | +1.73175 | +1.73672 | +1.73234 | +1.73294 |
| $xz,\ y=0$ | −0.85536 | −0.85833 | −0.85567 | −0.85507 |
| $xz,\ y=1$ | −2.84178 | −2.82848 | −2.84014 | −2.84074 |
| $yz,\ x=0$ | −1.94259 | −1.92893 | −1.93978 | −1.94039 |
| $yz,\ x=1$ | −1.11111 | −1.10673 | −1.11039 | −1.10979 |

The Bianchi row is $(-1,1,1,-1,-1,1)$. The cochain ranks are $(7,5,1)$. The inverse of five independent face rows reconstructs chord angles in the AHR-09 spanning-tree gauge. All six predicted faces agree with the projected phases to $8.9\times10^{-16}$ radians. In the separate small Gaussian-noise test, the projected-to-raw mean-square error ratio is 0.831, close to the expected $5/6$.

Deduplicating the shared zero-offset preparation saves one measured circuit per time. The one-time schedule drops from 24 to 23 settings. The two-time schedule drops from 48 to 46 settings. The Monte Carlo reuses the shared counts, which couples the affected face errors. At 2,048 shots per setting the Q3 angular RMSE is about 88° with one time and 102° with equal-shot Richardson. In this low-information regime the experiment frequently crosses phase branches, and Bianchi projection does not improve precision. A 10° target needs roughly 1.73 million shots per face under the leading-order conditional bound. [Full Q3 receipt](receipts/q3_curvature.json) · [Resource gate](HARDWARE_GATE.md)
