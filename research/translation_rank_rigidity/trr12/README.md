# TRR-12: ECDSA risk and the cost of evaluating a decoder

This update gives the security assessment a concrete model-scope control.
The forward decoder constrained by TRR-11 has an exact division-free
arithmetic circuit of size O(log q). Its large ordinary polynomial degree
and small evaluation circuit coexist. The new control checks every input
pair and assigned value on six synthetic prime-field curves.

Read [ECDSA risk and the evaluation program](ECDSA_RISK_ASSESSMENT.md) for
the assessment, current primary sources and empirical promotion gates.
The [scope proof](SCOPE_PROOF.md) gives the circuit, the complete case
argument and the degree-to-depth implication.

## Executed result

| Item | Result |
|---|---:|
| Small prime-field fixtures | 6 |
| Complete nonidentity input pairs | 4,624 |
| Circuit evaluations, including every assigned u | 130,464 |
| Inverse pairs | 160 |
| Tangent pairs | 160 |
| Rejected wrong-selector evaluations | 320 |

Static counting at the published secp256k1 field size gives 1,523 binary
field multiplications, twelve additions/subtractions and depth 507. The
TRR-11 degree bound implies a multiplicative-depth lower bound of 255 in
this circuit model. This exercise constructs and counts a symbolic gate
list from public parameters; its point evaluations are confined to the six
listed small fields.

The gate interpreter has no inverse or exponentiation primitive. Binary
powering is expanded into multiplication nodes. Formal block-degree
tracking yields syntactic upper bounds (4q-2, 3q-3), before cancellation.
The gate traces, fixture equations, marked points, assigned values and
source hash are retained in [circuit_scope_receipt.json](circuit_scope_receipt.json).
An [independent review](independent_review.json) recomputes the trace
bounds and checks the interpreter and final serialization.

## Scope and remaining work

The universal circuit identity has a written proof. This update adds no
Lean theorem; the 217-report TRR-11 audit retains its exact scope. The
new computation supplies an explicit control for claims connecting
polynomial degree to arithmetic cost.

[evaluation_plan.json](evaluation_plan.json) distinguishes the executed
control from planned candidate-recovery, signer and migration experiments.
The next Strategy V obligation is a cost-preserving connection from a
specified recovery method to the representation it must use. Scalar
recovery, nonce leakage and quantum capability have separate success and
cost criteria in the assessment.

## Reproduce

From this directory:

~~~sh
python circuit_scope_control.py --output /tmp/trr12-circuit-scope.json
cmp circuit_scope_receipt.json /tmp/trr12-circuit-scope.json
~~~

Python optimization is rejected because the exact controls use assertions.
The public workflow regenerates and compares the complete receipt, checks
that this guard fires before a file is created, and uploads its outputs.
Source and review hashes bind the receipt to the audited implementation.
