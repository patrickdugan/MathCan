import numpy as np
import pytest
qiskit=pytest.importorskip('qiskit')
from circuit_synthesis import build_circuit,synthesis_check


def test_exact_unitary_qiskit_ordering():
    for theta in (0,.73,np.pi):
        x=synthesis_check(1.6,theta,'exact')
        assert x['statevector_error']<1e-10
        assert x['return_prob_abs_error']<1e-10


def test_second_order_suzuki_convergence():
    x=synthesis_check(.2,.73,'suzuki2',reps=2)
    y=synthesis_check(.2,.73,'suzuki2',reps=8)
    assert y['return_prob_abs_error']<x['return_prob_abs_error']+.00001
    assert y['return_prob_abs_error']<.01


def test_compile_isa_proxy_basis():
    from qiskit import transpile
    from qiskit.quantum_info import Statevector
    circuit=build_circuit(1.6,.73,'exact',measure=True)
    isa=transpile(circuit,basis_gates=['rz','sx','x','cx','measure'],
                  coupling_map=[[0,1],[1,0]],optimization_level=3,seed_transpiler=20261123)
    assert isa.num_qubits==2
    assert isa.count_ops().get('cx',0)<=5
    assert isa.depth()>0


def test_optional_aer_counts():
    pytest.importorskip('qiskit_aer')
    from noise_benchmark import aer_simulate
    c=build_circuit(.8,.73,measure=True)
    result=aer_simulate([c],shots=256)
    assert sum(result[0]['counts'].values())==256
