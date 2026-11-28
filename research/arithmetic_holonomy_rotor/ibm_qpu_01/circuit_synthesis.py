"""Optional Qiskit synthesis for AHR-01; dense oracle is independently tested.

Qubit 0 holds exponent of 2, qubit 1 exponent of 3; the statevector
ordering matches the basis index x + 2*y used in hamiltonian.py.
"""
from __future__ import annotations
import numpy as np
from scipy.linalg import expm
from hamiltonian import square_hamiltonian
from exact_oracle import exact_probabilities


def require_qiskit():
    try:
        import qiskit
        return qiskit
    except ImportError as exc:
        raise RuntimeError('Install optional requirements-qiskit.txt to compile circuits') from exc


def build_circuit(t:float, phi:float, method:str='exact',reps:int=4,
                  broken:bool=False,detuning:float=0.,measure:bool=True):
    require_qiskit()
    from qiskit import QuantumCircuit
    from qiskit.circuit.library import UnitaryGate, PauliEvolutionGate
    h=square_hamiltonian(phi,broken=broken,detuning=detuning)
    circuit=QuantumCircuit(2)
    if method=='exact':
        circuit.append(UnitaryGate(expm(-1j*t*h),label='AHR exact'),[0,1])
    elif method=='suzuki2':
        from qiskit.quantum_info import Operator,SparsePauliOp
        from qiskit.synthesis import SuzukiTrotter
        paulis=SparsePauliOp.from_operator(Operator(h)).simplify(atol=1e-12)
        circuit.append(PauliEvolutionGate(paulis,time=t,synthesis=SuzukiTrotter(order=2,reps=reps)),[0,1])
        circuit=circuit.decompose(reps=2)
    else: raise ValueError('method must be exact or suzuki2')
    if measure: circuit.measure_all()
    return circuit


def synthesis_check(t:float,phi:float,method:str,reps:int=4,
                    broken:bool=False,detuning:float=0.):
    from qiskit.quantum_info import Statevector,Operator
    circuit=build_circuit(t,phi,method,reps,broken,detuning,measure=False)
    state=Statevector.from_instruction(circuit).data
    target=expm(-1j*t*square_hamiltonian(phi,broken=broken,detuning=detuning))[:,0]
    overlap=np.vdot(target,state)
    aligned=state*np.conj(overlap)/abs(overlap)
    return {'method':method,'reps':reps,
            'statevector_error':float(np.linalg.norm(aligned-target)),
            'return_prob_circuit':float(abs(state[0])**2),
            'return_prob_exact':float(abs(target[0])**2),
            'return_prob_abs_error':float(abs(abs(state[0])**2-abs(target[0])**2)),
            'depth_untranspiled':circuit.depth(),
            'ops_untranspiled':dict(circuit.count_ops())}


def transpile_for_backend(circuits,backend,seed:int=20261123,optimization_level:int=3):
    require_qiskit()
    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    pm=generate_preset_pass_manager(backend=backend,optimization_level=optimization_level,seed_transpiler=seed)
    isa=[pm.run(c) for c in circuits]
    summary=[{'depth':c.depth(), 'ops':dict(c.count_ops()),
              'num_qubits':c.num_qubits,'layout':str(c.layout)} for c in isa]
    return isa,summary


def select_synthesis(t:float, phases, tolerance:float=.015, reps=(2,4,8)):
    """Select first acceptable method by return-prob error and native proxy depth.

    Proxy depth is only a provisional criterion until backend ISA transpilation.
    """
    methods=[('exact',0)]+[('suzuki2',r) for r in reps]
    summary=[]
    for method,r in methods:
        checks=[synthesis_check(t,p,method,r) for p in phases]
        summary.append({'method':method,'reps':r,
                        'max_return_prob_error':max(c['return_prob_abs_error'] for c in checks),
                        'max_untranspiled_depth':max(c['depth_untranspiled'] for c in checks),
                        'checks':checks})
    valid=[s for s in summary if s['max_return_prob_error']<=tolerance]
    if not valid: return {'selected':None,'comparisons':summary}
    chosen=min(valid,key=lambda s:(s['max_untranspiled_depth'],s['max_return_prob_error']))
    return {'selected':{'method':chosen['method'],'reps':chosen['reps']}, 'comparisons':summary,
            'note':'Native backend transpilation must determine final choice.'}
