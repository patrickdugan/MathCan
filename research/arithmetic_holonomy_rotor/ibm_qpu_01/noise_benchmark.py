"""Noise-model contracts: simple analytic channel + optional Qiskit Aer backend model."""
from __future__ import annotations
from phase_estimator import monte_carlo


def phenomenological_report(t:float=1.6,theta:float=.73,shots_total:int=8192,
                            replicates:int=1000,seed:int=20261123):
    configs=[('ideal',0.,0.),('independent_2pct_readout',.02,0.),
             ('global_5pct_depolarization',0.,.05),('both',.02,.05)]
    return {name:monte_carlo(t,theta,shots_total,replicates,seed,bitflip,depol)
            for name,bitflip,depol in configs}


def aer_simulate(circuits:list,shots:int=2048,seed:int=20261123,backend=None):
    """Optional noise-model simulation; calibration is fetched only from supplied backend."""
    from qiskit_aer import AerSimulator
    sim=AerSimulator.from_backend(backend) if backend is not None else AerSimulator()
    compiled=__import__('qiskit').transpile(circuits,backend=sim,seed_transpiler=seed)
    results=sim.run(compiled,shots=shots,seed_simulator=seed).result()
    return [{'counts':results.get_counts(i),'p00':results.get_counts(i).get('00',0)/shots}
            for i in range(len(compiled))]
