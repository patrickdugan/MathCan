"""Recompute reproducible AHR-QPU-01 numerical receipt; offline and deterministic."""
from __future__ import annotations
import json
import platform
import importlib.metadata
from pathlib import Path
import numpy as np
from exact_oracle import four_phase_probabilities,real_fourier_coefficient
from phase_estimator import quadrature,phase_from_quadrature,phase_fisher_information
from noise_benchmark import phenomenological_report
from mask_comparison import equal_budget_comparison
from q3_curvature import (EDGES,faces,face_fluxes,bianchi_residual,project_bianchi,
                          reconstruct_chords,measured_face_phase,measurement_schedule)
from shot_budget import shot_targets


def version(pkg):
    try:return importlib.metadata.version(pkg)
    except importlib.metadata.PackageNotFoundError:return None


def main():
    t=1.6;theta=.73;B=8192
    probs=four_phase_probabilities(t,theta)
    a1=real_fourier_coefficient(t)
    z=quadrature(probs)
    rng=np.random.default_rng(20261123)
    angles=rng.uniform(-.25,.25,len(EDGES))
    flux=face_fluxes(angles)
    q3=[measured_face_phase(angles,i,.12) for i in range(6)]
    receipt={'status':'PASS','seed':20261123,'provenance':{
        'python':platform.python_version(),'numpy':version('numpy'),'scipy':version('scipy'),
        'qiskit':version('qiskit'),'qiskit-aer':version('qiskit-aer'),
        'qiskit-ibm-runtime':version('qiskit-ibm-runtime')},
        'q2':{'time':t,'implanted_phase':theta,'phase_offsets':[0,float(np.pi/2),float(np.pi),float(3*np.pi/2)],
              'return_probabilities':probs.tolist(),'first_harmonic_a1':a1,
              'quadrature':[float(z.real),float(z.imag)],
              'estimated_phase':float(phase_from_quadrature(z,a1)),
              'conditional_fisher':phase_fisher_information(t,theta,B,True),
              'shot_target':shot_targets(t,theta)},
        'noise':phenomenological_report(t,theta,B,1000),
        'masked_equal_budget':equal_budget_comparison(t,theta,B,1000),
        'q3':{'faces':faces(),'controlled_schedule':measurement_schedule(),
              'bianchi_residual':bianchi_residual(flux),
              'reconstructed_chords':reconstruct_chords(flux).tolist(),
              'projected_bianchi_residual':bianchi_residual(project_bianchi(flux)),
              'addressed_faces':q3,
              'short_time_note':'Full-cube exact dense matrix; t=0.12; finite-time O(t^2) angular bias'}}
    assert receipt['masked_equal_budget']['ideal_quadrature_discrepancy']<1e-10
    assert max(abs(x['angular_error']) for x in q3)<.004
    out=Path(__file__).parent/'receipts'/'offline_validation.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','a1':a1,'phase_estimate':receipt['q2']['estimated_phase'],
        'phase_rmse_deg':receipt['noise']['ideal']['rmse_deg'],
        'masked_rmse_deg':receipt['masked_equal_budget']['masked_rmse_deg'],
        'q3_max_phase_error_rad':max(abs(x['angular_error']) for x in q3)},indent=2))

if __name__=='__main__':main()
