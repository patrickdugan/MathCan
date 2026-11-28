"""AHR-QPU-01 simulator and strictly gated cloud entry point.

Default only simulates. Neither importing nor invoking this module in its default
mode accesses IBM Quantum, credentials, or any paid cloud resource.
"""
from __future__ import annotations
import argparse
import inspect
import json
import os
from pathlib import Path
import numpy as np
from exact_oracle import PHASE_OFFSETS,four_phase_probabilities,real_fourier_coefficient
from phase_estimator import quadrature,phase_from_quadrature,phase_fisher_information


def offline_report(t:float,theta:float,shots:int):
    p=four_phase_probabilities(t,theta)
    a1=real_fourier_coefficient(t)
    z=quadrature(p)
    return {'mode':'simulation_only','t':t,'phase_radians':theta,'shots_total':4*shots,
            'probabilities':p.tolist(),'a1':a1,
            'complex_quadrature':[float(z.real),float(z.imag)],
            'estimate_radians':float(phase_from_quadrature(z,a1)),
            'fisher':phase_fisher_information(t,theta,4*shots,nuisance=True)}


def live_job(args):
    if not args.authorize_cloud:
        raise RuntimeError('Cloud access requires --authorize-cloud, even for server dry-run')
    if not args.backend:
        raise RuntimeError('Supply an inspected IBM backend name with --backend')
    if args.mode=='hardware':
        if not args.instance:
            raise RuntimeError('Hardware requires an explicitly selected, verified Open Plan instance CRN')
        if not args.authorize_qpu or os.environ.get('AHR_QPU_ALLOW_LIVE_SUBMISSION')!='YES':
            raise RuntimeError('Hardware requires --authorize-qpu AND AHR_QPU_ALLOW_LIVE_SUBMISSION=YES')
        if os.environ.get('AHR_QPU_FREE_PLAN_VERIFIED')!='YES':
            raise RuntimeError('Explicit operator verification of a free-plan instance required')
    from qiskit_ibm_runtime import QiskitRuntimeService,Sampler
    from circuit_synthesis import build_circuit,transpile_for_backend
    # QiskitRuntimeService loads existing credentials; never log account or token.
    service=QiskitRuntimeService(instance=args.instance,plans_preference=['open'])
    backend=service.backend(args.backend)
    if backend.simulator:
        raise RuntimeError('Choose the intended physical backend for cloud pilot')
    circuits=[build_circuit(args.time,args.theta+d,method=args.method,reps=args.reps)
              for d in PHASE_OFFSETS]
    isa,metrics=transpile_for_backend(circuits,backend)
    metadata={'backend_name':args.backend,'circuits':metrics,'shots_per_circuit':args.shots,
              'mode':args.mode,'total_shots':4*args.shots}
    print(json.dumps(metadata,indent=2))
    sampler=Sampler(mode=backend)
    if args.mode=='dry_run':
        if 'dry_run' not in inspect.signature(sampler.run).parameters:
            raise RuntimeError('Current installed sampler does not advertise dry_run; HOLD')
        job=sampler.run(isa,shots=args.shots,dry_run=True)
        return {'mode':'dry_run','job_id':str(job.job_id()),'result_is_mock':True}
    job=sampler.run(isa,shots=args.shots)
    # On real hardware only the job id is returned immediately; never invent outcomes.
    return {'mode':'hardware','job_id':str(job.job_id()),'result_pending':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mode',choices=['simulation_only','compile_only','dry_run','hardware'],default='simulation_only')
    p.add_argument('--time',type=float,default=1.6)
    p.add_argument('--theta',type=float,default=.73)
    p.add_argument('--shots',type=int,default=2048,help='Per phase setting')
    p.add_argument('--method',choices=['exact','suzuki2'],default='exact')
    p.add_argument('--reps',type=int,default=4)
    p.add_argument('--backend',default=None)
    p.add_argument('--instance',default=None,help='Inspected Open Plan instance CRN; required for hardware')
    p.add_argument('--authorize-cloud',action='store_true')
    p.add_argument('--authorize-qpu',action='store_true')
    a=p.parse_args()
    if a.shots<1 or a.time<=0: raise SystemExit('Shots and time must be positive')
    if a.mode=='simulation_only':ret=offline_report(a.time,a.theta,a.shots)
    elif a.mode=='compile_only':
        from circuit_synthesis import select_synthesis
        ret=select_synthesis(a.time,a.theta+PHASE_OFFSETS)
    else:ret=live_job(a)
    print(json.dumps(ret,indent=2))

if __name__=='__main__':main()
