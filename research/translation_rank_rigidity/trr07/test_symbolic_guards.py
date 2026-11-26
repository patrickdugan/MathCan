#!/usr/bin/env python3
"""Focused regression checks for new-order certificate replay guards.

Exercises empty input, order substitution, invalid residue fields and altered
fibre data. Each negative control must produce the expected diagnostic and a
nonzero exit. The original certificate and verifier files are hash-checked.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, timeout):
    start = time.monotonic()
    env = dict(os.environ, TRR_SYMBOLIC_SCAN_MAXP='7')
    proc = subprocess.run(command, text=True, capture_output=True, timeout=timeout, env=env)
    return dict(returncode=proc.returncode, elapsed_seconds=round(time.monotonic()-start,6),
                stdout=proc.stdout, stderr=proc.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=HERE/'symbolic_results/certificate19.json')
    parser.add_argument('--output', type=Path, default=HERE/'audit_symbolic_guards.json')
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args()
    certificate=args.certificate.resolve()
    original=json.loads(certificate.read_text())
    assert set(original)=={'19'}, 'This regression fixture must be the order-19 certificate.'
    replay=HERE/'symbolic_replay.py'
    node=HERE/'symbolic_verify.mjs'
    sources=[certificate,replay,node,HERE/'symbolic_generic.py']
    before={p.name:sha(p) for p in sources}
    baseline=run([sys.executable,str(replay),str(certificate),'--expected-order','19'],args.timeout)
    assert baseline['returncode']==0 and 'ALL CHECKS PASSED' in baseline['stdout'],baseline
    cases=[]
    with tempfile.TemporaryDirectory(prefix='trr07-symbolic-guards-') as temp:
        root=Path(temp)
        empty=root/'empty.json';empty.write_text('{}')
        specs=[
            ('empty_python', [sys.executable,str(replay),str(empty)], 'nonempty certificate dictionary required'),
            ('empty_node', ['node',str(node),str(empty)], 'nonempty certificate dictionary required'),
            ('expected_order_mismatch', [sys.executable,str(replay),str(certificate),'--expected-order','23'],
             'certificate order differs from requested job'),
        ]
        for name, diagnostic in [
            ('nonmonic_phi','field polynomial must be monic'),
            ('noncanonical_phi','coefficient outside prime-field range'),
            ('altered_gamma','[FAIL] fibre gcd over F_19^1 matches all stored coefficients'),
        ]:
            data=copy.deepcopy(original)
            factor=data['19']['primes']['19']['factors'][0]
            if name=='nonmonic_phi':
                factor['phi'][-1]='2'
            elif name=='noncanonical_phi':
                # Represents the same residue, but must fail before arithmetic.
                factor['phi'][0]=str(int(factor['phi'][0])+19)
            else:
                factor['Gamma'][0][0]=str((int(factor['Gamma'][0][0])+1)%19)
            path=root/f'{name}.json';path.write_text(json.dumps(data))
            specs.append((name,[sys.executable,str(replay),str(path),'--expected-order','19'],diagnostic))
        for name, command, expected in specs:
            outcome=run(command,args.timeout)
            combined=outcome['stdout']+outcome['stderr']
            rejected=outcome['returncode']!=0 and expected in combined
            cases.append(dict(name=name,rejected_as_expected=rejected,
                              expected_diagnostic=expected,returncode=outcome['returncode'],
                              elapsed_seconds=outcome['elapsed_seconds']))
            assert rejected,dict(name=name,expected=expected,**outcome)
    assert before=={p.name:sha(p) for p in sources}
    result=dict(schema='trr07-symbolic-guards-v1',status='passed',
                source_sha256=before,harness_sha256=sha(Path(__file__)),
                baseline=dict(returncode=baseline['returncode'],
                              ok_checks=baseline['stdout'].count('[ok]'),
                              elapsed_seconds=baseline['elapsed_seconds']),
                cases=cases,negative_controls_rejected=len(cases),
                sanity_scan_max_prime=7,
                scope='Full exact order-19 replay plus focused rejection guards; short sanity scan is not proof.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',guards_rejected=len(cases),receipt=str(args.output))))


if __name__=='__main__':
    main()
