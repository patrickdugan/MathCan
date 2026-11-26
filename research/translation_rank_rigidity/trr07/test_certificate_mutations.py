#!/usr/bin/env python3
"""Replay the supplied certificate and reject deliberate changes to proof data.

The original verifier and certificate stay byte-for-byte unchanged. Each mutation
is run in a temporary JSON copy, with a finite per-process timeout. A crash alone
is not counted as a successful negative control: the verifier must print a FAIL
check and exit with status 1.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'trr05'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mutate(original, name):
    obj = copy.deepcopy(original)
    c = obj['17']
    if name == 'bezout_cofactor':
        c['W']['2'][0] = str(int(c['W']['2'][0]) + 1)
    elif name == 'residue_numerator':
        c['g']['2']['num'][0][0] = str(int(c['g']['2']['num'][0][0]) + 1)
    elif name == 'order_polynomial':
        c['f'][0][0] = str(int(c['f'][0][0]) + 1)
    elif name == 'norm_polynomial':
        c['P']['2'][0] = str(int(c['P']['2'][0]) + 1)
    elif name == 'localization_exponent':
        c['g']['7']['den_exp_t'] += 1
    elif name == 'norm_exponent':
        c['norm_exp']['7'][0] += 1
    elif name == 'certificate_integer':
        # Keep the prime set unchanged so this tests the integer identity.
        c['n0'] = str(2 * int(c['n0']))
    elif name == 'factor_multiplicity':
        c['primes']['17']['factors'][0]['mult'] -= 1
    elif name == 'fibre_root':
        roots = c['primes']['17']['factors'][0]['roots']
        roots[0]['rho'][0] = str((int(roots[0]['rho'][0]) + 1) % 17)
    elif name == 'fibre_multiplicity':
        c['primes']['17']['factors'][0]['roots'][0]['mult'] -= 1
    else:
        raise ValueError(name)
    return obj


def run(verifier, certificate, orders, timeout):
    started = time.monotonic()
    proc = subprocess.run(
        ['node', str(verifier), str(certificate), *map(str, orders)],
        capture_output=True, text=True, timeout=timeout,
    )
    return {
        'returncode': proc.returncode,
        'elapsed_seconds': round(time.monotonic() - started, 6),
        'ok_checks': proc.stdout.count('[ok]'),
        'failed_checks': [line.strip() for line in proc.stdout.splitlines() if '[FAIL]' in line],
        'stdout': proc.stdout,
        'stderr': proc.stderr,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE / 'audit_mutations.json')
    ap.add_argument('--timeout', type=int, default=180)
    args = ap.parse_args()
    verifier, source = BASE / 'verify.mjs', BASE / 'certificate.json'
    originals = {p.name: digest(p) for p in (verifier, source)}
    baseline = run(verifier, source, [], args.timeout)
    assert baseline['returncode'] == 0, baseline
    assert baseline['ok_checks'] == 83 and not baseline['failed_checks'], baseline
    assert 'ALL CHECKS PASSED' in baseline['stdout'], baseline
    original = json.loads(source.read_text())
    names = ['bezout_cofactor', 'residue_numerator', 'order_polynomial',
             'norm_polynomial', 'localization_exponent', 'norm_exponent',
             'certificate_integer', 'factor_multiplicity', 'fibre_root',
             'fibre_multiplicity']
    cases = []
    with tempfile.TemporaryDirectory(prefix='trr07-mutations-') as temp:
        for name in names:
            path = Path(temp) / f'{name}.json'
            path.write_text(json.dumps(mutate(original, name)))
            out = run(verifier, path, [17], args.timeout)
            accepted = out['returncode'] == 1 and bool(out['failed_checks'])
            cases.append({'name': name, 'rejected_as_expected': accepted,
                          **{k: v for k, v in out.items() if k not in ('stdout', 'stderr')}})
            assert accepted, {'name': name, **out}
    assert originals == {p.name: digest(p) for p in (verifier, source)}
    receipt = {
        'schema': 'trr07-certificate-mutations-v1', 'status': 'passed',
        'node_version': subprocess.check_output(['node', '--version'], text=True).strip(),
        'source_sha256': originals, 'harness_sha256': digest(Path(__file__)),
        'baseline': {k: v for k, v in baseline.items() if k not in ('stdout', 'stderr')},
        'mutations': cases,
        'scope': 'Proof-bearing certificate fields are tested; explanatory metadata fields are not proof inputs.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'baseline_checks': 83,
                      'mutations_rejected': len(cases), 'receipt': str(args.output)}))


if __name__ == '__main__':
    main()
