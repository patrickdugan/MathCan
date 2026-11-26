#!/usr/bin/env python3
"""Summarize CI receipts, keeping completed searches distinct from exclusions."""
import argparse
import hashlib
import json
from pathlib import Path


def certificate_replay(path, order):
    """Bind a successful replay to the certificate produced in this CI job."""
    certificate = path.with_name(f'certificate{order}.json')
    receipt = path.with_name('flint-replay.json')
    if not certificate.exists() or not receipt.exists():
        return False, 'missing independent replay'
    data = json.loads(receipt.read_text())
    digest = hashlib.sha256(certificate.read_bytes()).hexdigest()
    source_hashes = {
        name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        for name in ('flint_replay.py', 'symbolic_generic.py', 'symbolic_norm_replay.py', 'uniform_probe.md')
    }
    elimination = data.get('elimination_and_fibres', {})
    valid = (
        data.get('schema') == 'trr07-flint-certificate-replay-v1'
        and data.get('status') == 'passed'
        and data.get('order') == order
        and data.get('certificate_sha256') == digest
        and data.get('source_sha256') == source_hashes
        and data.get('ratio_identities') == (order - 3) // 2
        and elimination.get('status') == 'passed'
        and elimination.get('certificate_sha256') == digest
        and [row.get('order') for row in elimination.get('orders', [])] == [order]
    )
    return valid, 'FLINT residue reconstruction and elimination' if valid else 'incomplete or mismatched independent replay'


def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--markdown',type=Path,required=True)
    args=ap.parse_args();rows=[];errors=[];seen_orders=set();schemas=set();cohorts=set()
    for path in sorted(args.directory.rglob('*.json')):
        d=json.loads(path.read_text());schema=d.get('schema','')
        if not schema:continue
        schemas.add(schema)
        if schema=='trr07-symbolic-search-v1':
            n=d['order'];seen_orders.add(n);replay=path.with_name('replay.log')
            verified,method=certificate_replay(path,n)
            direct=bool(replay.exists() and 'ALL CHECKS PASSED' in replay.read_text())
            status='certificate independently replayed' if verified else d.get('status','unknown')
            if status=='error' or not verified:errors.append(f'{path}: {method}')
            if n<=23 and not direct:errors.append(f'{path}: missing direct H-lambda replay')
            rows.append(dict(experiment=f'symbolic order {n}',status=status,
                             last_stage=d.get('last_stage'),receipt=str(path),proof=verified,
                             replay_method=method,direct_H_lambda_replay=direct))
        elif schema=='trr07-finite-sweep-v1':
            cohorts.add(path.parent.name)
            c=d['counts'];complete=not d.get('errors') and all(f.get('complete',False) for f in d['fields'])
            if not complete:errors.append(str(path))
            if c.get('new_smooth_exception',0):errors.append(f'{path}: new smooth exception requires review')
            rows.append(dict(experiment=path.parent.name,status='complete finite cohort' if complete else 'incomplete',
                             models=c.get('smooth_models',0),subgroups=c.get('subgroup_instances',0),
                             known_order5_drops=c.get('exceptions',0)-c.get('new_smooth_exception',0),
                             new_smooth_exceptions=c.get('new_smooth_exception',0),receipt=str(path),proof=False))
        elif schema=='trr07-robustness-v1':
            rows.append(dict(experiment='robustness',status='finite controls passed',
                             cases=d['cases'],exact_distances=d['exact_function_distances'],receipt=str(path),proof=False))
        elif schema in ('trr07-certificate-mutations-v1','trr07-symbolic-audit-v1','trr07-lean-algebra-v1',
                        'trr07-uniform-lean-v1','trr07-symbolic-guards-v1','trr07-uniform-exclusion-v1',
                        'trr07-elimination-mutations-v1','trr07-flint-bridge-guards-v1'):
            rows.append(dict(experiment=schema,status=d.get('status','completed'),receipt=str(path),
                             geometry_formalized=d.get('geometry_formalized',False)))
            if d.get('status')!='passed':errors.append(f'{path}: audit did not pass')
    for n in [19,23,29,31]:
        if n not in seen_orders:
            rows.append(dict(experiment=f'symbolic order {n}',status='missing receipt',proof=False));errors.append(f'missing order {n}')
    required=['trr07-finite-sweep-v1','trr07-robustness-v1','trr07-certificate-mutations-v1','trr07-lean-algebra-v1',
              'trr07-uniform-lean-v1','trr07-symbolic-guards-v1','trr07-uniform-exclusion-v1','trr07-symbolic-audit-v1',
              'trr07-elimination-mutations-v1','trr07-flint-bridge-guards-v1']
    errors += [f'missing {s}' for s in required if s not in schemas]
    errors += [f'missing finite cohort {c}' for c in ['trr07-prime-exhaustive','trr07-extension-exhaustive',
                'trr07-extension-small','trr07-extension-large'] if c not in cohorts]
    summary=dict(schema='trr07-ci-summary-v1',experiments=rows,execution_errors=errors,
        remaining_formal_obligations=['function-field and residue constructions','Riemann-Roch and evaluation hyperplane',
                                     'genus-one divisor criterion and derivation kernel','geometric chart coverage'],
        interpretation='Finite cohorts provide coverage. A symbolic exclusion requires complete integer and characteristic certificates plus independent replay.')
    args.output.parent.mkdir(parents=True,exist_ok=True);args.markdown.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(summary,indent=2)+'\n')
    lines=['# TRR-07 experiment receipt','','| Experiment | Observed status |','|---|---|']
    for r in rows:lines.append(f"| {r['experiment']} | {r['status']} |")
    lines += ['','Finite-field scans retain their stated sampling limits. Lean checks field algebra under explicit geometric hypotheses.']
    if errors:lines+=['','Execution issues: '+', '.join(errors)]
    args.markdown.write_text('\n'.join(lines)+'\n');print(args.markdown.read_text())
    if errors:raise SystemExit(1)


if __name__=='__main__':main()
