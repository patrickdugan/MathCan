#!/usr/bin/env python3
"""Reject corruption of the local-residue bridge, including its denominators."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=HERE/'symbolic_results/certificate19.json')
    parser.add_argument('--output',type=Path,default=HERE/'audit_flint_bridge.json')
    parser.add_argument('--timeout',type=int,default=180)
    args=parser.parse_args()
    original=json.loads(args.certificate.read_text())
    assert set(original)=={'19'}
    sources=[args.certificate,HERE/'flint_replay.py',HERE/'symbolic_generic.py',HERE/'symbolic_norm_replay.py']
    before={p.name:digest(p) for p in sources}
    records=[]
    with tempfile.TemporaryDirectory(prefix='trr07-flint-bridge-') as temp:
        temp=Path(temp)
        for name in ['positive_control','residue_numerator','residue_denominator']:
            data=copy.deepcopy(original)
            if name=='residue_numerator':
                entry=data['19']['g']['2']['num'][0]
                entry[0]=str(int(entry[0])+1)
            elif name=='residue_denominator':
                data['19']['g']['2']['den_exp_t']+=1
            certificate=temp/f'{name}.json'
            certificate.write_text(json.dumps(data))
            receipt=temp/f'{name}_receipt.json'
            started=time.monotonic()
            run=subprocess.run([sys.executable,str(HERE/'flint_replay.py'),str(certificate),
                                '--expected-order','19','--output',str(receipt)],
                               capture_output=True,text=True,timeout=args.timeout)
            detail=json.loads(receipt.read_text())
            if name=='positive_control':
                accepted=run.returncode==0 and detail['status']=='passed'
                assert detail['ratio_identities']==8
                assert detail['elimination_and_fibres']['status']=='passed'
            else:
                accepted=run.returncode!=0 and detail['status']=='failed'
                accepted=accepted and 'g_2 differs from direct Laurent coefficient' in run.stderr
            records.append(dict(case=name,expected_result_observed=accepted,
                                returncode=run.returncode,status=detail['status'],
                                elapsed_seconds=round(time.monotonic()-started,6)))
            assert accepted,dict(case=name,stdout=run.stdout,stderr=run.stderr,receipt=detail)
    assert before=={p.name:digest(p) for p in sources},'input changed during guard checks'
    out=dict(schema='trr07-flint-bridge-guards-v1',status='passed',
             source_sha256=before,harness_sha256=digest(Path(__file__)),
             cases=records,negative_controls_rejected=2,
             scope='The numerator and localization denominator must match independent local Laurent reconstruction; elimination-only replay cannot verify the denominator.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(status='passed',negative_controls_rejected=2,receipt=str(args.output))))


if __name__=='__main__':
    main()
