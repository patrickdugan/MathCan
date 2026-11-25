#!/usr/bin/env python3
"""Compile the uniform obstruction's field-algebra classification in Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean',default='lean')
    parser.add_argument('--module',type=Path,default=ROOT/'MathCan/TranslationInterpolationUniform.lean')
    parser.add_argument('--output',type=Path,default=HERE/'proof_uniform_receipt.json')
    args=parser.parse_args()
    source=args.module.resolve()
    assert not re.search(r'\b(sorry|admit|axiom)\b',source.read_text())
    start=time.monotonic()
    result=subprocess.run([args.lean,str(source)],capture_output=True,text=True,timeout=120,cwd=source.parent)
    assert result.returncode==0,result.stdout+result.stderr
    rows=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",result.stdout,re.S)
    assert len(rows)==6,result.stdout
    axioms={name:[v.strip() for v in values.replace('\n',' ').split(',') if v.strip()]
            for name,values in rows}
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
    receipt=dict(schema='trr07-uniform-lean-v1',status='passed',
                 lean_version=subprocess.check_output([args.lean,'--version'],text=True).strip(),
                 source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                 module='MathCan.TranslationInterpolationUniform',theorem_count=len(rows),
                 transitive_axioms=axioms,elapsed_seconds=round(time.monotonic()-start,6),
                 theorem='Leading four degree-eight obstruction coefficients force 4*A^3+27*B^2=0.',
                 field_hypotheses=['n != 0','2 != 0','3 != 0'],
                 additional_characteristic_exclusions=[],geometry_formalized=False,
                 remaining_obligations=['Derive the slope cocycle from global rational functions.',
                                        'Derive the polynomial obstruction from the decoder condition.',
                                        'Apply the distinct-root bound to force polynomial identity.',
                                        'Supply the matching-characteristic geometric argument and small-order certificates.'])
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(status='passed',theorems=len(rows),receipt=str(args.output))))


if __name__=='__main__':
    main()
