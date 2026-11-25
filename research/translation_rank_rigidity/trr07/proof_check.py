#!/usr/bin/env python3
"""Run the TRR-07 Lean algebra module and record its explicit proof scope."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', default='lean')
    ap.add_argument('--module', type=Path, default=ROOT/'MathCan/TranslationInterpolationAlgebra.lean')
    ap.add_argument('--output', type=Path, default=HERE/'proof_receipt.json')
    args = ap.parse_args()
    source = args.module.resolve()
    text = source.read_text()
    # The source has no admitted goals, new axioms, or opaque theorem declarations.
    assert not re.search(r'\b(sorry|admit|axiom)\b', text)
    version = subprocess.check_output([args.lean,'--version'],text=True).strip()
    started = time.monotonic()
    result = subprocess.run([args.lean,str(source)],capture_output=True,text=True,timeout=120,cwd=source.parent)
    assert result.returncode == 0, result.stdout+result.stderr
    statements = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",result.stdout,re.S)
    assert len(statements) == 9, result.stdout
    axioms = {name:[word.strip() for word in words.replace('\n',' ').split(',') if word.strip()]
              for name,words in statements}
    assert all(set(words)<= {'propext','Classical.choice','Quot.sound'} for words in axioms.values()),axioms
    receipt = {
        'schema':'trr07-lean-algebra-v1','status':'passed','lean_version':version,
        'elapsed_seconds':round(time.monotonic()-started,6),
        'module':'MathCan.TranslationInterpolationAlgebra','theorem_count':len(statements),
        'transitive_axioms':axioms,
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'General field-algebra consequences of explicit residue and cocycle hypotheses.',
        'geometry_formalized':False,
        'remaining_obligations':[
            'Construct function fields, invariant differentials, and local expansions.',
            'Prove global residue and genus-one principal-divisor facts in the chosen formal library.',
            'Identify the kernel of a nonzero derivation with pth powers over perfect constants.',
            'Prove the Riemann-Roch evaluation hyperplane and its polynomial decoder interpretation.',
            'Prove complete geometric Tate chart coverage.',
        ],
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'passed','theorems':len(statements),'receipt':str(args.output)}))


if __name__ == '__main__':
    main()
