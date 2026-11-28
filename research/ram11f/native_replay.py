"""Native Lean 4.35 double-compile audit of 76 historical RAM-11F worklist scripts.

This branch is a *public-runner transplant* of a pinned read-only diagnostic.
It only uses the original MathCan training source, never the PEF/RAM-10 heldouts.
Source validation, two independent compilations, and the transitive axiom
inventory are mandatory for any historical theorem certificate. No proof
credit is assigned on parse errors or compiler timeouts.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

OLD_SOURCE = 'c84e2025334e9a967c1297425a490f98d5b3d189'
WORKLIST_HASH = 'f5876539862a0f4f913dc3af620be0d038555efcdd3611754e002dc353c3b2aa'
EXPECTED_CASES = 76
ALLOWED_AXIOMS = frozenset(('propext', 'Classical.choice', 'Quot.sound'))
MAX_SECONDS_PER_CASE = 30.0
MAX_SECONDS_PER_COMPILE = 10.0
ROOT = Path(__file__).resolve().parent
END_SOURCE = re.compile(
    r'^(?:theorem|lemma|def|abbrev|opaque|instance|inductive|structure|class|namespace|section|end|'
    r'#(?:print|eval|check)|/-[-!]|@\[)\b|^/-[-!]|^@\[')
BEGIN_MARK = 'RAM11F_AXIOMS_BEGIN_20261115'
END_MARK = 'RAM11F_AXIOMS_END_20261115'


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def run(*argv: str, cwd: Path | None = None, timeout: float = 15) -> subprocess.CompletedProcess:
    return subprocess.run(list(argv), cwd=cwd, capture_output=True, text=True,
                          errors='replace', timeout=timeout, check=False)


def validate_worklist(path: Path) -> list[dict]:
    raw = path.read_bytes()
    if sha(raw) != WORKLIST_HASH:
        raise ValueError('historical RAM-11F worklist SHA mismatch')
    rows = [json.loads(s) for s in raw.decode('utf8').splitlines() if s.strip()]
    if len(rows) != EXPECTED_CASES:
        raise ValueError('incomplete worklist')
    seen = set()
    for row in rows:
        if row.get('historical_proof_score') != 0:
            raise ValueError('input must be the original unscored worklist')
        if not row['source_file'].startswith('MathCan/') or not row['source_file'].endswith('.lean'):
            raise ValueError('source outside original MathCan corpus')
        if not re.fullmatch(r"[A-Za-z_][\w']*", row['theorem'], flags=re.ASCII):
            raise ValueError('invalid target theorem')
        if not (1 <= len(row['proposed_new_actions']) <= 8):
            raise ValueError('outside original script depth bound')
        for act in row['proposed_new_actions']:
            if '\n' in act or '\r' in act or ';' in act or re.search(
                r'\b(?:sorry|sorryAx|admit|axiom|unsafe|run_tac|set_option)\b', act):
                raise ValueError('disallowed executable candidate')
        target = (row['source_file'], row['theorem'], tuple(row['proposed_new_actions']))
        if target in seen:
            raise ValueError('duplicate input script')
        seen.add(target)
    return rows


def verify_checkout(mathcan: Path):
    actual = run('git', 'rev-parse', 'HEAD', cwd=mathcan)
    if actual.returncode != 0 or actual.stdout.strip() != OLD_SOURCE:
        raise ValueError('MathCan old-source HEAD mismatch')
    version = (mathcan/'lean-toolchain').read_text().strip()
    if version != 'leanprover/lean4:v4.35.0':
        raise ValueError('MathCan original toolchain mismatch')
    changed = run('git', 'status', '--porcelain', '--untracked-files=no', cwd=mathcan)
    if changed.returncode or changed.stdout.strip():
        raise ValueError('pinned MathCan tracked source has been modified')
    lean = run('lake', 'env', 'lean', '--version', cwd=mathcan, timeout=25)
    if lean.returncode or '4.35.0' not in lean.stdout + lean.stderr:
        raise ValueError('Lean4.35.0 compiler unavailable')
    return lean.stdout.strip() or lean.stderr.strip()


def render_source(original: str, theorem: str, actions: list[str]) -> str:
    """Replace the entire original proof, keeping exact theorem header.

    Preserve original imports, declarations and source namespaces. The source
    *after* the replaced target is kept intact, so the remaining MathCan file
    still compiles. Marked #print axioms occurs immediately after the target.
    Avoid accidentally pulling the original target proof into the generated file.
    """
    lines = original.splitlines(keepends=True)
    pattern = re.compile(r'^(?:theorem|lemma)\s+'+re.escape(theorem)+r'(?=\s|\(|\{|\[|:)', re.ASCII)
    starts = [i for i,line in enumerate(lines) if pattern.match(line)]
    if len(starts) != 1:
        raise ValueError(f'original declaration not unique: {theorem}: {starts}')
    start = starts[0]
    boundary = next((i for i in range(start+1,len(lines))
                     if END_SOURCE.match(lines[i])), len(lines))
    # Replace both tactic-mode `:= by` and term-mode `:= expr` proofs.
    # Later nested `have := by` clauses are part of the old proof.
    markers = [(i, line.index(':=')) for i,line in enumerate(lines[start:boundary],start)
               if ':=' in line]
    if not markers:
        raise ValueError(f'original theorem proof marker absent: {theorem}')
    marker, at = markers[0]
    # Never append original theorem proof comments, let-bindings, or tactics.
    raw_header = ''.join(lines[start:marker]) + lines[marker][:at] + ':= by\n'
    if not raw_header.startswith(('theorem ', 'lemma ')):
        raise AssertionError('renderer changed target statement prefix')
    tactic_body = ''.join('  '+s+'\n' for s in actions)
    axiom_output = (f'#eval IO.println "{BEGIN_MARK}"\n'
                    f'#print axioms {theorem}\n'
                    f'#eval IO.println "{END_MARK}"\n')
    suffix=''.join(lines[boundary:])
    result = ''.join(lines[:start])+raw_header+tactic_body+'\n'+axiom_output+'\n'+suffix
    if any(item.strip() in result[result.index(raw_header)+len(raw_header):result.index(axiom_output)]
           for item in ('sorry','admit')):
        raise AssertionError('renderer unexpectedly includes admit/sorry')
    return result


def axiom_inventory(stdout: str) -> tuple[bool, list[str], str]:
    if stdout.count(BEGIN_MARK) != 1 or stdout.count(END_MARK) != 1:
        return False, [], 'missing or duplicated axiom delimiters'
    relevant = stdout.split(BEGIN_MARK,1)[1].split(END_MARK,1)[0]
    if "does not depend on any axioms" in relevant:
        return True, [], ''
    match = re.search(r'depends on axioms:\s*\[([^\]]*)\]', relevant)
    if match is None:
        return False, [], 'Lean axiom inventory parse failure'
    axioms=[s.strip() for s in match.group(1).split(',') if s.strip()]
    if not set(axioms).issubset(ALLOWED_AXIOMS):
        return False, axioms, 'unexpected transitive theorem axioms'
    return True, axioms, ''


def compile_once(mathcan: Path, source: bytes, prefix: Path, seconds: float) -> dict:
    prefix.parent.mkdir(parents=True, exist_ok=True)
    source_path=prefix.with_suffix('.lean')
    if source_path.exists():
        raise FileExistsError('compilation source output already exists')
    source_path.write_bytes(source)
    log_file=prefix.with_suffix('.log')
    try:
        res=run('lake','env','lean',str(source_path.resolve()),cwd=mathcan,timeout=max(.1,seconds))
        output=res.stdout+'\n'+res.stderr
        log_file.write_text(output,encoding='utf8')
        okay,axioms,reason=axiom_inventory(output)
        passed=bool(res.returncode==0 and okay and 'error:' not in output and 'sorryAx' not in output)
        return dict(status='accepted' if passed else 'rejected', exitcode=res.returncode,
                    axiom_gate=okay, axioms=axioms, diagnostic=reason,
                    log_sha256=sha(log_file.read_bytes()),source_sha256=sha(source),
                    source_file=str(source_path),log_file=str(log_file))
    except subprocess.TimeoutExpired as e:
        log_file.write_text(f'Lean process exceeded {seconds:.3f}s timeout: {e!s}\n')
        return dict(status='compiler_timeout_unknown',source_sha256=sha(source),
                    source_file=str(source_path),log_file=str(log_file))


def audit(archive: Path, mathcan: Path, out: Path) -> dict:
    if out.exists():
        raise FileExistsError('preserve any previous audit output; choose a new path')
    jobs=validate_worklist(archive)
    compiler_version=verify_checkout(mathcan)
    out.mkdir(parents=True)
    receipt=dict(campaign='RAM11F-public-native-replay',phase='historical_old_train_only',
                 status='running',old_source_commit=OLD_SOURCE,compiler=compiler_version,
                 worklist_sha256=sha(archive.read_bytes()),expected=len(jobs),processed=0,
                 certified_original_train_sources=0,original_PEF_test_scores=0,
                 RAM10_new_source_scores=0,cases=[])
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    for i,item in enumerate(jobs):
        begin=time.perf_counter()
        one=dict(index=i,source_file=item['source_file'],theorem=item['theorem'],
                 actions=item['proposed_new_actions'],recorded_original_source_sha256=item['original_source_sha256'],
                 historical_proof_score=0,classification='not_started')
        try:
            path=mathcan/item['source_file']
            original_raw=path.read_bytes()
            if sha(original_raw)!=item['original_source_sha256']:
                raise ValueError('original theorem source byte hash differs from frozen RAM11F worklist')
            rendered=render_source(original_raw.decode('utf8'),item['theorem'],item['proposed_new_actions'])
            data=rendered.encode('utf8')
            prefix=out/'cases'/f'{i:03d}'
            first=compile_once(mathcan,data,prefix/'first',
                min(MAX_SECONDS_PER_COMPILE,max(.1,MAX_SECONDS_PER_CASE-(time.perf_counter()-begin))))
            one['first']=first
            if first['status']=='compiler_timeout_unknown':
                one['classification']='compiler_timeout_unknown'
            elif first['status']!='accepted':
                one['classification']='first_full_source_rejected'
            elif time.perf_counter()-begin >= MAX_SECONDS_PER_CASE:
                one['classification']='in_budget_replay_unavailable'
            else:
                second=compile_once(mathcan,data,prefix/'second',
                    min(MAX_SECONDS_PER_COMPILE,max(.1,MAX_SECONDS_PER_CASE-(time.perf_counter()-begin))))
                one['second']=second
                if second['status']=='compiler_timeout_unknown':
                    one['classification']='compiler_timeout_unknown'
                elif second['status']!='accepted':
                    one['classification']='independent_source_rejected'
                elif (second['source_sha256']!=first['source_sha256'] or
                      second['axioms']!=first['axioms']):
                    one['classification']='independent_source_disagreement'
                elif time.perf_counter()-begin>MAX_SECONDS_PER_CASE:
                    one['classification']='deadline_overrun'
                else:
                    one['classification']='double_kernel_compiled_train_theorem'
                    one['certificate_sha256']=first['source_sha256']
                    one['axioms']=first['axioms']
                    receipt['certified_original_train_sources']+=1
        except Exception as error:
            one['classification']='infrastructure_or_source_error_unknown'
            one['error']=repr(error)
            receipt['status']='aborted'
        one['seconds']=round(time.perf_counter()-begin,4)
        receipt['processed']+=1
        receipt['cases'].append(one)
        (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
        print('RAM11F_NATIVE',i,one['source_file'],one['theorem'],one['classification'],flush=True)
        if receipt['status']=='aborted':break
    if receipt['status']!='aborted':
        receipt['status']='complete' if receipt['processed']==len(jobs) else 'incomplete'
    receipt['classifications']=dict(Counter(case['classification'] for case in receipt['cases']))
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worklist',type=Path,default=ROOT/'locked_worklist.jsonl')
    p.add_argument('--mathcan',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    receipt=audit(args.worklist,args.mathcan,args.out)
    print('RAM11F_NATIVE_FINAL',json.dumps({k:v for k,v in receipt.items() if k!='cases'},sort_keys=True))
    if receipt['status']!='complete':raise SystemExit(1)