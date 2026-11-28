"""RAM-14 posthoc native Lean4.35 tactic-family coverage diagnostic.

Outputs include every generated source and compiler log. The original target
proof body is only passed to a *proof-body replacement renderer*. Candidate
ranking is computed from the prior declarations and target statement alone.
No model training, proprietary artifacts, or prospective score changes.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import re

from grammar import TARGETS, SOURCE_SHA, SOURCE_BLOB, generate, git_blob, sha
from grammar import FAMILIES, MAX_PER_FAMILY, MAX_TOTAL

PER_COMPILE_SECONDS = 15.0
ALLOWED_VERSION = "4.35.0"


def checkout(args: argparse.Namespace):
    mathcan = args.mathcan.resolve()
    assert mathcan.is_dir()
    result = subprocess.run(["git", "rev-parse", "HEAD"],cwd=mathcan,capture_output=True,text=True)
    if result.returncode != 0 or result.stdout.strip() != SOURCE_SHA:
        raise ValueError("source revision differs from pinned original MathCan")
    tracked = subprocess.run(["git","status","--porcelain","--untracked-files=no"],
                             cwd=mathcan,capture_output=True,text=True)
    if tracked.returncode or tracked.stdout.strip():
        raise ValueError("tracked source modified")
    if (mathcan / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        raise ValueError("original Lean version differs")
    raw=(mathcan / "MathCan/GramianTransfer.lean").read_bytes()
    if git_blob(raw) != SOURCE_BLOB:
        raise ValueError("original source Git blob mismatches")
    lean=subprocess.run(["lake","env","lean","--version"],cwd=mathcan,
                        capture_output=True,text=True,timeout=20)
    if lean.returncode or ALLOWED_VERSION not in (lean.stdout+lean.stderr):
        raise ValueError("pinned Lean4.35 unavailable")
    return mathcan, raw.decode(), lean.stdout.strip()


def compile_once(mathcan: Path, source: bytes, path: Path):
    # Paths stay inside the pinned project root; the source checkout's tracked
    # files are unaffected and every test has a new source name.
    path.parent.mkdir(parents=True,exist_ok=False)
    path.write_bytes(source)
    started=time.perf_counter()
    try:
        run=subprocess.run(["lake","env","lean",str(path.resolve())],cwd=mathcan,
                           capture_output=True,text=True,errors="replace",
                           timeout=PER_COMPILE_SECONDS)
        stdout=run.stdout+"\n"+run.stderr
        status="compiler_rejected"
        if run.returncode==0 and "error:" not in stdout and "sorryAx" not in stdout:
            status="candidate_compiled"
        log=path.with_suffix(".log")
        log.write_text(stdout,encoding="utf8")
        return dict(status=status,returncode=run.returncode,
                    source_sha256=sha(source),log_sha256=sha(stdout.encode()),
                    wall_seconds=round(time.perf_counter()-started,4),
                    source_file=str(path),log_file=str(log))
    except subprocess.TimeoutExpired as exc:
        log=path.with_suffix(".log")
        log.write_text("unknown compiler timeout\n"+str(exc)+"\n",encoding="utf8")
        return dict(status="compiler_timeout_unknown",returncode=None,
                    source_sha256=sha(source),log_sha256=sha(log.read_bytes()),
                    wall_seconds=round(time.perf_counter()-started,4),
                    source_file=str(path),log_file=str(log))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mathcan",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--scratch-name",default="RAM14Scratch")
    args=p.parse_args()
    # The scorer imports the existing, separately native-certified source
    # renderer and axiom inventory checker from public MathCan RAM-11F.
    mathcan,original,version=checkout(args)
    sys.path.insert(0,str(mathcan/"research/ram11f"))
    from native_replay import render_source,axiom_inventory
    if not re.fullmatch(r"RAM14Scratch[A-Za-z0-9_]*",args.scratch_name):
        raise ValueError("invalid scratch name")
    scratch=mathcan/args.scratch_name
    if args.out.exists() or scratch.exists():
        raise FileExistsError("preserve original scorer artifacts, use new output paths")
    args.out.mkdir(parents=True)
    scratch.mkdir()
    rows=[]
    for target in TARGETS:
        generated=generate(original,target)
        if len(generated)>MAX_TOTAL or Counter(x.family for x in generated).get("nat_induction",0)>MAX_PER_FAMILY:
            raise AssertionError("registered source-grammar budget changed")
        print("RAM14_GENERATED",target,len(generated),flush=True)
        target_rows=[]
        for index,item in enumerate(generated):
            case_id=f"{target}_{index:03d}"
            generated_source=render_source(original,target,[item.script]).encode()
            first=compile_once(mathcan,generated_source,scratch/case_id/"first.lean")
            second=None;axioms=[];accepted=False;gate_detail=""
            if first["status"]=="candidate_compiled":
                firstlog=Path(first["log_file"]).read_text(encoding="utf8")
                gate,axioms,gate_detail=axiom_inventory(firstlog)
                if gate:
                    second=compile_once(mathcan,generated_source,
                                        scratch/case_id/"independent"/"second.lean")
                    if second["status"]=="candidate_compiled":
                        again=Path(second["log_file"]).read_text(encoding="utf8")
                        gate2,axioms2,why2=axiom_inventory(again)
                        accepted=bool(gate2 and axioms2==axioms
                                      and first["source_sha256"]==second["source_sha256"])
                        gate_detail=why2 or gate_detail
            receipt=dict(theorem=target,index=index,candidate=item.as_dict(),
                         first=first,second=second,accepted=accepted,
                         allowed_axioms=axioms,axiom_gate_detail=gate_detail,
                         historical_ram13_score="0/2 every original policy",
                         study_class="posthoc after target reference proof was inspected")
            rows.append(receipt);target_rows.append(receipt)
            print("RAM14_CASE",target,index,item.family,item.script,
                  int(accepted),first["status"],flush=True)
            (args.out/"cases.jsonl").open("a",encoding="utf8").write(
                json.dumps(receipt,ensure_ascii=False,sort_keys=True)+"\n")
    original_oracle=subprocess.run(
        ["lake","env","lean","MathCan/GramianTransfer.lean"],cwd=mathcan,
        capture_output=True,text=True,timeout=60)
    if original_oracle.returncode or "error:" in (original_oracle.stdout+original_oracle.stderr):
        raise AssertionError("original frozen GramianTransfer source does not compile")
    totals={t:sum(x["accepted"] for x in rows if x["theorem"]==t) for t in TARGETS}
    result=dict(study="RAM14_posthoc_gramian_structural_grammar",
                source_commit=SOURCE_SHA,source_git_blob=SOURCE_BLOB,
                lean=version,status="complete",
                generated_candidates=len(rows),per_theorem_generated=dict(Counter(x["theorem"] for x in rows)),
                per_theorem_double_compiled=totals,
                per_family_generated=dict(Counter(x["candidate"]["family"] for x in rows)),
                per_family_double_compiled=dict(Counter(x["candidate"]["family"] for x in rows if x["accepted"])),
                failed_compilers=sum(x["first"]["status"]=="compiler_rejected" for x in rows),
                compiler_unknown=sum(x["first"]["status"]=="compiler_timeout_unknown" for x in rows),
                original_frozen_gramian_benchmark="0/2 original RAM-13; unchanged",
                prospective_theorem_score_credit=0,
                first_attempt_posthoc=True,
                candidate_source="target statement and prior declaration headers, never reference target proof",
                full_source_double_compile_gate=True,
                original_source_oracle_status="passed")
    (args.out/"report.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    # Preserve the complete source/log artifacts with a copy outside the
    # checked-out git tree, so the Actions artifact survives job cleanup.
    import shutil
    shutil.copytree(scratch,args.out/"compiler_sources_and_logs")
    print("RAM14_REPORT",json.dumps(result,sort_keys=True),flush=True)


if __name__=="__main__":
    main()
