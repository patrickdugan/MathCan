"""Independent RAM-14 audit of original source-only posthoc tactic candidates.

Consumes the *first completed* original CI artifact from run 43791363290,
reconstructs all 35 candidate sources, verifies both recorded compiler
passes, and recompiles each accepted source in a new Lean4.35 process.
"""
from __future__ import annotations
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path
from grammar import TARGETS,SOURCE_SHA,SOURCE_BLOB,generate,git_blob,sha

ORIGINAL_RUN=43791363290
EXPECTED_ROWS=35
EXPECTED_CERTIFIED=4
VALID_CLASSES={"candidate_compiled","compiler_rejected","compiler_timeout_unknown"}


def checked_source(mathcan: Path):
    head=subprocess.run(["git","rev-parse","HEAD"],cwd=mathcan,
                        capture_output=True,text=True,check=True).stdout.strip()
    if head!=SOURCE_SHA:raise ValueError("not the originally evaluated MathCan source")
    if (mathcan/"lean-toolchain").read_text().strip()!="leanprover/lean4:v4.35.0":
        raise ValueError("bad compiler toolchain")
    raw=(mathcan/"MathCan/GramianTransfer.lean").read_bytes()
    if git_blob(raw)!=SOURCE_BLOB:raise ValueError("original source blob changed")
    return raw.decode()


def run(mathcan:Path,evidence:Path,out:Path):
    if out.exists():raise FileExistsError("independent audit output already exists")
    original=checked_source(mathcan)
    sys.path.insert(0,str(mathcan/"research/ram11f"))
    from native_replay import render_source,axiom_inventory
    path=evidence/"cases.jsonl"
    if not path.is_file():raise FileNotFoundError("original complete CI receipt absent")
    lines=[json.loads(s) for s in path.read_text().splitlines() if s.strip()]
    if len(lines)!=EXPECTED_ROWS:raise AssertionError("incomplete first-run case list")
    report=json.loads((evidence/"report.json").read_text())
    if report["status"]!="complete" or report["generated_candidates"]!=EXPECTED_ROWS:
        raise AssertionError("original first-run report incomplete")
    if report["source_commit"]!=SOURCE_SHA or report["source_git_blob"]!=SOURCE_BLOB:
        raise AssertionError("first-run source provenance mismatch")
    if report["per_theorem_double_compiled"] != {
            "transport_iterate":1,"observable_transport":3}:
        raise AssertionError("original proof count changed")
    out.mkdir(parents=True)
    scratch=mathcan/"RAM14AuditScratch"
    if scratch.exists():raise FileExistsError("audit scratch already exists")
    scratch.mkdir()
    final=[]
    for target in TARGETS:
        expected=generate(original,target)
        rows=[r for r in lines if r["theorem"]==target]
        if len(rows)!=len(expected):raise AssertionError("changed candidate grammar")
        for index,(row,item) in enumerate(zip(rows,expected)):
            if row["index"]!=index or row["candidate"]!=item.as_dict():
                raise AssertionError("first-run generated tactic or ordering changed")
            case=f"{target}_{index:03d}"
            src=evidence/"compiler_sources_and_logs"/case/"first.lean"
            old=src.read_bytes()
            reconstructed=render_source(original,target,[item.script]).encode()
            if old!=reconstructed:raise AssertionError("original source payload changed")
            proofhash=sha(old)
            first=row["first"]
            if proofhash!=first["source_sha256"]:raise AssertionError("bad original source digest")
            if first["status"] not in VALID_CLASSES:raise AssertionError("unknown compiler status")
            firstlog=evidence/"compiler_sources_and_logs"/case/"first.log"
            if sha(firstlog.read_bytes())!=first["log_sha256"]:
                raise AssertionError("first compiler log changed")
            second=row.get("second")
            if row["accepted"]:
                if second is None or first["status"]!="candidate_compiled" or second["status"]!="candidate_compiled":
                    raise AssertionError("proof missing second compiler acceptance")
                src2=evidence/"compiler_sources_and_logs"/case/"independent"/"second.lean"
                log2=evidence/"compiler_sources_and_logs"/case/"independent"/"second.log"
                if src2.read_bytes()!=old or sha(log2.read_bytes())!=second["log_sha256"]:
                    raise AssertionError("second source/log disagreement")
                a1,l1,_=axiom_inventory(firstlog.read_text())
                a2,l2,_=axiom_inventory(log2.read_text())
                if not a1 or not a2 or l1!=l2 or l1!=row["allowed_axioms"]:
                    raise AssertionError("untrusted original axiom inventory")
                dest=scratch/(case+".lean");dest.write_bytes(old)
                trial=subprocess.run(["lake","env","lean",str(dest.resolve())],cwd=mathcan,
                                     capture_output=True,text=True,timeout=20)
                trace=trial.stdout+"\n"+trial.stderr
                logs=out/"third_compiler_logs";logs.mkdir(exist_ok=True)
                (logs/(case+".log")).write_text(trace,encoding="utf8")
                gate,axioms,why=axiom_inventory(trace)
                if trial.returncode or "error:" in trace or "sorryAx" in trace or not gate or axioms!=l1:
                    raise AssertionError(f"invalid independent Lean source: {case}: {why}")
                final.append(dict(theorem=target,index=index,script=item.script,
                                  source_sha256=proofhash,third_lean_returncode=trial.returncode,
                                  third_lean_log_sha256=sha(trace.encode()),axioms=axioms,
                                  exactly_same_source=True,trust_gate="triple_compiled"))
            elif second is not None:
                raise AssertionError("candidate reported failed after second compilation")
    if len(final)!=EXPECTED_CERTIFIED:raise AssertionError("final certificate count mismatch")
    evidence_sha=sha(path.read_bytes())
    receipt=dict(experiment="RAM14_posthoc_independent_third_Lean435_replay",
                 original_run=ORIGINAL_RUN,first_cases_sha256=evidence_sha,
                 total_candidate_attempts=len(lines),independently_third_compiled=len(final),
                 full_source_compiles_on_accepted_scripts=3*len(final),
                 distinct_original_theorems=len({x["theorem"] for x in final}),
                 compiler_false_certificates=0,
                 original_RAM13_result_unchanged=True,
                 prospective_capability_claim=False,
                 separate_mathcan_old_source=SOURCE_SHA,
                 certificates=final,status="passed")
    (out/"independent_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print("RAM14_INDEPENDENT_THIRD",json.dumps(receipt,sort_keys=True),flush=True)
    return receipt


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--mathcan",type=Path,required=True)
    p.add_argument("--first-artifact",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args()
    run(a.mathcan.resolve(),a.first_artifact.resolve(),a.out.resolve())
