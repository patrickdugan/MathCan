"""Review native Lean declarations against explicit axiom policies and type contracts.
Use a trusted repository and manifest. Graphs refer to instrumented source,
and are reconciled with the original compiled declaration's axiom closure.
"""
import argparse
import hashlib
import json
import re
import subprocess
from collections import deque
from pathlib import Path

NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
DENY = {"sorryAx", "Lean.ofReduceBool", "Lean.ofReduceNat", "ofReduceBool", "ofReduceNat"}

def sha(x):
    return hashlib.sha256(x.encode() if isinstance(x,str) else x).hexdigest()

def run(cmd,repo,log):
    p=subprocess.run(cmd,cwd=repo,text=True,capture_output=True,timeout=600)
    s=p.stdout+p.stderr
    log.write_text(s)
    if p.returncode or re.search(r"(^|\n).*error:",s):
        raise RuntimeError(f"Native command failed: {cmd}; {log}\n{s[-4000:]}")
    return s

def reports(s):
    out={}
    for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",s):
        if m[1] in out:raise ValueError("duplicate axiom report "+m[1])
        out[m[1]]=sorted(set(x.strip() for x in (m[3] or "").split(",") if x.strip()))
    return out

def names(s):return sorted(set(x.strip() for x in s.split(",") if x.strip()))

def parse_graph(s):
    gs,axs={},{}
    for line in s.splitlines():
        if "CG11_ROOT|" in line:
            r,a=line.split("CG11_ROOT|",1)[1].split("|",1)
            if r in axs:raise ValueError("duplicate root "+r)
            axs[r]=names(a)
        if "CG11_NODE|" in line:
            r,n,k,t,v,a=line.split("CG11_NODE|",1)[1].split("|",5)
            g=gs.setdefault(r,{})
            if n in g:raise ValueError("duplicate node "+n)
            g[n]={"kind":k,"type":names(t),"value":names(v),"axioms":names(a)}
    if set(gs)!=set(axs):raise ValueError("root/graph mismatch")
    return gs,axs

def closure_paths(g,root):
    q=deque([(root,[root])]);seen=set();paths={}
    while q:
        n,path=q.popleft()
        if n in seen:continue
        if n not in g:raise ValueError("unresolved dependency "+n)
        seen.add(n);x=g[n]
        axs=[n] if x["kind"]=="axiom" else x["axioms"] if x["kind"]=="boundary" else []
        for a in axs:paths.setdefault(a,{"path":path,"boundary_summary":x["kind"]=="boundary"})
        for k in sorted(set(x["type"]+x["value"])):q.append((k,path+[k]))
    if seen!=set(g):raise ValueError("unreachable graph rows")
    return paths

def validate(d):
    if d.get("schema")!=1 or not isinstance(d.get("modules"),list) or not d["modules"]:
        raise ValueError("invalid manifest")
    seen=set();mods=set()
    for m in d["modules"]:
        module=m["module"]
        if not NAME.fullmatch(module) or module in mods or not m["roots"]:raise ValueError("invalid module")
        mods.add(module)
        if type(m.get("graph",False)) is not bool:raise ValueError("invalid graph flag")
        for r in m["roots"]:
            n=r["name"]
            if not NAME.fullmatch(n) or not n.startswith(module+".") or n in seen:raise ValueError("invalid theorem "+n)
            seen.add(n)
            for k in ("allowed_axioms","expected_axioms"):
                if k=="expected_axioms" and k not in r:continue
                xs=r[k]
                if type(xs) is not list or any(type(x) is not str or not NAME.fullmatch(x) for x in xs) or DENY.intersection(xs):
                    raise ValueError("invalid foundation policy "+n)
            if "contract" in r and (type(r["contract"]) is not str or not r["contract"].strip()):
                raise ValueError("invalid statement contract")
    return seen

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--repo",type=Path,default=Path("."))
    p.add_argument("--manifest",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    a=p.parse_args();repo=a.repo.resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
    raw_manifest=a.manifest.read_bytes();data=json.loads(raw_manifest);expected_roots=validate(data)
    rev=run(["git","rev-parse","HEAD"],repo,out/"revision.log").strip()
    if run(["git","status","--porcelain","--untracked-files=no"],repo,out/"status.log").strip():
        raise RuntimeError("commit tracked source before review")
    version=run(["lake","env","lean","--version"],repo,out/"version.log").strip()
    if data["lean_version"] not in version:raise RuntimeError("unexpected Lean toolchain")
    run(["lake","build",*[m["module"] for m in data["modules"]]],repo,out/"build.log")
    extractor=Path(__file__).with_name("Extract.lean").read_text()
    if not extractor.startswith("import Lean\n"):raise RuntimeError("invalid extractor")
    rows=[];graphs={};failures=[]
    for m in data["modules"]:
        mod=m["module"];source=repo/Path(*mod.split(".")).with_suffix(".lean")
        raw=source.read_bytes();roots=[r["name"] for r in m["roots"]]
        audit=out/(mod+"-audit.lean")
        ls=["import "+mod,"set_option pp.fullNames true","universe u v w","namespace ReviewContracts"]
        contracts={}
        for i,r in enumerate(m["roots"]):
            if "contract" in r:
                alias=f"ReviewContracts.contract{i}"
                ls.append(f"theorem contract{i} : {r['contract']} := @{r['name']}")
                contracts[r["name"]]=alias
        ls.append("end ReviewContracts")
        expected=set(roots)|set(contracts.values())
        ls.extend("#print axioms "+n for n in sorted(expected))
        audit.write_text("\n".join(ls)+"\n")
        actual=reports(run(["lake","env","lean",str(audit)],repo,audit.with_suffix(".log")))
        if set(actual)!=expected:raise ValueError("missing or extra native roots")
        paths={};instrumented_hash=None
        if m.get("graph",False):
            text=raw.decode()
            if re.search(r"(?m)^\s*(module|prelude)\b",text):raise ValueError("unsupported module header")
            inst="import Lean\n"+text+"\n"+extractor.removeprefix("import Lean\n")+"\nset_option pp.fullNames true\n"
            for n in roots:inst+=f"#cg11_deps {n} within {mod}\n#print axioms {n}\n"
            gp=out/(mod+"-instrumented.lean");gp.write_text(inst)
            log=run(["lake","env","lean",str(gp)],repo,gp.with_suffix(".log"))
            log=log[log.index("CG11_ROOT|"):]
            gs,axs=parse_graph(log);printed=reports(log)
            if set(gs)!=set(roots) or set(printed)!=set(roots):raise ValueError("instrumented roots mismatch")
            for n in roots:
                paths[n]=closure_paths(gs[n],n)
                if not (sorted(paths[n])==axs[n]==printed[n]==actual[n]):
                    raise ValueError("native/graph closure mismatch "+n)
                graphs[n]=gs[n]
            instrumented_hash=sha(inst)
        for r in m["roots"]:
            n=r["name"];allowed=set(r["allowed_axioms"]);observed=set(actual[n]);errors=[]
            extra=observed-allowed
            if extra:errors.append("unapproved axioms: "+", ".join(sorted(extra)))
            if DENY&observed:errors.append("admitted or native-reduction dependency")
            if "expected_axioms" in r and observed!=set(r["expected_axioms"]):errors.append("axiom set drift")
            alias=contracts.get(n)
            if alias and (set(actual[alias])-allowed or DENY&set(actual[alias])):
                errors.append("contract uses unapproved axioms")
            row={"name":n,"module":mod,"source_sha256":sha(raw),"axioms":sorted(observed),
                 "allowed_axioms":sorted(allowed),"expected_axioms":r.get("expected_axioms"),
                 "contract_checked":alias is not None,
                 "contract_sha256":sha(r["contract"]) if alias else None,
                 "instrumented_sha256":instrumented_hash,
                 "graph_sha256":sha(json.dumps(graphs[n],sort_keys=True)) if n in graphs else None,
                 "axiom_paths":paths.get(n),"status":"FAIL" if errors else "PASS","errors":errors}
            rows.append(row);failures.extend({"name":n,"error":x} for x in errors)
            print("REVIEW",json.dumps(row),flush=True)
    if {r["name"] for r in rows}!=expected_roots:raise ValueError("incomplete review")
    receipt={"schema":1,"revision":rev,"lean":version,"manifest_sha256":sha(raw_manifest),
             "roots":rows,"failures":failures,"passed":not failures}
    (out/"review.json").write_text(json.dumps(receipt,indent=2))
    (out/"graphs.json").write_text(json.dumps(graphs,indent=2))
    ls=["# Native proof review",f"Revision: {rev}","",
        "| Declaration | Axioms | Contract | Status |","|---|---|---|---|"]
    for r in rows:
        ls.append(f"| {r['name']} | {', '.join(r['axioms']) or 'none'} | {'checked' if r['contract_checked'] else 'not specified'} | {r['status']} |")
    ls+=["","A policy violation describes the submitted proof relative to its declared foundation.",
         "Paths describe instrumented copies. Imported boundaries carry axiom summaries."]
    (out/"review.md").write_text("\n".join(ls)+"\n")
    print("REVIEW_GATE",json.dumps({"roots":len(rows),"contracts":len([r for r in rows if r["contract_checked"]]),
          "graph_roots":len(graphs),"failures":len(failures),"passed":not failures}),flush=True)
    return int(bool(failures))

if __name__=="__main__":raise SystemExit(main())
