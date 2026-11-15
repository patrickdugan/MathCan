import os
from collections import Counter
from pathlib import Path
import hashlib
import json
import re

W=Path(os.environ.get("CAMPAIGN_WORK", Path(__file__).resolve().parent)).resolve()
R=W/"replay432/Lemmas"
v=json.loads((R/"verdicts.json").read_text())
a=json.loads((R/"axiom-graph.json").read_text())
c=json.loads((R/"source_export_comparison.json").read_text())
assert v["input"]["sha256"]==a["sha256"]==hashlib.sha256((R/"Lemmas.ndjson").read_bytes()).hexdigest()
assert v["pins"]["file_lean_version"]=="4.32.0-rc1"
assert v["pins"]["file_lean_githash"]=="b4812ae53eea93439ad5dce5a5c26591c31cb697"
assert a["structurally_closed"] and a["unambiguous_names"] and not a["unsafe_records"]
assert len(v["decls"])==a["record_count"]==a["closure_record_count"]
assert all(x["verdict"]=="verified" for x in v["decls"])
assert v["totals"]["verified"]==len(v["decls"]) and v["totals"]["unsupported"]==v["totals"]["rejected"]==0
assert c["status"]=="matched" and c["constants_compared"]==sum(len(x["names"]) for x in a["records"])
assert all(x["type_equal"] and x["value_equal_after_metadata_normalization"] and x["level_parameters_equal"] for x in c["records"])
native={}
for filename in ("quantized_jet_native.log","spatial_native.log"):
    log=(R/filename).read_text()
    assert "error:" not in log and "sorryAx" not in log
    for name,axes in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",log,re.M):
        native[name]=sorted(x.strip() for x in axes.split(",") if x.strip())
    for name in re.findall(r"^'([^']+)' does not depend on any axioms",log,re.M): native[name]=[]
assert len(native)==14,len(native)
nodes={r["id"]:r for r in a["records"]}
owners={name:r["id"] for r in a["records"] for name in r["display_names"]}
byname={r["name"]:r for r in v["decls"]}
roots=[]
for name,axes in sorted(native.items()):
    assert byname[name]["verdict"]=="verified"
    todo=[owners[name]]; seen=set()
    while todo:
        i=todo.pop()
        if i in seen: continue
        seen.add(i); todo+=nodes[i]["dependencies"]
    exported=sorted(n for i in seen if nodes[i]["kind"]=="axiom" for n in nodes[i]["display_names"])
    assert exported==axes,(name,exported,axes)
    assert set(axes)<={"propext","Quot.sound","Classical.choice"}
    roots.append({"name":name,"verdict":"verified","native_lean":"accepted","leanchecker":"accepted",
                  "axioms":axes,"dependency_record_ids":sorted(seen),"dependency_records":len(seen),
                  "statement_and_proof_match":True})
result={"status":"accepted","export_sha256":v["input"]["sha256"],"verdicts":{"verified":len(v["decls"]),"unsupported":0,"rejected":0},
        "constants_compared":c["constants_compared"],"theorems":roots,
        "source_sha256":{n:hashlib.sha256((W/"MathCan/MathCan"/n).read_bytes()).hexdigest() for n in ("QuantizedJet.lean","SpatialInterface.lean")}}
(R/"ACCEPTANCE.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
print(json.dumps({k:len(v) if k=="theorems" else v for k,v in result.items() if k!="source_sha256"},indent=2))
