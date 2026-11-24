"""Inventory and lexical import-closure verification for the pinned VPVNP source."""
import argparse
import csv
import hashlib
import json
import re
import subprocess
from pathlib import Path

PIN = "11b6c7e3c927df2658f513b6b68ea7f8929c62c5"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    pin = subprocess.check_output(["git","-C",str(checkout),"rev-parse","HEAD"],text=True).strip()
    assert pin == PIN, (pin,PIN)
    with Path(__file__).with_name("source_inventory.tsv").open() as f:
        rows=list(csv.DictReader(f,delimiter="\t"))
    expected={r["path"]:r for r in rows}
    actual={p.relative_to(checkout).as_posix() for p in (checkout/"vp-vnp").rglob("*.lean") if ".lake" not in p.parts}
    assert len(rows)==len(expected)==324 and actual==set(expected)
    edges={}
    prefix="vp-vnp/"
    for p,row in expected.items():
        raw=(checkout/p).read_bytes()
        assert len(raw)==int(row["bytes"]),p
        oid=hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\x00"+raw).hexdigest()
        assert oid==row["git_blob_sha1"],p
        mod=p[len(prefix):-5].replace("/",".")
        # Lexical import inventory; strip nested Lean block comments and line comments.
        s=raw.decode("utf-8")
        pattern=re.compile(r"/-|-\/|--[^\n]*|\n|[^/\-\n]+|.", re.S)
        depth=0
        clean=[]
        for token in pattern.findall(s):
            if token=="/-":
                depth+=1
            elif token=="-/" and depth:
                depth-=1
            elif token=="\n":
                clean.append("\n")
            elif not depth and not token.startswith("--"):
                clean.append(token)
        imports=[]
        for line in "".join(clean).splitlines():
            m=re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$",line)
            if m:
                imports.extend(m.group(1).split())
        edges[mod]=sorted(set(imports))
    local={m:[d for d in deps if d in edges] for m,deps in edges.items()}
    visiting=set()
    done=set()
    def visit(m):
        assert m not in visiting, ("local import cycle",m)
        if m in done:
            return
        visiting.add(m)
        for d in local[m]:
            visit(d)
        visiting.remove(m)
        done.add(m)
    visit("Solution")
    closure=sorted(done)
    assert "Statement" in closure and "Challenge" not in closure
    assert edges["Statement"]==["Mathlib"],edges["Statement"]
    for m in local:
        visit(m)
    report={"pin":pin,"files":len(rows),"bytes":sum(int(r["bytes"]) for r in rows),
            "local_edge_count":sum(map(len,local.values())),
            "solution_closure":closure,"solution_closure_count":len(closure),
            "imports":edges,"method":"lexical file-level imports; not elaborated declaration dependencies",
            "status":"PASS"}
    args.out.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print("Verified",len(rows),"blobs; Solution reaches",len(closure),"local modules including itself")

if __name__=="__main__":
    main()
