"""Structural dependency/axiom audit for pinned lean4export NDJSON 3.1.0.

This is not a type checker. Names are component tuples, never dotted-string
keys. Inductive families are atomic record nodes; constructors and recursors
map to their owner. Duplicate owners remain visible and block acceptance.
"""
import argparse
import hashlib
import json
from pathlib import Path

def digest(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def audit(path, target=None):
    names={0: ()}
    levels={0: digest(["zero"])}
    expressions={}
    nodes=[]
    owners={}
    meta=None
    def N(i):
        return names[i]
    def E(i):
        return expressions[i]
    def allrefs(ids):
        s=set()
        for i in ids:
            s.update(E(i)[0])
        return s
    for line_number, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(),1):
        row=json.loads(line)
        if "meta" in row:
            if line_number != 1 or meta is not None:
                raise ValueError("metadata must occur exactly once, first")
            meta=row["meta"]
            if meta["format"]["version"] != "3.1.0":
                raise ValueError("unrecognized format")
        elif "in" in row:
            i=row["in"]
            if i in names:
                raise ValueError("duplicate name index")
            if "str" in row:
                v=row["str"]; names[i]=N(v["pre"])+(("str",v["str"]),)
            elif "num" in row:
                v=row["num"]; names[i]=N(v["pre"])+(("num",v["i"]),)
            else:
                raise ValueError("unknown name constructor")
        elif "il" in row:
            i=row["il"]
            if i in levels:
                raise ValueError("duplicate level index")
            tag=next(k for k in row if k!="il")
            v=row[tag]
            if tag=="succ": val=levels[v]
            elif tag in ("max","imax"): val=[levels[x] for x in v]
            elif tag=="param": val=N(v)
            else: raise ValueError("unknown level constructor")
            levels[i]=digest([tag,val])
        elif "ie" in row:
            i=row["ie"]
            if i in expressions:
                raise ValueError("duplicate expression index")
            tag=next(k for k in row if k!="ie")
            v=row[tag]; refs=set()
            if tag in ("bvar","natVal","strVal"):
                val=v
                if tag=="natVal": refs.add((("str","Nat"),))
                if tag=="strVal": refs.add((("str","String"),))
            elif tag=="sort": val=levels[v]
            elif tag=="const":
                refs.add(N(v["name"])); val=[N(v["name"]),[levels[u] for u in v["us"]]]
            elif tag in ("app","lam","forallE","letE"):
                fields={"app":("fn","arg"),"lam":("type","body"),"forallE":("type","body"),"letE":("type","value","body")}[tag]
                refs=allrefs(v[f] for f in fields)
                val=[E(v[f])[1] for f in fields]
                if "binderInfo" in v: val.append(v["binderInfo"])
                if "nondep" in v: val.append(v["nondep"])
            elif tag=="proj":
                refs=set(E(v["struct"])[0]); refs.add(N(v["typeName"]))
                val=[N(v["typeName"]),v["idx"],E(v["struct"])[1]]
            elif tag=="mdata":
                expressions[i]=E(v["expr"]); continue
            else: raise ValueError("unknown expression constructor: "+tag)
            expressions[i]=(refs,digest([tag,val]))
        else:
            if len(row)!=1:
                raise ValueError("unknown declaration record")
            kind,decl=next(iter(row.items()))
            if kind=="inductive":
                parts=decl["types"]+decl["ctors"]+decl["recs"]
            elif kind in ("axiom","def","opaque","thm","quot"):
                parts=[decl]
            else: raise ValueError("unknown declaration kind: "+kind)
            owned=[N(p["name"]) for p in parts]
            refs=set()
            unsafe=False
            types=[]
            for p in parts:
                refs.update(allrefs([p["type"]]))
                types.append({"name":N(p["name"]),"sha256":E(p["type"])[1]})
                if "value" in p: refs.update(allrefs([p["value"]]))
                for r in p.get("rules",[]):
                    refs.update(allrefs([r["rhs"]])); refs.add(N(r["ctor"]))
                for key in ("all","ctors"):
                    refs.update(N(x) for x in p.get(key,[]))
                if "induct" in p: refs.add(N(p["induct"]))
                unsafe |= p.get("isUnsafe",False) or p.get("safety","safe")!="safe"
            idx=len(nodes)
            nodes.append({"id":idx,"line":line_number,"kind":kind,"names":owned,"refs":refs,"unsafe":unsafe,"types":types})
            for name in owned:
                owners.setdefault(name,[]).append(idx)
    if meta is None:
        raise ValueError("missing metadata")
    duplicate_names={n:ids for n,ids in owners.items() if len(ids)>1}
    missing=set()
    for node in nodes:
        edges=set()
        for ref in node["refs"]:
            if ref not in owners: missing.add(ref)
            edges.update(owners.get(ref,[]))
        node["edges"]=edges-{node["id"]}
    root_name=tuple(("str",x) for x in target.split(".")) if isinstance(target,str) else target
    if root_name is not None and root_name not in owners:
        raise ValueError("target declaration is absent")
    closure=set()
    todo=list(owners[root_name]) if root_name is not None else list(range(len(nodes)))
    while todo:
        i=todo.pop()
        if i in closure: continue
        closure.add(i); todo.extend(nodes[i]["edges"]-closure)
    selected_missing={ref for i in closure for ref in nodes[i]["refs"] if ref not in owners}
    def namejson(n): return [[kind,value] for kind,value in n]
    def show(n):
        return ".".join((str(v) if k=="num" or "." not in str(v) else "«"+str(v)+"»") for k,v in n)
    out={"scope":"structural_graph_only_not_kernel_verification", "sha256":hashlib.sha256(Path(path).read_bytes()).hexdigest(),
         "metadata":meta,"target":target,"record_count":len(nodes),"closure_record_count":len(closure),
         "structurally_closed":not selected_missing,"unambiguous_names":not duplicate_names,
         "missing_constants":[namejson(n) for n in sorted(selected_missing)],
         "duplicate_names":[{"name":namejson(n),"owners":ids} for n,ids in duplicate_names.items()],
         "axioms":[{"name":show(n),"name_components":namejson(n),"record":i} for i in sorted(closure) if nodes[i]["kind"]=="axiom" for n in nodes[i]["names"]],
         "unsafe_records":[i for i in sorted(closure) if nodes[i]["unsafe"]],
         "records":[{"id":i,"line":nodes[i]["line"],"kind":nodes[i]["kind"],"names":[namejson(n) for n in nodes[i]["names"]],"display_names":[show(n) for n in nodes[i]["names"]],"dependencies":sorted(nodes[i]["edges"]),"type_fingerprints":nodes[i]["types"]} for i in sorted(closure)]}
    return out

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("export")
    p.add_argument("--target")
    p.add_argument("--output",required=True)
    args=p.parse_args()
    result=audit(args.export,args.target)
    Path(args.output).write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({k:v for k,v in result.items() if k not in ("records","metadata")},indent=2))
    if not result["structurally_closed"] or not result["unambiguous_names"] or result["unsafe_records"]:
        raise SystemExit(3)
