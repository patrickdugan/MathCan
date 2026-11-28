"""MM05: prospectively frozen source-disjoint, alpha-signature grouped corpus."""
import argparse
import hashlib
import json
from pathlib import Path
from collections import Counter

from setmm_corpus import BLOB, PIN, VERIFIER, canonical, digest, extract, load_verifier, require, source_prefix, strip_comments

FIRST = 601
LAST = 2400
SALT = "mm05-alpha-family-20261127-v1"

def family(sig):
    types = {v:t for t,v in sig["floating"]}
    renames = {}
    def token(s):
        if s not in types:
            return ["constant", s]
        if s not in renames:
            renames[s] = len(renames)
        return ["variable", types[s], renames[s]]
    goal = [token(s) for s in sig["statement"]]
    hyp = [[token(s) for s in h] for h in sig["essential"]]
    require(set(renames) == set(types), "unused mandatory variable")
    dv = sorted(sorted((renames[a], renames[b])) for a,b in sig["distinct"])
    return digest([goal,hyp,dv])

def partition(fam):
    k = int(digest([SALT,fam])[:16],16) % 100
    return "train" if k < 70 else "dev" if k < 85 else "family_test"

def main():
    p = argparse.ArgumentParser()
    p.add_argument("verifier",type=Path)
    p.add_argument("db",type=Path)
    p.add_argument("out",type=Path)
    a = p.parse_args()
    raw = a.db.read_bytes()
    require(hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()==BLOB,"source git blob")
    c = extract(load_verifier(a.verifier),a.db,limit=LAST)
    prior = {family(x["statement"]) for x in c.proofs if x["source_index"] < FIRST}
    families = {x["label"]:family(x["statement"]) for x in c.proofs}
    oracle = {y["id"]:y for y in c.oracle}
    rows, ys, excluded = [], [], Counter()
    manifest = []
    for proof in c.proofs:
        i,f = proof["source_index"],families[proof["label"]]
        manifest.append({"id":proof["label"],"source_index":i,"family":f,
                         "split":"spent" if i < FIRST else "excluded_prior_family" if f in prior else partition(f)})
    for x in c.inputs:
        f = families[x["id"]]
        if x["source_index"] < FIRST:
            excluded["spent"] += 1
            continue
        if f in prior:
            excluded["prior_alpha_family"] += 1
            continue
        rows.append(dict(x, family=f, split=partition(f)))
        ys.append(oracle[x["id"]])
    splits = Counter(x["split"] for x in rows)
    require(all(splits[s]>0 for s in ("train","dev","family_test")),"empty split")
    by = {s:{x["family"] for x in rows if x["split"]==s} for s in splits}
    require(not any(by[s]&by[t] for s in by for t in by if s!=t),"family leakage")
    require(not any(v&prior for v in by.values()),"prior family leakage")
    a.out.mkdir(parents=True,exist_ok=True)
    for name, data in (("inputs",rows),("oracle",ys),("proofs",c.proofs),("family_manifest",manifest)):
        (a.out/(name+".jsonl")).write_bytes(b"".join(canonical(x)+b"\n" for x in data))
    prefix = strip_comments(source_prefix(raw.decode("ascii"),c.names,c.replacements))
    (a.out/"expanded-prefix.mm").write_text(prefix,encoding="ascii")
    receipt = {"schema":"mm05-family-v1","source_commit":PIN,"source_git_blob":BLOB,
               "source_sha256":hashlib.sha256(raw).hexdigest(),"verifier_commit":VERIFIER,
               "verifier_sha256":hashlib.sha256(a.verifier.read_bytes()).hexdigest(),
               "window":[FIRST,LAST],"salt":SALT,"verified_prefix_theorems":len(c.names),
               "expanded_and_replayed":len(c.replacements),"excluded":dict(excluded),
               "splits":dict(splits),"family_counts":{s:len(v) for s,v in by.items()},
               "candidate_checks":sum(len(x["candidates"]) for x in rows),
               "alternative_candidates":sum(len(y["accepted_actions"])-1 for y in ys),
               "artifact_sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in a.out.iterdir() if p.is_file()}}
    (a.out/"receipt.json").write_bytes(canonical(receipt)+b"\n")
    print(json.dumps(receipt,indent=2))

if __name__=="__main__":
    main()
