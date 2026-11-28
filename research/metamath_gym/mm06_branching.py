"""MM06: multiple hidden assertion labels with scoped branching oracle."""
import argparse
from collections import Counter, defaultdict
import hashlib
import itertools
import json
from pathlib import Path

from mm05_family import family
from setmm_corpus import (
    BLOB, PIN, VERIFIER, canonical, digest, extract, load_verifier, require,
    signature, source_prefix, strip_comments,
)

FIRST, LAST = 2401, 4200
SALT = "mm06-branching-20261127-v1"
BANK, SAMPLE, CAP = 6, 96, 256

def partition(key):
    n = int(digest([SALT, "split", key])[:16], 16) % 100
    return "train" if n < 70 else "dev" if n < 85 else "family_test"

def mask_depth(key):
    return 2 + int(digest([SALT, "depth", key])[:16], 16) % 3

def exhaustive(template, banks, initial, target, transition):
    """Exact tree search; failed edges count, no future reference states."""
    valid = []
    calls = 0
    def visit(pos, stack, chosen):
        nonlocal calls
        # Fixed runs are executed once per reached branch.
        while pos < len(template) and isinstance(template[pos], str):
            calls += 1
            stack = transition(stack, template[pos])
            if stack is None:
                return
            pos += 1
        if pos == len(template):
            if stack == [target]:
                valid.append(list(chosen))
            return
        for label in banks[template[pos]]:
            calls += 1
            after = transition(stack, label)
            if after is not None:
                visit(pos + 1, after, (*chosen, label))
    visit(0, initial, ())
    return valid, calls

def collect(mm, db):
    prior = set()
    rows, oracle = [], []
    excluded = Counter()
    def on_expanded(c, label, index, sig, proof, active, variables, distinct):
        key = family(sig)
        if index < FIRST:
            prior.add(key)
            return
        if key in prior:
            excluded["prior_expanded_alpha_family"] += 1
            return
        if len(proof) > CAP:
            excluded["over_cap"] += 1
            return
        depth = mask_depth(key)
        groups = defaultdict(list)
        for name, entry in c.labels.items():
            if entry[0] in ("$a", "$p"):
                s = signature(entry)
                groups[s["arity"], s["statement"][0]].append(name)
        def transition(stack, name):
            require(name in c.labels and
                    (c.labels[name][0] in ("$a", "$p") or name in active),
                    "out-of-scope reference")
            copied = list(stack)
            try:
                c.treat_step(c.labels[name], copied)
            except mm.MMError:
                return None
            return copied
        stack = []
        states = {}
        for i, name in enumerate(proof):
            states[i] = stack
            stack = transition(stack, name)
            require(stack is not None, "source replay")
        require(stack == [sig["statement"]], "source conclusion")
        # Deterministic root/arity pools; avoid an all-database scan at every position.
        pools = {}
        positions = [i for i, name in enumerate(proof)
                     if c.labels[name][0] in ("$a", "$p")]
        positions.sort(key=lambda i: digest([SALT, label, "position", i]))
        selected = {}
        for i in positions:
            if any(abs(i-j) < 2 for j in selected):
                continue
            gold = proof[i]
            gs = signature(c.labels[gold])
            gkey = (gs["arity"], gs["statement"][0])
            if gkey not in pools:
                pools[gkey] = sorted(groups[gkey],
                    key=lambda name: digest([SALT, label, "pool", name]))[:SAMPLE]
            legal, other = [], []
            for name in pools[gkey]:
                if name == gold:
                    continue
                if transition(states[i], name) is None:
                    other.append(name)
                else:
                    legal.append(name)
            if not legal:
                continue
            # Gold plus up to three legal alternatives; fill to six with
            # other sampled assertions, preferring remaining legal alternatives.
            chosen = [gold] + legal[:3]
            chosen += (legal[3:] + other)[:BANK-len(chosen)]
            if len(chosen) < 4:
                continue
            selected[i] = sorted(chosen,
                key=lambda name: digest([SALT, label, "bank", i, name]))
            if len(selected) == depth:
                break
        if len(selected) != depth:
            excluded["insufficient_branch_positions"] += 1
            return
        indices = sorted(selected)
        first = indices[0]
        banks = [selected[i] for i in indices]
        template = [indices.index(i) if i in selected else proof[i]
                    for i in range(first, len(proof))]
        solutions, calls = exhaustive(template, banks, states[first], sig["statement"], transition)
        reference = [proof[i] for i in indices]
        require(reference in solutions, "reference missing")
        # Full upstream recheck every accepted tuple, using its exact scope.
        f, e = sig["floating"], sig["essential"]
        for choices in solutions:
            full = proof[:first] + [choices[t] if isinstance(t,int) else t for t in template]
            c.verify_proofs = True
            mm.MM.verify(c, f, e, sig["statement"], full)
        rows.append({"id":label, "source_index":index, "family":key,
                     "split":partition(key), "depth":depth, "target":sig["statement"],
                     "prefix":proof[:first], "prefix_stack":states[first],
                     "template":template,"banks":banks,"variables":variables,
                     "distinct":distinct,
                     "active_hypotheses":{a:signature(c.labels[a]) for a in sorted(active)},
                     "signatures":{a:signature(c.labels[a])
                         for a in sorted(set(itertools.chain.from_iterable(banks)) |
                                         {t for t in template if isinstance(t,str)})}})
        oracle.append({"id":label,"reference":reference,"accepted":solutions,
                       "exhaustive_transitions":calls})
    c = extract(mm, db, limit=LAST, on_expanded=on_expanded, single_masks=False)
    # Exclude ALL prior families, including those over the original expansion cap.
    prior = {family(x["statement"]) for x in c.proofs if x["source_index"] < FIRST}
    keep = {x["id"] for x in rows if x["family"] not in prior}
    excluded["prior_unexpanded_alpha_family"] = len(rows) - len(keep)
    rows = [x for x in rows if x["id"] in keep]
    oracle = [x for x in oracle if x["id"] in keep]
    return c, rows, oracle, excluded

def main():
    p = argparse.ArgumentParser()
    p.add_argument("verifier", type=Path)
    p.add_argument("db", type=Path)
    p.add_argument("out", type=Path)
    a = p.parse_args()
    raw = a.db.read_bytes()
    require(hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest() == BLOB, "db blob")
    c, rows, oracle, excluded = collect(load_verifier(a.verifier), a.db)
    splits = Counter(x["split"] for x in rows)
    by = {s:{x["family"] for x in rows if x["split"]==s} for s in splits}
    require(all(splits[s]>0 for s in ("train","dev","family_test")), "empty split")
    require(not any(by[s]&by[t] for s in by for t in by if s!=t), "family leakage")
    require(len(rows)==len(oracle), "oracle coverage")
    a.out.mkdir(parents=True, exist_ok=True)
    for name, data in (("inputs",rows),("oracle",oracle),("proofs",c.proofs)):
        (a.out/(name+".jsonl")).write_bytes(b"".join(canonical(x)+b"\n" for x in data))
    prefix = strip_comments(source_prefix(raw.decode("ascii"),c.names,c.replacements))
    (a.out/"expanded-prefix.mm").write_text(prefix, encoding="ascii")
    receipt = {"schema":"mm06-branching-v1","source_commit":PIN,"source_git_blob":BLOB,
        "source_sha256":hashlib.sha256(raw).hexdigest(),"verifier_commit":VERIFIER,
        "verifier_sha256":hashlib.sha256(a.verifier.read_bytes()).hexdigest(),
        "window":[FIRST,LAST],"salt":SALT,"verified_prefix_theorems":len(c.names),
        "expanded_and_replayed":len(c.replacements),"excluded":dict(excluded),
        "splits":dict(splits),"depth_counts":dict(Counter(x["depth"] for x in rows)),
        "family_counts":{s:len(v) for s,v in by.items()},
        "exhaustive_transitions":sum(x["exhaustive_transitions"] for x in oracle),
        "solution_tuples":sum(len(x["accepted"]) for x in oracle),
        "alternative_tuples":sum(len(x["accepted"])-1 for x in oracle),
        "artifact_sha256":{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in a.out.iterdir() if p.is_file()}}
    (a.out/"receipt.json").write_bytes(canonical(receipt)+b"\n")
    print(json.dumps(receipt,indent=2))

if __name__ == "__main__":
    main()
