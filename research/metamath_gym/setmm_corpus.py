"""MM-GYM-02: fixed-window extraction and replay using pinned mmverify.py."""
import argparse
from collections import defaultdict
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import textwrap

PIN = "806509385370b29fe8b1723804777ac21b1ce194"
BLOB = "141813b90eb65b4c3c0d68dc02bd18ff9e2dc953"
VERIFIER = "63a2aa3815cd5bf67892dbfc7f2048cbb177524c"
LIMIT = 600
CAP = 512
BANK = 12

def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(",", ":")).encode()

def digest(x):
    return hashlib.sha256(canonical(x)).hexdigest()

def require(cond, msg):
    if not cond:
        raise ValueError(msg)

@dataclass(frozen=True)
class Node:
    label: str
    children: tuple
    length: int

def decode(proof, implicit, arity, cap=CAP):
    """Decode references, preserving DAG reuse until bounded expansion."""
    stack, saved, used = [], [], set()
    applications = 0
    def apply(label):
        nonlocal applications
        require(isinstance(label, str), "missing label")
        n = arity(label)
        require(0 <= n <= len(stack), "stack underflow")
        children = tuple(stack[-n:]) if n else ()
        if n:
            del stack[-n:]
        stack.append(Node(label, children, 1 + sum(x.length for x in children)))
        used.add(label)
        applications += 1
    if proof and proof[0] == "(":
        end = proof.index(")")
        refs = list(implicit) + proof[1:end]
        acc, pending = 0, False
        for ch in "".join(proof[end+1:]):
            if "U" <= ch <= "Y":
                acc, pending = 5*acc + ord(ch)-ord("U")+1, True
            elif "A" <= ch <= "T":
                i = 20*acc + ord(ch)-ord("A")
                acc, pending = 0, False
                if i < len(refs):
                    apply(refs[i])
                else:
                    j = i-len(refs)
                    require(j < len(saved), "invalid saved reference")
                    stack.append(saved[j])
            elif ch == "Z":
                require(not pending and stack, "invalid save")
                saved.append(stack[-1])
            else:
                raise ValueError("invalid compressed proof character")
        require(not pending, "unterminated reference")
    else:
        for label in proof:
            apply(label)
    require(len(stack) == 1, "final stack size")
    root, expanded = stack[0], None
    if root.length <= cap:
        expanded, todo = [], [(root, False)]
        while todo:
            node, visited = todo.pop()
            if visited:
                expanded.append(node.label)
            else:
                todo.append((node, True))
                todo.extend((child, False) for child in reversed(node.children))
        require(len(expanded) == root.length, "expanded length mismatch")
    return used, applications, root.length, expanded

def signature(entry):
    kind, value = entry
    if kind in ("$f", "$e"):
        return {"kind": kind, "statement": value, "arity": 0}
    dv, f, e, stmt = value
    return {"kind": kind, "statement": stmt, "floating": f, "essential": e,
            "distinct": sorted(dv), "arity": len(f)+len(e)}

def source_prefix(source, names, replacements):
    """Copy exact source through named prefix; replace only proof bodies."""
    spans, depth, comment, inside = [], 0, False, False
    previous = label = start = stop = None
    seen = []
    for m in re.finditer(r"\S+", source):
        tok = m.group()
        if comment:
            if tok == "$)":
                comment = False
            continue
        if tok == "$(":
            comment = True
            continue
        if tok == "$[":
            raise ValueError("external includes unsupported")
        if tok == "$" + "{":
            depth += 1
        elif tok == "$}":
            depth -= 1
            require(depth >= 0, "unbalanced scope")
        elif tok == "$p":
            require(not inside, "nested proof")
            label, inside = previous, True
        elif tok == "$=" and inside:
            start = m.end()
        elif tok == "$." and inside:
            require(start is not None, "missing proof start")
            seen.append(label)
            require(label == names[len(seen)-1], "source order mismatch")
            if label in replacements:
                spans.append((start, m.start(), " " + " ".join(replacements[label]) + " "))
            inside, start = False, None
            if len(seen) == len(names):
                stop = m.end()
                break
        previous = tok
    require(stop is not None and seen == names, "incomplete prefix")
    require(len(spans) == len(replacements), "replacement count")
    out, pos = [], 0
    for lo, hi, new in spans:
        out.extend((source[pos:lo], new))
        pos = hi
    out.append(source[pos:stop])
    out.append("\n" + "$}\n"*depth)
    return "".join(out)

def strip_comments(source):
    """Discard comment tokens, including C's inline include marker metadata.

    Re-emit precisely the remaining whitespace-delimited mathematical tokens.
    This avoids unbalanced Begin/End pseudo-includes when a prefix ends inside
    an originally inlined file. Actual include directives remain prohibited.
    """
    tokens, comment = [], False
    for tok in source.split():
        if comment:
            if tok == "$)":
                comment = False
            elif tok == "$(":
                raise ValueError("nested comment")
        elif tok == "$(":
            comment = True
        else:
            require(tok not in ("$)", "$[", "$]"), "unexpected comment or include delimiter")
            tokens.append(tok)
    require(not comment, "unterminated comment")
    return textwrap.fill(" ".join(tokens), width=100, break_long_words=False,
                         break_on_hyphens=False) + "\n"

def load_verifier(path):
    spec = importlib.util.spec_from_file_location("pinned_mmverify", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    mod.verbosity, mod.logfile = 0, sys.stderr
    return mod

class StopPrefix(Exception):
    pass

def extract(mm, db, limit=LIMIT):
    class Tracking(mm.Toks):
        previous = None
        p_label = None
        def readc(self):
            tok = super().readc()
            if tok == "$p":
                self.p_label = self.previous
            self.previous = tok
            return tok

    class Collector(mm.MM):
        def __init__(self):
            super().__init__(None, None)
            self.names, self.inputs, self.oracle, self.proofs = [], [], [], []
            self.replacements, self.closure, self.hashes = {}, {}, {}
            self.current = None

        def read_p_stmt(self, toks):
            if len(self.names) >= limit:
                raise StopPrefix()
            self.current = toks.p_label
            return super().read_p_stmt(toks)

        def dep(self, label):
            if label not in self.hashes:
                entry = self.labels[label]
                require(entry[0] == "$a", "unverified dependency")
                self.hashes[label] = digest([label, signature(entry)])
                self.closure[label] = {label}
            return self.hashes[label], self.closure[label]

        def verify(self, f, e, conclusion, proof):
            super().verify(f, e, conclusion, proof)
            label = self.current
            require(isinstance(label, str) and label not in self.names, "root label")
            self.names.append(label)
            index = len(self.names)
            active = {lab for fr in self.fs for group in (fr.f_labels, fr.e_labels)
                      for lab in group.values()}
            variables = sorted({v for fr in self.fs for v in fr.v})
            distinct = sorted({p for fr in self.fs for p in fr.d})
            implicit = ([self.fs.lookup_f(v) for _, v in f] +
                        [self.fs.lookup_e(stmt) for stmt in e])
            def arity(lab):
                require(lab in self.labels, "unknown or future label")
                entry = self.labels[lab]
                require(entry[0] in ("$a", "$p") or lab in active, "inactive hypothesis")
                return signature(entry)["arity"]
            used, dag, length, expanded = decode(proof, implicit, arity)
            deps = sorted(lab for lab in used if self.labels[lab][0] in ("$a", "$p"))
            hashes, axioms = {}, set()
            for dep in deps:
                hashes[dep], closure = self.dep(dep)
                axioms.update(closure)
            statement = signature(("$p", self.fs.make_assertion(conclusion)))
            self.hashes[label] = digest([label, statement, proof, hashes])
            self.closure[label] = axioms
            self.proofs.append({"label": label, "source_index": index,
                "statement": statement, "statement_sha256": digest(statement),
                "dependency_sha256": self.hashes[label], "direct_dependencies": deps,
                "transitive_a_labels": sorted(axioms),
                "normalized_encoded_bytes": len(" ".join(proof).encode("ascii")),
                "dag_label_applications": dag, "expanded_label_steps": length,
                "expanded_replay": expanded is not None})
            if expanded is None:
                return
            super().verify(f, e, conclusion, expanded)
            self.replacements[label] = expanded
            groups = defaultdict(list)
            for lab, entry in self.labels.items():
                if entry[0] in ("$a", "$p"):
                    sig = signature(entry)
                    groups[(sig["arity"], sig["statement"][0])].append(lab)
            viable = []
            for i, lab in enumerate(expanded):
                if self.labels[lab][0] in ("$a", "$p"):
                    sig = signature(self.labels[lab])
                    pool = groups[(sig["arity"], sig["statement"][0])]
                    if len(pool) >= 4:
                        viable.append((i, pool))
            if not viable:
                return
            mask, pool = min(viable, key=lambda x: digest([PIN, label, x[0]]))
            gold = expanded[mask]
            negatives = sorted((lab for lab in pool if lab != gold),
                               key=lambda lab: digest([PIN, label, "bank", lab]))[:BANK-1]
            bank = sorted([gold]+negatives, key=lambda lab: digest([PIN, label, "order", lab]))
            prefix, suffix = expanded[:mask], expanded[mask+1:]
            stack = self.treat_normal_proof(prefix)
            accepted, immediate = [], []
            for candidate in bank:
                try:
                    copied = list(stack)
                    self.treat_step(self.labels[candidate], copied)
                    immediate.append(candidate)
                except mm.MMError:
                    pass
                try:
                    super().verify(f, e, conclusion, prefix+[candidate]+suffix)
                    accepted.append(candidate)
                except mm.MMError:
                    pass
            require(gold in accepted and set(accepted) <= set(immediate), "mask inconsistency")
            split = "train" if index <= 200 else "dev" if index <= 400 else "public_challenge"
            self.inputs.append({"id": label, "split": split, "source_index": index,
                "target": conclusion, "prefix": prefix, "suffix": suffix, "prefix_stack": stack,
                "variables": variables, "distinct": distinct,
                "active_hypotheses": {lab: signature(self.labels[lab]) for lab in sorted(active)},
                "candidates": bank,
                "candidate_signatures": {lab: signature(self.labels[lab]) for lab in bank}})
            self.oracle.append({"id": label, "reference_action": gold,
                "accepted_actions": accepted, "immediate_legal_actions": immediate,
                "expanded_label_steps": length})
    c = Collector()
    with db.open("r", encoding="ascii") as file:
        try:
            c.read(Tracking(file))
        except StopPrefix:
            pass
    require(len(c.names) == limit, "incomplete theorem window")
    return c

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("verifier", type=Path)
    parser.add_argument("database", type=Path)
    parser.add_argument("out", type=Path)
    a = parser.parse_args()
    raw = a.database.read_bytes()
    require(hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest() == BLOB,
            "set.mm Git blob mismatch")
    c = extract(load_verifier(a.verifier), a.database)
    a.out.mkdir(parents=True, exist_ok=True)
    for name, rows in (("inputs", c.inputs), ("oracle", c.oracle), ("proofs", c.proofs)):
        (a.out/(name+".jsonl")).write_bytes(b"".join(canonical(row)+b"\n" for row in rows))
    (a.out/"expanded-prefix.mm").write_text(strip_comments(source_prefix(raw.decode("ascii"), c.names,
                                                        c.replacements)), encoding="ascii")
    splits = {s: sum(x["split"] == s for x in c.inputs)
              for s in ("train", "dev", "public_challenge")}
    require(all(splits.values()), "empty split")
    receipt = {"schema": "mm-gym-02-v1", "source_commit": PIN, "source_git_blob": BLOB,
        "source_sha256": hashlib.sha256(raw).hexdigest(), "verifier_commit": VERIFIER,
        "verifier_sha256": hashlib.sha256(a.verifier.read_bytes()).hexdigest(),
        "verified_prefix_theorems": len(c.names), "expanded_and_replayed": len(c.replacements),
        "masked_tasks": len(c.inputs), "splits": splits,
        "candidate_checks": sum(len(x["candidates"]) for x in c.inputs),
        "accepted_candidates": sum(len(x["accepted_actions"]) for x in c.oracle),
        "alternative_candidates": sum(len(x["accepted_actions"])-1 for x in c.oracle),
        "artifact_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in a.out.iterdir() if p.is_file()}}
    (a.out/"receipt.json").write_bytes(canonical(receipt)+b"\n")
    print(json.dumps(receipt, indent=2))

if __name__ == "__main__":
    main()
