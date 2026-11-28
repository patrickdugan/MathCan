"""RAM-14: source-statement-only structural tactic templates.

POSTHOC diagnostic for already-opened GramianTransfer failures. Candidate
generation reads the target statement and earlier declarations' *headers*
only. Reference proof bodies are never used as tactic features.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import json
import re

SOURCE_SHA = "f427e0ef4a61093304d12ca2c0dc943d8d2429e5"
SOURCE_BLOB = "f07e99a3f27acba22c2c0c6b3f675a68ab774ab2"
TARGETS = ("transport_iterate", "observable_transport")
ALLOWED_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
FAMILIES = ("nat_induction", "simp_prior", "rewrite_prior")
MAX_PER_FAMILY = 16
MAX_TOTAL = 48
DECL = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.M)
DEFINE = re.compile(r"^(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b", re.M)
NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def mask_comments(text: str) -> str:
    """Erase nested Lean comments and line comments, retaining line breaks.

    The scanner does not treat string literals as comments; source-visible
    declaration lines in this registered cohort do not contain multiline
    Lean strings.
    """
    out = []
    i, depth = 0, 0
    while i < len(text):
        ch = text[i]
        pair = text[i:i+2]
        if pair == "/-":
            depth += 1
            out.extend((" ", " "))
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            out.extend((" ", " "))
            i += 2
        elif depth:
            out.append("\n" if ch == "\n" else " ")
            i += 1
        elif pair == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(ch)
            i += 1
    if depth:
        raise ValueError("unclosed Lean comment")
    return "".join(out)


def statement_scope(source: str, target: str) -> tuple[str, str]:
    if not NAME.fullmatch(target):
        raise ValueError("bad theorem identifier")
    masked = mask_comments(source)
    matches = list(DECL.finditer(masked))
    targets = [m for m in matches if m.group(1) == target]
    if len(targets) != 1:
        raise ValueError("ambiguous theorem declaration")
    begin = targets[0].start()
    after = masked[begin:]
    marker = after.find(":=")
    if marker == -1:
        raise ValueError("theorem header lacks :=")
    return masked[:begin], masked[begin:begin+marker]


def earlier_headers(prefix: str) -> list[tuple[str, str]]:
    """Only previous theorem headers, stopping at their first := marker."""
    positions = list(DECL.finditer(prefix))
    ret = []
    for match in positions:
        after = prefix[match.start():]
        pos = after.find(":=")
        if pos < 0:
            continue
        header = after[:pos]
        # Prevent carrying a later declaration after a missing proof marker.
        if DECL.search(header, 1):
            continue
        ret.append((match.group(1), header))
    return ret


def word_tokens(text: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", text))


@dataclass(frozen=True)
class Candidate:
    family: str
    script: str
    witnesses: tuple[str, ...]

    def as_dict(self):
        return dict(family=self.family, script=self.script, witnesses=list(self.witnesses))


def generate(source: str, target: str) -> list[Candidate]:
    previous, header = statement_scope(source, target)
    source_tokens = word_tokens(header)
    earlier = [(name, old) for name, old in earlier_headers(previous)
               if name != target and len((source_tokens & word_tokens(old)) &
                       {"iterateState", "transport", "readout", "StateGauge"}) >= 2]
    # All usable definitions must be declared before the target AND mentioned
    # in its statement. This forbids borrowing the target reference proof.
    definitions = [m.group(1) for m in DEFINE.finditer(previous)
                   if m.group(1) in source_tokens]
    definitions = list(dict.fromkeys(definitions))[:3]
    nat_vars = re.findall(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*Nat\s*\)", header)
    value_vars = [n for n, typ in re.findall(
        r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*([^\s()]+)\s*\)", header)
        if typ not in ("Nat", "Int", "Bool", "Prop", "Type")]
    gauges = re.findall(
        r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:\s*StateGauge\b[^)]*\)", header)
    # The inverse-law fields must already be declared in a visible structure
    # before the theorem, as opposed to invented by a script template.
    # Read structural field names only from the preceding *structure
    # declaration* block, never from an earlier theorem's proof body.
    structure = re.search(r"^structure\s+StateGauge\b[^\n]*(?:\n(?!(?:def|theorem|lemma|structure|namespace|end)\b)[^\n]*)*",
                          previous, re.M)
    visible_struct = structure.group(0) if structure else ""
    fields = [f"{g}.{field}" for g in gauges[:1]
              for field in ("left_inv", "right_inv")
              if re.search(r"^\s+" + field + r"\s*:", visible_struct, re.M)]
    inv = fields[:1]
    deflist = definitions[:2]
    all_lemmas = deflist + inv
    prior_names = [n for n, _ in earlier][:2]
    candidates = []
    def add(fam: str, script: str, evidence: list[str]):
        if fam not in FAMILIES:
            raise ValueError("unknown tactic family")
        if any(x in script for x in ("\r", "sorry", "admit", "run_tac", "set_option")):
            raise ValueError("disallowed candidate syntax")
        if not any(x.family == fam and x.script == script for x in candidates):
            candidates.append(Candidate(fam, script, tuple(evidence)))
    # One-shot source-visible Nat induction and deterministic cleanup.
    for n in nat_vars[:2]:
        for x in value_vars[:2]:
            for tact in ("simp_all", "simp"):
                for subset in (all_lemmas, deflist, inv, []):
                    names = [s for s in subset if s]
                    suffix = f" [{', '.join(names)}]" if names else ""
                    add("nat_induction",
                        f"induction {n} generalizing {x} <;> {tact}{suffix}",
                        [f"binder:{n}:Nat", f"generalizing:{x}",
                         *[f"prior_or_field:{v}" for v in names]])
            # A natural induction is also useful as a single transition in
            # a multigoal proof-search engine, independently of simplifiers.
            add("nat_induction", f"induction {n} generalizing {x}",
                [f"binder:{n}:Nat", f"generalizing:{x}"])
    for script in ("simp", "simp_all"):
        for terms in (all_lemmas, deflist, inv):
            if terms:
                add("simp_prior", f"{script} [{', '.join(terms)}]",
                    [f"prior_or_field:{t}" for t in terms])
    for p in prior_names:
        add("rewrite_prior", f"rw [{p}]", [f"earlier_theorem:{p}"])
        add("rewrite_prior", f"simp [{p}]", [f"earlier_theorem:{p}"])
        add("rewrite_prior", f"simpa [{p}]", [f"earlier_theorem:{p}"])
        if inv:
            add("rewrite_prior", f"simp [{p}, {inv[0]}]",
                [f"earlier_theorem:{p}", f"field:{inv[0]}"])
            add("rewrite_prior", f"simpa [{p}, {inv[0]}]",
                [f"earlier_theorem:{p}", f"field:{inv[0]}"])
    caps = {f:0 for f in FAMILIES}
    output = []
    for item in candidates:
        if caps[item.family] < MAX_PER_FAMILY and len(output) < MAX_TOTAL:
            caps[item.family] += 1
            output.append(item)
    return output


def describe(source: str, target: str) -> dict:
    previous, header = statement_scope(source, target)
    items = generate(source, target)
    return dict(target=target, statement_hash=sha(header.encode()),
                previous_source_hash=sha(previous.encode()),
                candidate_count=len(items), candidates=[x.as_dict() for x in items])


if __name__ == "__main__":
    import argparse
    from pathlib import Path
    p=argparse.ArgumentParser()
    p.add_argument("source",type=Path)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    src=args.source.read_text(encoding="utf8")
    result=[describe(src,t) for t in TARGETS]
    body=json.dumps(result,indent=2)
    if args.out:
        args.out.write_text(body+"\n")
    else:
        print(body)
