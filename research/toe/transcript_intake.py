"""Rights-aware local TOE caption importer. No scraping or remote downloading.

Full source text is retained only in the ignored research/toe/private/ folder.
Transcripts from third-party sources require an independently reviewed usage basis.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

INDEX=Path(__file__).with_name("EPISODE_INDEX.json")
TIMESTAMP=re.compile(r"^\s*((?:\d{1,2}:)?\d\d:\d\d[.,]\d+)\s+-->\s+((?:\d{1,2}:)?\d\d:\d\d[.,]\d+)")


def normalize_stamp(text):
    parts=text.replace(",",".").split(":")
    if len(parts)==2:parts=["00"]+parts
    if len(parts)!=3:raise ValueError("timestamp fields")
    hour,minute,second=parts
    if not 0<=int(minute)<60 or not 0<=float(second)<60:raise ValueError("timestamp range")
    return "%02d:%02d:%06.3f"%(int(hour),int(minute),float(second))


def parse_captions(text):
    """Parse timed SRT or VTT caption blocks, without inventing speaker labels."""
    if not text or not isinstance(text,str):raise ValueError("empty captions")
    chunks=re.split(r"\n\s*\n",text.replace("\r\n","\n").lstrip("\ufeff"))
    results=[]
    for chunk in chunks:
        lines=chunk.splitlines()
        idx=next((i for i,line in enumerate(lines) if TIMESTAMP.match(line)),None)
        if idx is None:continue
        match=TIMESTAMP.match(lines[idx])
        body="\n".join(lines[idx+1:]).strip()
        if not body:continue
        start,end=normalize_stamp(match[1]),normalize_stamp(match[2])
        if end<start:raise ValueError("negative duration")
        results.append({"start":start,"end":end,"text":body,"speaker":"unverified"})
    if not results:raise ValueError("no timed cues")
    return results


def import_captions(episode_id,source,destination,permission_basis):
    registry=json.loads(INDEX.read_text(encoding="utf-8"))
    episode=next((e for e in registry["episodes"] if e["id"]==episode_id),None)
    if episode is None:raise ValueError("unknown episode")
    if not permission_basis.strip():raise ValueError("permission basis required")
    raw=Path(source).read_bytes()
    segments=parse_captions(raw.decode("utf-8-sig"))
    out=Path(destination)/episode_id
    out.mkdir(parents=True,exist_ok=True)
    provenance={"schema":"mathcan.toe.local.v1","episode_id":episode_id,
                "source_url":episode["transcript_url"],"rights_basis":permission_basis,
                "sha256":hashlib.sha256(raw).hexdigest(),"cues":len(segments),
                "quality":"machine transcription / speaker labels unverified"}
    (out/"provenance.json").write_text(json.dumps(provenance,indent=2)+"\n",encoding="utf-8")
    (out/"segments.jsonl").write_text("".join(json.dumps(s,ensure_ascii=False)+"\n" for s in segments),encoding="utf-8")
    return provenance


def main(argv=None):
    parser=argparse.ArgumentParser(description="TOE local caption intake")
    parser.add_argument("--list",action="store_true")
    parser.add_argument("--episode-id")
    parser.add_argument("--input",type=Path)
    parser.add_argument("--permission-basis")
    parser.add_argument("--output-dir",type=Path,default=Path(__file__).parent/"private")
    args=parser.parse_args(argv)
    if args.list:
        print(json.dumps(json.loads(INDEX.read_text())["episodes"],indent=2));return
    if not args.episode_id or not args.input or not args.permission_basis:
        parser.error("episode-id, input, and permission-basis required")
    print(json.dumps(import_captions(args.episode_id,args.input,args.output_dir,args.permission_basis),indent=2))


if __name__=="__main__":main()
