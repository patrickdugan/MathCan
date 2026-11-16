from pathlib import Path
import hashlib,json,re
W=Path(__file__).resolve().parent;R=W/'replay432/Synthesis';mods=json.loads((R/'manifest.json').read_text(encoding='utf-8'))['sources']
for m,rel in mods.items():
 p=W/'MathCan'/rel;s=p.read_text(encoding='utf-8');assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',s);assert all(x==x.rstrip() for x in s.splitlines())
print('All seven formal source files are admission-free and whitespace-clean.')
