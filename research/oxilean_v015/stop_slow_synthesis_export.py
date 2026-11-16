from pathlib import Path
from datetime import datetime, timezone
import json
import os
import signal

assert os.name == 'posix'
W = Path(__file__).resolve().parent
R = W/'replay432/Synthesis'
binary = W/'replay432/lean4export-source/.lake/build/bin/lean4export'
original_output = R/'Lemmas.ndjson'
roots = json.loads((R/'manifest.json').read_text())['theorems']
stopped = []
for entry in Path('/proc').iterdir():
    if not entry.name.isdigit():
        continue
    try:
        args = entry.joinpath('cmdline').read_bytes().split(b'\0')
        if len(args) < 3 or args[0].decode() != str(binary):
            continue
        if args[1] != b'ApproximationMathlib.MultivariateCapture':
            continue
        if entry.joinpath('fd/1').resolve() != original_output:
            continue
        assert set(value.decode() for value in args[3:] if value) == set(roots)
        os.kill(int(entry.name), signal.SIGTERM)
        stopped.append(int(entry.name))
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        continue
result = {'status': 'interrupted_export_not_counted', 'pids': stopped,
          'time_utc': datetime.now(timezone.utc).isoformat(),
          'reason': 'Replaced slow Windows-mounted output with Linux-local candidate output',
          'partial_file': str(original_output),
          'partial_bytes': original_output.stat().st_size if original_output.exists() else 0,
          'verification_result': None}
(R/'slow_export_interruption.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2), flush=True)
