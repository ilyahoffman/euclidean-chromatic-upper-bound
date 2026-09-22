#!/usr/bin/env python3
"""Force Lean to check every project source, independently of Lake's up-to-date traces."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
sources = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p
           for p in [ROOT / 'Hoffman.lean', *sorted((ROOT / 'Hoffman').rglob('*.lean'))]}
ordered, visiting, done = [], set(), set()


def visit(name):
    if name in done:
        return
    if name in visiting:
        raise SystemExit('Cyclic project import: ' + name)
    visiting.add(name)
    for dep in re.findall(r'^import\s+(Hoffman(?:\.[\w]+)*)\s*$', sources[name].read_text(), re.M):
        if dep not in sources:
            raise SystemExit('Missing project import: ' + dep)
        visit(dep)
    visiting.remove(name)
    done.add(name)
    ordered.append(name)


for name in sorted(sources):
    visit(name)
for name in ordered:
    relative = sources[name].relative_to(ROOT)
    output = ROOT / '.lake/build/lib/lean' / relative.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(['lake', 'env', 'lean', str(relative), '-R', str(ROOT), '-o', str(output)],
                   cwd=ROOT, check=True)
    print('SOURCE RECHECK PASS:', name, flush=True)
print(f'ALL SOURCE RECHECKS PASSED: {len(ordered)} modules, including the root import.', flush=True)
