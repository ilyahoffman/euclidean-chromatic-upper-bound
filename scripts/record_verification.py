#!/usr/bin/env python3
"""Tie a successful complete verification run to the current source bytes."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
log = (ROOT / 'verification/compiled-audit.log').read_text()
matches = re.findall(r'COMPILED AUDIT PASS: (\d+) logical declarations; (\d+) theorem declarations kernel-rechecked; (\d+) runtime auxiliaries\.', log)
if len(matches) != 1:
    raise SystemExit('Missing or duplicate compiled-audit completion marker')
source_log = (ROOT / 'verification/source-recheck.log').read_text()
expected_modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts)
                    for p in [ROOT / 'Hoffman.lean', *sorted((ROOT / 'Hoffman').rglob('*.lean'))]}
checked_modules = re.findall(r'^SOURCE RECHECK PASS: ([\w.]+)$', source_log, re.M)
if len(checked_modules) != len(expected_modules) or set(checked_modules) != expected_modules:
    raise SystemExit('Incomplete forced source recheck')
source_files = [ROOT / 'Hoffman.lean', *sorted((ROOT / 'Hoffman').rglob('*.lean')),
                ROOT / 'CompiledAudit.lean', ROOT / 'AxiomAudit.lean', ROOT / 'verify.sh',
                *sorted((ROOT / 'scripts').glob('*.py')), ROOT / 'lean-toolchain', ROOT / 'lakefile.toml', ROOT / 'lake-manifest.json']
result = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'passed',
    'clean_project_build': True,
    'forced_source_modules': checked_modules,
    'logical_declarations': int(matches[0][0]),
    'kernel_rechecked_theorem_declarations': int(matches[0][1]),
    'compiler_runtime_auxiliaries': int(matches[0][2]),
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'environment': json.loads((ROOT / 'verification/environment.json').read_text()),
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files},
}
(ROOT / 'verification/LAST_VERIFIED.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS: complete run recorded with source hashes in verification/LAST_VERIFIED.json')
