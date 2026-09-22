#!/usr/bin/env python3
"""Negative controls for the audit (temporary copies only; run after verify.sh)."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
results = []


def check(label, process, expected_success, needle=None):
    ok = (process.returncode == 0) == expected_success
    if needle is not None:
        ok = ok and needle in process.stdout
    if not ok:
        raise RuntimeError(f"{label}: unexpected result ({process.returncode})\n{process.stdout}")
    results.append({'test': label, 'passed': True, 'exit_code': process.returncode})
    print('PASS:', label, flush=True)


def execute(args, cwd, env=None):
    return subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT)


with tempfile.TemporaryDirectory(prefix='hoffman-audit-controls-') as td:
    tmp = Path(td)
    shutil.copytree(ROOT / 'Hoffman', tmp / 'Hoffman')
    shutil.copy2(ROOT / 'Hoffman.lean', tmp / 'Hoffman.lean')
    (tmp / 'scripts').mkdir()
    shutil.copy2(ROOT / 'scripts/audit.py', tmp / 'scripts/audit.py')
    (tmp / 'verification').mkdir()
    log_path = tmp / 'verification/axioms.log'
    log = (ROOT / 'verification/axioms.log').read_text()
    log_path.write_text(log)
    command = [sys.executable, 'scripts/audit.py']
    check('unmodified source inventory', execute(command + ['prepare'], tmp), True)
    check('unmodified compiler axiom reports', execute(command + ['check'], tmp), True)
    root_source = (tmp / 'Hoffman.lean').read_text()
    for label, code, token in [
        ('proof hole in root import file', 'example : True := by sorry', 'sorry'),
        ('custom axiom in root import file', 'axiom control_axiom : True', 'axiom'),
        ('unsafe source declaration', 'unsafe def control_unsafe : Nat := 0', 'unsafe'),
        ('kernel-check bypass option', 'set_option debug.skipKernelTC true', 'debug.skipKernelTC'),
        ('native_decide proof shortcut', 'example : True := by native_decide', 'native_decide'),
    ]:
        (tmp / 'Hoffman.lean').write_text(root_source + '\n' + code + '\n')
        check(label, execute(command + ['prepare'], tmp), False, token)
    (tmp / 'Hoffman.lean').write_text(root_source)
    (tmp / 'Hoffman/Nested').mkdir()
    nested = tmp / 'Hoffman/Nested/Control.lean'
    nested.write_text('example : True := by sorry\n')
    check('proof hole in nested module', execute(command + ['prepare'], tmp), False, 'sorry')
    nested.unlink()
    (tmp / 'Hoffman.lean').write_text(root_source + '\n/- nested /- sorry -/ axiom -/\n')
    check('nested comments do not create false proof-hole reports', execute(command + ['prepare'], tmp), True)
    (tmp / 'Hoffman.lean').write_text(root_source)
    log_path.write_text(log.replace("'Hoffman.main_upper_bound'", "'Control.wrong_name'"))
    check('missing main theorem compiler report', execute(command + ['check'], tmp), False, 'Missing compiler axiom report')
    log_path.write_text(log.replace('[propext, Classical.choice, Quot.sound]', '[propext, Classical.choice, Quot.sound, control_axiom]', 1))
    check('unexpected transitive axiom in compiler report', execute(command + ['check'], tmp), False, 'Unexpected axioms')

    # Compile a new project-owned module containing a harmless True axiom.
    # The names deliberately lie outside namespace Hoffman: module ownership
    # must still include them in the compiled audit. No proof source is edited.
    leanpath = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    paths = [str((ROOT / p).resolve()) if not Path(p).is_absolute() else p for p in leanpath.split(os.pathsep)]
    lean = shutil.which('lean')
    if lean is None:
        raise RuntimeError('Lean must be on PATH')
    canary_root = tmp / 'canary'
    shutil.copytree(ROOT / '.lake/build/lib/lean/Hoffman', canary_root / 'Hoffman')
    shutil.copy2(ROOT / '.lake/build/lib/lean/Hoffman.olean', canary_root / 'Hoffman.olean')
    canary = canary_root / 'Hoffman/AuditCanary.lean'
    canary.write_text('import Hoffman\naxiom control_axiom_outside_namespace : True\n'
                      'lemma control_lemma_outside_namespace : True := control_axiom_outside_namespace\n')
    canary_env = {**os.environ, 'LEAN_PATH': os.pathsep.join([str(canary_root), *paths])}
    build = execute([lean, str(canary), '-R', str(canary_root), '-o', str(canary.with_suffix('.olean'))], ROOT, canary_env)
    check('compile the deliberately contaminated control module', build, True)
    auditor = canary_root / 'ControlAudit.lean'
    auditor.write_text((ROOT / 'CompiledAudit.lean').read_text().replace('import Hoffman\n', 'import Hoffman.AuditCanary\n', 1))
    audit = execute([lean, str(auditor), '-R', str(canary_root)], ROOT, canary_env)
    check('compiled inventory rejects an axiom outside namespace Hoffman', audit, False, 'control_axiom_outside_namespace')
    (ROOT / 'verification/negative-control-compiled.log').write_text(audit.stdout)

(ROOT / 'verification/negative-controls.json').write_text(json.dumps(results, indent=2) + '\n')
print(f'PASS: {len(results)} audit controls; all mutations stayed in temporary files.')
