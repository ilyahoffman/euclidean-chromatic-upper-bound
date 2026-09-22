#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p verification
rm -f verification/LAST_VERIFIED.json
python3 scripts/check_environment.py | tee verification/environment.log
lake env lean --version | tee verification/lean-version.txt
python3 scripts/audit.py prepare
python3 - <<'PY'
from pathlib import Path
import shutil
build = Path('.lake/build')
if build.exists():
    shutil.rmtree(build)
PY
lake build 2>&1 | tee verification/build.log
python3 scripts/recheck_sources.py 2>&1 | tee verification/source-recheck.log
lake env lean AxiomAudit.lean 2>&1 | tee verification/axioms.log
python3 scripts/audit.py check | tee verification/audit-result.txt
lake env lean CompiledAudit.lean 2>&1 | tee verification/compiled-audit.log
python3 scripts/record_verification.py
