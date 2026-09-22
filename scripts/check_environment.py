#!/usr/bin/env python3
"""Check the compiler, dependency revisions, source cleanliness, and search paths."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()


def fail(message):
    raise SystemExit("ENVIRONMENT CHECK FAILED: " + message)


for command in ("lake", "git"):
    if not shutil.which(command):
        fail(f"{command} is not on PATH; install Lean/elan and Git first")
for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
    if os.environ.get(key):
        fail(f"unset inherited {key} before verification; Lake must select the project imports")
toolchain = (ROOT / "lean-toolchain").read_text().strip()
if toolchain != "leanprover/lean4:v4.19.0":
    fail("unexpected lean-toolchain")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
packages = []
for package in manifest["packages"]:
    path = ROOT / manifest["packagesDir"] / package["name"]
    if not path.is_dir():
        fail(f"missing dependency {package['name']}; first run python3 scripts/fetch_cache.py")
    head = run("git", "rev-parse", "HEAD", cwd=path)
    if head != package["rev"]:
        fail(f"revision mismatch for {package['name']}: {head}")
    status = run("git", "status", "--porcelain", "--untracked-files=all", cwd=path)
    if status:
        fail(f"modified or untracked dependency source in {package['name']}: {status}")
    packages.append({"name": package["name"], "revision": head, "clean": True})
version = run("lake", "env", "lean", "--version")
if "version 4.19.0," not in version or "commit 6caaee842e94," not in version:
    fail("the active Lean binary does not match 4.19.0 / 6caaee842e94: " + version)
if json.loads((ROOT / "lake-manifest.json").read_text()) != manifest:
    fail("Lake changed the dependency lockfile; check lakefile.toml against the release")
result = {
    "lean_toolchain": toolchain,
    "lean_version": version,
    "python_version": sys.version.split()[0],
    "dependency_lock_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
    "packages": packages,
}
(ROOT / "verification").mkdir(exist_ok=True)
(ROOT / "verification/environment.json").write_text(json.dumps(result, indent=2) + "\n")
print(version)
print(f"PASS: {len(packages)} locked dependency revisions and clean source trees.")
