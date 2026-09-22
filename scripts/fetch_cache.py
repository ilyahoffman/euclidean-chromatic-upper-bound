#!/usr/bin/env python3
"""Fetch the pinned upstream imports; mathlib 4.19 does not traverse Hoffman imports."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
modules = sorted({
    name
    for path in (ROOT / "Hoffman").rglob("*.lean")
    for name in re.findall(r"^import\s+(Mathlib\.[\w.]+)\s*$", path.read_text(), re.M)
})
if not modules:
    raise SystemExit("No direct mathlib imports found; refusing an empty cache request")
print(f"Fetching {len(modules)} direct mathlib imports and their transitive dependencies.", flush=True)
raise SystemExit(subprocess.call(["lake", "exe", "cache", "get", *modules], cwd=ROOT))
