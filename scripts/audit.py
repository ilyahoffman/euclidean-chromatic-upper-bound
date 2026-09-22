#!/usr/bin/env python3
"""Audit project proof holes and inspect Lean's own transitive axiom reports."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def without_comments(text):
    # Lean comments can nest. Preserve newlines for declaration scanning.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise SystemExit("Unclosed Lean comment")
    return "".join(out)


def theorems():
    names = []
    for path in [ROOT / "Hoffman.lean", *sorted((ROOT / "Hoffman").rglob("*.lean"))]:
        code = without_comments(path.read_text())
        bad = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|elab|run_elab|run_cmd|initialize|syntax|macro_rules)\b|debug\.skipKernelTC", code)
        if bad:
            raise SystemExit(f"Forbidden token {bad[0]!r} in {path.name}")
        names += ["Hoffman." + n for n in re.findall(r"^\s*(?:theorem|lemma)\s+(\w+)", code, re.M)]
    if not names or len(names) != len(set(names)):
        raise SystemExit("Empty or duplicate theorem inventory")
    return names


names = theorems()
REQUIRED = {
    "Hoffman.main_upper_bound", "Hoffman.main_upper_bound_explicit",
    "Hoffman.finite_upper_bound", "Hoffman.colorBound_eq_explicit",
    "Hoffman.ordinary_chromaticNumber_finite", "Hoffman.chromatic_root_limsup",
    "Hoffman.unitDistanceGraph_adj_iff_coordinates",
}
if not REQUIRED.issubset(names):
    raise SystemExit(f"Missing required main-result declarations: {REQUIRED - set(names)}")
if sys.argv[1:] == ["prepare"]:
    (ROOT / "AxiomAudit.lean").write_text(
        "import Hoffman\n\n" + "\n".join("#print axioms " + n for n in names) + "\n"
    )
    print(f"Prepared transitive axiom audit for {len(names)} theorems.")
elif sys.argv[1:] == ["check"]:
    log = (ROOT / "verification/axioms.log").read_text()
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log))
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        reports[name] = ""
    for name in names:
        if name not in reports:
            raise SystemExit(f"Missing compiler axiom report: {name}")
        used = {x.strip() for x in reports[name].split(",") if x.strip()}
        if used - ALLOWED:
            raise SystemExit(f"Unexpected axioms for {name}: {used - ALLOWED}")
    print(f"PASS: {len(names)} theorem axiom reports checked.")
    print("No proof holes, custom axioms, unsafe source declarations or native_decide in project proof sources.")
    print("Only standard Lean foundations permitted: propext, Classical.choice, Quot.sound.")
    print("PASS: legacy named-theorem reports; CompiledAudit.lean supplies the complete compiled inventory.")
else:
    raise SystemExit("Usage: audit.py prepare|check")
