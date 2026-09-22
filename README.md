# Hoffman R006: complete Lean proof of the main upper bound

**F004, 21 September 2026. Audited reproduction of the complete main proof.**

F004 repairs the cache/bootstrap instruction, expands the audit to compiled logical declarations, adds explicit semantic checks, and makes the PDF fonts portable. The F003 mathematical proof and its upper bound are unchanged; one stale source comment is corrected. See `AUDIT_REPORT_RU.md` and `CHANGELOG_F004.md`.

For every integer `d ≥ 2`, this project proves existence of a periodic Borel coloring of real Euclidean space with no monochromatic unit-distance pair and at most

\[
(40e+1)\,d\log d\,(3\sqrt3/2)^d
\]

colors. It also proves the stated upper bound on the limit superior of the d-th roots of the ordinary chromatic number, using mathlib's `SimpleGraph.chromaticNumber`.

## Start here

- `Hoffman/Main.lean`: `main_upper_bound_explicit` and `main_upper_bound : MainUpperBound`.
- `Hoffman/Chromatic.lean`: `ordinary_chromaticNumber_le`, finiteness, and `chromatic_root_limsup`.
- `Hoffman/FiniteUpperBound.lean`: a complete quantitative periodic Borel coloring theorem.
- `Hoffman/AsymptoticEstimate.lean`: explicit parameters, an explicit finite color count, and its bound.
- `docs/HOFFMAN_R006_LEAN_PROOF_NOTE.pdf`: the full mathematical argument and formalization map.
- `BLUEPRINT.md`: dependency map and precise scope relative to R006.

The finite color count is

\[
K_d=\left\lceil4\bigl(1+d\log(64d^2+1)\bigr)
\left[\frac{3\sqrt3}{2}\left(1+\frac1d\right)\right]^d\right\rceil.
\]

`colorBound_eq_explicit` proves this exact expression. `colorBound_periodic_borel` constructs a coloring with this count; `colorBound_le` proves the bound above.

## Relation to R006

This is a separate Lean companion. The supplied R006 publication archive, the article, and its AI disclosure remain unchanged. The full main upper-bound theorem is proved by a shorter route: the exclusion region lies inside a translated ball of radius `(3√3/2)h`, and a finite independent-center calculation replaces the Poisson expected-density calculation. No mathematical assertion from R006 is assumed as an axiom.

The exact spherical-moment formulas, the sharper printed finite prefactors, and the optimal-density/leading-constant results of the appendix are **not all formalized**. They are not assumptions of the completed main proof. F004 establishes the full principal upper bound and its limsup consequence, not a line-by-line verification of every assertion in the paper.

## Reproduce the checks

Requirements: Lean/elan, Git, Python 3.10 or later, Bash, curl, tar, and network access for the first dependency setup. The proof-note Python packages are optional and are **not** needed to verify Lean.

Pinned versions:

- Lean **4.19.0**, commit `6caaee842e94`.
- mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**.
- All transitive dependency revisions are pinned in `lake-manifest.json`.

Extract the ZIP into a new directory and run these commands from the directory containing `lakefile.toml`:

```sh
python3 scripts/fetch_cache.py
bash verify.sh
```

The cache helper passes the actual direct **Mathlib** imports to the pinned cache utility. The old F003 command `lake exe cache get Hoffman` does not traverse downstream `Hoffman.*` imports in mathlib 4.19 and therefore does not fetch their dependencies. Do not use it for bootstrap.

The verifier checks the active compiler and all nine dependency revisions, rejects modified dependency source trees and inherited Lean search-path overrides, removes only this project's `.lake/build`, and builds the project. It then forces Lean to re-elaborate every project source in dependency order, overwriting the project oleans independently of Lake’s up-to-date traces. Finally it checks the named-theorem axiom reports and inventories the compiled declarations by their owning modules. `CompiledAudit.lean` checks all logical declarations for additional axioms and directly rechecks the theorem proof terms with Lean's kernel. Compiler-generated unsafe runtime auxiliaries are reported separately; no `unsafe` declarations are permitted in the proof sources, and safe proofs cannot use unsafe runtime definitions. Only `propext`, `Classical.choice` and `Quot.sound` are permitted as logical axioms.

The original 114 named theorems and the two audit-facing semantic theorems are checked. Generated theorem declarations and theorem-valued instances are also included in the compiled inventory. `Hoffman/Semantics.lean` states the coordinate distance condition, Borel color fibers and all integer combinations of a period basis explicitly, and proves that the real chromatic value is the finite minimum number of colors.

Optional auditor controls: run `python3 scripts/test_audit_guards.py` after verification. The deliberately contaminated temporary module is expected to be rejected; the error in `verification/negative-control-compiled.log` records that successful negative control, not a project build failure.

`verification/LAST_VERIFIED.json` is written only after successful completion of the full verifier and records the source hashes and environment. Verification rewrites the logs. The release manifest is for checking the distributed archive **before** running the verifier:

```sh
sha256sum -c MANIFEST.sha256
```

The release includes build and audit logs. Logs record a run; they do not replace rebuilding the proof. Dependencies, compiler binaries and caches are not bundled. The existence proof is noncomputable and does not supply an efficient executable coloring algorithm. No full rebuild of Lean and mathlib from their source is claimed.

On Windows use WSL with the commands above. Linux was tested in this audit; macOS and Windows/WSL were not independently tested.

## Regenerate the explanatory PDF (optional)

```sh
python3 -m venv .venv-note
.venv-note/bin/python -m pip install -r requirements-proof-note.txt
.venv-note/bin/python scripts/build_proof_note.py
```

The generator uses DejaVu fonts bundled with the pinned matplotlib version, rather than an operating-system font path. The tested environment was Python 3.12.14 with reportlab 4.4.9, matplotlib 3.10.8 and pypdf 6.10.0. Repeated PDF generation was checked in that environment; byte-identical output on other operating systems or Python versions is not promised. The mathematical note is explanatory text; the Lean source is the machine-checked proof.

## Source and attribution

Mathematical source: Ilya Hoffman's `HOFFMAN_EUCLIDEAN_CHROMATIC_UPPER_BOUND_PUBLICATION_R006_20260914.zip`, included unchanged in `reference/`.

Original archive SHA-256:

`4f5520ad02c270b6bb2e40f095acc479c9c1ddd2ed121e27a1ca6c64ba651000`

The Lean companion, enclosing-ball route, verification tooling, and explanatory note were prepared with OpenAI Codex. The formal graph is connected explicitly to the coordinate condition `sum_i (x_i-y_i)^2 = 1` by `unitDistanceGraph_adj_iff_coordinates`.
