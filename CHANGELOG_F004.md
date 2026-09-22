# F004: reproduction audit of F003

21 September 2026.

The original mathematical proof and upper bound are preserved. All 21 original
Lean modules have identical code after comments are removed; 20 files are
byte-identical. The only changed original proof-source file is
`Hoffman/CoveringEstimate.lean`, where an obsolete progress comment is corrected.
The original R006 publication ZIP is unchanged.

## Corrections and additions

1. **Bootstrap correction.** Replace `lake exe cache get Hoffman` with
   `python3 scripts/fetch_cache.py`. Mathlib 4.19's cache traverses only recognized
   upstream import prefixes; it does not follow the `Hoffman.*` imports in the
   root module. The helper passes the 28 actual Mathlib imports explicitly.
2. **Version and dependency checks.** Verify the active Lean release/commit,
   each of the nine locked dependency revisions, clean dependency source trees
   and absence of inherited Lean search-path overrides. Clean the project build
   before compiling and clear the old successful-run marker before verification.
   Force a separate Lean invocation for every project source in dependency order,
   so source rechecking does not depend on incremental-build traces.
3. **Complete compiled inventory.** Retain the human-readable named-theorem
   axiom reports and add `CompiledAudit.lean`, which inventories declarations by
   owning module. Check logical declarations, theorem-valued instances and
   generated proof declarations; directly recheck the theorem proof terms using
   Lean's kernel. List compiler runtime auxiliaries separately.
4. **Explicit semantics.** Add two proved consequences in `Hoffman/Semantics.lean`:
   coordinate unit distance, Borel color fibers, positive finite color count and
   all integer lattice periods; and exact identification of the finite ordinary
   chromatic value with the minimum number of colors.
5. **Audit controls and evidence.** Extend source scanning to the root import
   file and nested modules. Add negative controls for proof holes, axioms,
   unsafe source declarations, a kernel-check bypass option, missing reports
   and a deliberately contaminated compiled module. Record current source hashes
   and the verified environment after a complete successful run.
6. **PDF portability and precision.** Pin the three optional PDF dependencies
   and use matplotlib's bundled fonts. Correct the bootstrap commands,
   distinguish a finite product probability space from a finite sample space,
   explicitly state positivity of the local ball radius, describe the graph API
   accurately, and typeset the period-basis subscripts. The note remains six
   pages with 26 vector equations.

## Scope

F004 proves the same principal Theorem 1 and chromatic-root limsup as F003,
with explicit constant `40 * Real.exp 1 + 1` and explicit finite count `K_d`.
It does not extend the complete formalization to the paper's sharper moment
formulas, finite prefactors or optimal-density appendix. See the audit report
for the exact reproduction level and the recorded checks.
