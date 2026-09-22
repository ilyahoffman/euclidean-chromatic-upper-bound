import Hoffman
import Lean.Util.CollectAxioms

/-!
Inventory the compiled environment by the owning module, rather than by a
source-text theorem regex. This includes definitions, instances, generated
declarations, lemmas and theorems, even outside the Hoffman namespace.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let required : Array Name := #[
    ``Hoffman.main_upper_bound, ``Hoffman.main_upper_bound_explicit,
    ``Hoffman.finite_upper_bound, ``Hoffman.colorBound_eq_explicit,
    ``Hoffman.ordinary_chromaticNumber_finite, ``Hoffman.chromatic_root_limsup,
    ``Hoffman.unitDistanceGraph_adj_iff_coordinates,
    ``Hoffman.main_upper_bound_coordinates, ``Hoffman.ordinary_chromatic_value_exact]
  let owned := fun n => match env.getModuleIdxFor? n with
    | some i => (`Hoffman).isPrefixOf env.header.moduleNames[i]!
    | none => false
  let names := (env.constants.fold (fun ns n _ =>
    if owned n then ns.push n else ns) (#[] : Array Name)).qsort Name.quickLt
  if names.isEmpty then throwError "Empty compiled project inventory"
  for n in required do
    if !names.contains n then throwError "Missing required declaration: {n}"
  let mut theoremCount := 0
  let mut runtimeCount := 0
  for n in names do
    let some info := env.find? n | throwError "Missing declaration: {n}"
    if info.isUnsafe then
      runtimeCount := runtimeCount + 1
      logInfo m!"RUNTIME auxiliary (excluded from logical inventory): {n}"
      continue
    if info matches .axiomInfo _ then throwError "Project axiom: {n}"
    if let .thmInfo thm := info then
      theoremCount := theoremCount + 1
      match Kernel.check env {} thm.value with
      | .error _ => throwError "Kernel recheck failed for proof term: {n}"
      | .ok type =>
        match Kernel.isDefEq env {} type thm.type with
        | .ok true => pure ()
        | _ => throwError "Kernel recheck found the wrong proof type: {n}"
    let axioms ← collectAxioms n
    for a in axioms do
      if !allowed.contains a then throwError "Unexpected axiom {a} in {n}"
    let kind := if info.isTheorem then "theorem" else "declaration"
    logInfo m!"AUDIT {kind} {n}: {axioms}"
  logInfo m!"COMPILED AUDIT PASS: {names.size - runtimeCount} logical declarations; {theoremCount} theorem declarations kernel-rechecked; {runtimeCount} runtime auxiliaries."
