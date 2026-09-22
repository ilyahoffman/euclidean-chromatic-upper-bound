import Hoffman.Chromatic

/-!
# Audit-facing statements without the project-specific coloring predicates

These consequences make the coordinate metric, Borel fibers, positive finite
color count, integer lattice periods, and finite chromatic value explicit.
They do not change the proof or the bound established in F003.
-/

namespace Hoffman

open scoped BigOperators

theorem main_upper_bound_coordinates (d : ℕ) (hd : 2 ≤ d) :
    ∃ k : ℕ, 0 < k ∧
      (k : ℝ) ≤ (40 * Real.exp 1 + 1) * d * Real.log d * (3 * Real.sqrt 3 / 2) ^ d ∧
      ∃ c : EuclideanSpace ℝ (Fin d) → Fin k,
        (∀ i, @MeasurableSet (EuclideanSpace ℝ (Fin d))
          (borel (EuclideanSpace ℝ (Fin d))) {x | c x = i}) ∧
        (∀ x y, (∑ i, (x i - y i) ^ 2) = 1 → c x ≠ c y) ∧
        ∃ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
          ∀ z : Fin d → ℤ, ∀ x, c (x + ∑ j, z j • b j) = c x := by
  classical
  obtain ⟨k, hk, c, hc, hp, b, hb⟩ := main_upper_bound_explicit d hd
  have hk0 : 0 < k := (Nat.zero_le (c 0).val).trans_lt (c 0).isLt
  refine ⟨k, hk0, hk, c, ?_, ?_, b, ?_⟩
  · intro i
    exact hc (measurableSet_singleton i)
  · intro x y hxy
    exact hp x y ((unitDistanceGraph_adj_iff_coordinates d x y).mpr hxy)
  · intro z
    have hperiod : ∀ s : Finset (Fin d), Function.Periodic c (∑ j ∈ s, z j • b j) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [Function.Periodic]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact ((show Function.Periodic c (b j) from fun x => hb x j).zsmul (z j)).add_period ih
    exact hperiod Finset.univ

theorem ordinary_chromatic_value_exact {d : ℕ} (hd : 2 ≤ d) :
    ∃ n : ℕ, euclideanChromaticNumber d = (n : ℕ∞) ∧
      chromaticReal d = (n : ℝ) ∧
      (unitDistanceGraph d).Colorable n ∧
      ∀ m : ℕ, (unitDistanceGraph d).Colorable m → n ≤ m := by
  let n := (euclideanChromaticNumber d).toNat
  have he : (n : ℕ∞) = euclideanChromaticNumber d :=
    ENat.coe_toNat (ordinary_chromaticNumber_finite hd)
  refine ⟨n, he.symm, rfl, ?_, ?_⟩
  · exact SimpleGraph.chromaticNumber_le_iff_colorable.mp he.ge
  · intro m hm
    exact ENat.toNat_le_of_le_coe hm.chromaticNumber_le

end Hoffman
