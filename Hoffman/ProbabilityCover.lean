import Hoffman.CoveringEstimate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure

/-!
# Existence of a finite covering realization

The probability space is constructed as a finite product. Independence and
the union bound are proved using the product measure, not assumed as an
unproved covering hypothesis.
-/

namespace Hoffman

open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

theorem exists_samples_hitting_sets {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (B : Fin m → Set Ω) (hB : ∀ j, MeasurableSet (B j))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmass : ∀ j, ENNReal.ofReal δ ≤ μ (B j)) :
    ∃ sample : Fin ⌈(1 + Real.log m) / δ⌉₊ → Ω,
      ∀ j, ∃ i, sample i ∈ B j := by
  classical
  let k : ℕ := ⌈(1 + Real.log m) / δ⌉₊
  let ν : Measure (Fin k → Ω) := Measure.pi (fun _ => μ)
  let bad : Fin m → Set (Fin k → Ω) :=
    fun j => Set.pi Set.univ (fun _ => (B j)ᶜ)
  have hbad : ∀ j, ν (bad j) ≤ ENNReal.ofReal ((1 - δ) ^ k) := by
    intro j
    change Measure.pi (fun _ : Fin k => μ) (Set.pi Set.univ (fun _ => (B j)ᶜ)) ≤ _
    have hc : μ (B j)ᶜ ≤ ENNReal.ofReal (1 - δ) := by
      rw [measure_compl (hB j) (measure_ne_top μ (B j)), measure_univ,
        ENNReal.ofReal_sub 1 hδ.le, ENNReal.ofReal_one]
      exact tsub_le_tsub_left (hmass j) 1
    rw [Measure.pi_pi]
    calc
      (∏ _ : Fin k, μ (B j)ᶜ) ≤ ∏ _ : Fin k, ENNReal.ofReal (1 - δ) :=
        Finset.prod_le_prod' (fun _ _ => hc)
      _ = _ := by simp [← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 - δ)]
  have hsum : (∑ j : Fin m, ν (bad j)) ≤ ENNReal.ofReal ((m : ℝ) * (1 - δ) ^ k) := by
    calc
      _ ≤ ∑ _ : Fin m, ENNReal.ofReal ((1 - δ) ^ k) := Finset.sum_le_sum (fun j _ => hbad j)
      _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  have hfail : ν (⋃ j, bad j) < 1 := by
    apply lt_of_le_of_lt ((measure_iUnion_fintype_le ν bad).trans hsum)
    rw [ENNReal.ofReal_lt_one]
    exact covering_failure_lt_one (by exact_mod_cast hm) hδ hδ1
  have hex : (⋃ j, bad j)ᶜ.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    have hh := measure_univ_le_add_compl (μ := ν) (⋃ j, bad j)
    rw [measure_univ, he, measure_empty, add_zero] at hh
    exact (not_le_of_gt hfail) hh
  obtain ⟨sample, hs⟩ := hex
  refine ⟨sample, ?_⟩
  intro j
  have hj : sample ∉ bad j := fun h => hs (Set.mem_iUnion.mpr ⟨j, h⟩)
  simpa [bad] using hj

/-- A measurable positive-density set in an invariant probability group
has enough translates to cover any given finite list of points. -/
theorem exists_translates_cover_finite {G : Type*} [MeasurableSpace G]
    [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    [IsAddLeftInvariant μ] [IsNegInvariant μ]
    {m : ℕ} (hm : 0 < m) (z : Fin m → G)
    (A : Set G) (hA : MeasurableSet A) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : μ A = ENNReal.ofReal δ) :
    ∃ shift : Fin ⌈(1 + Real.log m) / δ⌉₊ → G,
      ∀ j, ∃ i, z j - shift i ∈ A := by
  let B : Fin m → Set G := fun j => (fun t => z j - t) ⁻¹' A
  apply exists_samples_hitting_sets μ hm B
  · intro j
    exact hA.preimage (measurable_const.sub measurable_id)
  · exact hδ
  · exact hδ1
  · intro j
    exact (((measurePreserving_sub_left μ (z j)).measure_preimage hA.nullMeasurableSet).trans hmass).ge

end Hoffman
