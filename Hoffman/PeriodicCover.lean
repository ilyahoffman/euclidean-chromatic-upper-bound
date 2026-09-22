import Hoffman.Net
import Hoffman.ProbabilityCover

namespace Hoffman

open Set Metric MeasureTheory MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E]

theorem openNeighborhood_periodic {A : Set E} {t : E}
    (hA : ∀ x, x + t ∈ A ↔ x ∈ A) (ρ : ℝ) (x : E) :
    x + t ∈ openNeighborhood A ρ ↔ x ∈ openNeighborhood A ρ := by
  simp only [openNeighborhood, Set.mem_iUnion, Metric.mem_ball]
  constructor
  · rintro ⟨a, ha, hd⟩
    refine ⟨a - t, ?_, ?_⟩
    · exact (hA (a - t)).mp (by simpa using ha)
    · have he : dist x (a - t) = dist (x + t) a := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [he]
      exact hd
  · rintro ⟨a, ha, hd⟩
    exact ⟨a + t, (hA a).mpr ha, by simpa using hd⟩

theorem periodic_borel_coloring_of_robust_cover
    [MeasurableSpace E] [BorelSpace E]
    (A : ℕ → Set E) (P : Set E) {η ρ : ℝ} {k : ℕ}
    (hA : ∀ n, AvoidsGap (A n) η) (hρη : 2 * ρ < η)
    (hcover : ∀ x, ∃ n < k, x ∈ openNeighborhood (A n) ρ)
    (hper : ∀ n t, t ∈ P → ∀ x, x + t ∈ A n ↔ x ∈ A n) :
    ∃ c : E → Fin k, Measurable c ∧
      (∀ x y, dist x y = 1 → c x ≠ c y) ∧
      ∀ t ∈ P, ∀ x, c (x + t) = c x := by
  classical
  let S := fun n => openNeighborhood (A n) ρ
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨n, _, hn⟩ := hcover x
    exact ⟨n, hn⟩
  let c : E → Fin k := fun x => ⟨firstColor S hS x, firstColor_lt S hS hcover x⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · apply measurable_to_countable'
    intro j
    have heq : c ⁻¹' {j} = firstColor S hS ⁻¹' {j.val} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
      rfl
    rw [heq]
    exact (measurable_firstColor S hS fun n =>
      (isOpen_openNeighborhood (A n) ρ).measurableSet) (measurableSet_singleton _)
  · intro x y hxy heq
    have hi : firstColor S hS x = firstColor S hS y := congrArg Fin.val heq
    have hx := firstColor_mem S hS x
    have hy := firstColor_mem S hS y
    rw [← hi] at hy
    exact neighborhood_unit_distance_free (hA _) hρη hx hy hxy
  · intro t ht x
    apply Fin.ext
    exact firstColor_invariant S hS (fun x => x + t)
      (fun n x => openNeighborhood_periodic (hper n t ht) ρ x) x

/-- The quantitative coloring lemma, formulated for a quotient map and a
finite net with global lifts. Every probabilistic and Borel-coloring step
is proved here; construction of the dense set and the net are inputs. -/
theorem quotient_net_coloring [MeasurableSpace E] [BorelSpace E]
    {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (π : E →+ G) (hπ : Function.Surjective π)
    (μ : Measure G) [IsProbabilityMeasure μ]
    [IsAddLeftInvariant μ] [IsNegInvariant μ]
    (P : Set E) (hP : ∀ t ∈ P, π t = 0)
    {m : ℕ} (hm : 0 < m) (z : Fin m → G)
    {η ρ : ℝ} (hρη : 2 * ρ < η)
    (hnet : ∀ x : E, ∃ j y, π y = z j ∧ dist x y < ρ)
    (A : Set G) (hA : MeasurableSet A)
    (hgap : AvoidsGap (π ⁻¹' A) η)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmass : μ A = ENNReal.ofReal δ) :
    ∃ c : E → Fin ⌈(1 + Real.log m) / δ⌉₊, Measurable c ∧
      (∀ x y, dist x y = 1 → c x ≠ c y) ∧
      ∀ t ∈ P, ∀ x, c (x + t) = c x := by
  classical
  let k : ℕ := ⌈(1 + Real.log m) / δ⌉₊
  obtain ⟨shift, hshift⟩ := exists_translates_cover_finite μ hm z A hA hδ hδ1 hmass
  let lift : Fin k → E := fun i => Classical.choose (hπ (shift i))
  have hlift (i : Fin k) : π (lift i) = shift i := Classical.choose_spec (hπ (shift i))
  let S : ℕ → Set E := fun n => if hn : n < k then
    {x | π (x - lift ⟨n, hn⟩) ∈ A} else ∅
  apply periodic_borel_coloring_of_robust_cover S P ?_ hρη ?_ ?_
  · intro n
    by_cases hn : n < k
    · intro x y hx hy hxy
      apply hgap (x := x - lift ⟨n, hn⟩) (y := y - lift ⟨n, hn⟩)
      · simpa [S, hn] using hx
      · simpa [S, hn] using hy
      · simpa using hxy
    · intro x y hx
      simp [S, hn] at hx
  · intro x
    obtain ⟨j, y, hy, hxy⟩ := hnet x
    obtain ⟨i, hi⟩ := hshift j
    refine ⟨i.val, i.isLt, ?_⟩
    simp only [openNeighborhood, Set.mem_iUnion, Metric.mem_ball]
    refine ⟨y, ?_, hxy⟩
    have hik : (i : ℕ) < k := i.isLt
    simpa [S, hik, map_sub, hlift, hy] using hi
  · intro n t ht x
    by_cases hn : n < k
    · simp [S, hn, map_sub, map_add, hP t ht]
    · simp [S, hn]

end Hoffman
