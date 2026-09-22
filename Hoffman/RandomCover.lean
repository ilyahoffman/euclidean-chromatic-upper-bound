import Hoffman.PeriodicCover

namespace Hoffman

open Set Metric MeasureTheory

/-- Random sets need only cover a finite net with a uniform positive probability.
Their open neighborhoods produce a measurable periodic coloring. -/
theorem random_net_coloring
    {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Set E) (P : Set E) {η ρ : ℝ}
    (hgap : ∀ s, AvoidsGap (A s) η) (hρη : 2 * ρ < η)
    (hper : ∀ s t, t ∈ P → ∀ x, x + t ∈ A s ↔ x ∈ A s)
    {m : ℕ} (hm : 0 < m) (z : Fin m → E)
    (hnet : ∀ x : E, ∃ j t, t ∈ P ∧ dist x (z j + t) < ρ)
    (B : Fin m → Set Ω) (hB : ∀ j, MeasurableSet (B j))
    (hBA : ∀ j s, s ∈ B j → z j ∈ A s)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmass : ∀ j, ENNReal.ofReal δ ≤ μ (B j)) :
    ∃ c : E → Fin ⌈(1 + Real.log m) / δ⌉₊, Measurable c ∧
      (∀ x y, dist x y = 1 → c x ≠ c y) ∧
      ∀ t ∈ P, ∀ x, c (x + t) = c x := by
  classical
  let k : ℕ := ⌈(1 + Real.log m) / δ⌉₊
  obtain ⟨s, hs⟩ := exists_samples_hitting_sets μ hm B hB hδ hδ1 hmass
  let S : ℕ → Set E := fun n => if hn : n < k then A (s ⟨n, hn⟩) else ∅
  apply periodic_borel_coloring_of_robust_cover S P ?_ hρη ?_ ?_
  · intro n
    by_cases hn : n < k
    · simpa only [S, dif_pos hn] using hgap (s ⟨n, hn⟩)
    · intro x y hx
      simp [S, hn] at hx
  · intro x
    obtain ⟨j, t, ht, hd⟩ := hnet x
    obtain ⟨i, hi⟩ := hs j
    refine ⟨i.val, i.isLt, ?_⟩
    simp only [openNeighborhood, Set.mem_iUnion, Metric.mem_ball]
    refine ⟨z j + t, ?_, hd⟩
    have hik : (i : ℕ) < k := i.isLt
    simpa [S, hik] using (hper (s i) t ht (z j)).mpr (hBA j (s i) hi)
  · intro n t ht x
    by_cases hn : n < k
    · simpa [S, hn] using hper (s ⟨n, hn⟩) t ht x
    · simp [S, hn]

end Hoffman
