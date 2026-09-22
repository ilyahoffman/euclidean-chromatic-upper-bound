import Hoffman.ExclusionBall
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Exclusion-volume estimate without spherical integration -/

namespace Hoffman

open Set Metric MeasureTheory MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exclusionRegion_volume_le (μ : Measure E) [IsAddHaarMeasure μ]
    {h : ℝ} (hh : 0 < h) {p x : E} (hx : ‖x - p‖ ≤ h) :
    μ (exclusionRegion h p x) ≤
      ENNReal.ofReal ((base * h) ^ Module.finrank ℝ E) * μ (ball (0 : E) 1) := by
  calc
    μ (exclusionRegion h p x)
        ≤ μ (ball (p + (3 / 2 : ℝ) • (x - p)) (base * h)) :=
      measure_mono (exclusionRegion_subset_ball hh.le hx)
    _ = _ := addHaar_ball_of_pos μ _ (mul_pos base_pos hh)

end Hoffman
