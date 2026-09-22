import Hoffman.Geometry
import Hoffman.Planar

/-!
# A ball enclosing the exclusion region

This estimate supplies the exponential base of the main theorem directly.
It does not require the exact spherical moment or its asymptotic expansion.
-/

namespace Hoffman

open Set Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def exclusionRegion (h : ℝ) (p x : E) : Set E :=
  {z | x ∉ halfspace h p z}

theorem base_sq : base ^ 2 = 27 / 4 := by
  unfold base
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith

/-- Every excluding center lies in a shifted ball of radius `(3√3/2) h`.
This is a geometric estimate; no volume or probability assumption is used. -/
theorem exclusionRegion_subset_ball {h : ℝ} (hh : 0 ≤ h) {p x : E}
    (hx : ‖x - p‖ ≤ h) :
    exclusionRegion h p x ⊆ ball (p + (3 / 2 : ℝ) • (x - p)) (base * h) := by
  intro z hz
  have hz' : ‖z - p‖ ^ 2 / 2 - h * ‖z - p‖ < ⟪x - p, z - p⟫ := by
    simpa [exclusionRegion, halfspace] using hz
  have hi : ⟪z - p, x - p⟫ = ⟪x - p, z - p⟫ := real_inner_comm _ _
  have heq : z - (p + (3 / 2 : ℝ) • (x - p)) =
      (z - p) - (3 / 2 : ℝ) • (x - p) := by abel
  have hn : ‖z - (p + (3 / 2 : ℝ) • (x - p))‖ ^ 2 =
      ‖z - p‖ ^ 2 - 3 * ⟪x - p, z - p⟫ + 9 / 4 * ‖x - p‖ ^ 2 := by
    rw [heq, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, hi]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    norm_num
    ring
  have hv : ‖x - p‖ ^ 2 ≤ h ^ 2 := by nlinarith [norm_nonneg (x - p)]
  have hb : (base * h) ^ 2 = 27 / 4 * h ^ 2 := by rw [mul_pow, base_sq]
  have hnorm : 0 ≤ ‖z - (p + (3 / 2 : ℝ) • (x - p))‖ := norm_nonneg _
  have hr : 0 ≤ base * h := mul_nonneg base_pos.le hh
  rw [Metric.mem_ball, dist_eq_norm]
  nlinarith [sq_nonneg (‖z - p‖ - 3 * h)]

end Hoffman
