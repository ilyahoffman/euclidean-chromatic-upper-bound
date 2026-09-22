import Mathlib.Probability.Distributions.Poisson
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The scalar Poisson summation identity

The count is shifted by one, so there is no `0 * q⁻¹` expression.
This is an identity of convergent real series, not a construction of a
Poisson point process or a proof of the expected-volume formula.
-/

namespace Hoffman

theorem poisson_size_biased_hasSum (μ q : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-μ) * μ ^ (n + 1) /
      (n + 1).factorial * (n + 1 : ℝ) * q ^ n)
      (μ * Real.exp (μ * (q - 1))) := by
  have hs : HasSum (fun n : ℕ => (μ * q) ^ n / n.factorial)
      (Real.exp (μ * q)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (μ * q)
  have hh := hs.mul_left (μ * Real.exp (-μ))
  have heq : μ * Real.exp (-μ) * Real.exp (μ * q) =
      μ * Real.exp (μ * (q - 1)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hh
  convert hh using 1
  ext n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, mul_pow]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem poisson_void_density_hasSum (rate V w : ℝ) (hV : V ≠ 0) :
    HasSum (fun n : ℕ =>
      (Real.exp (-(rate * V)) * (rate * V) ^ (n + 1) /
        (n + 1).factorial * (n + 1 : ℝ) * (1 - w / V) ^ n) / V)
      (rate * Real.exp (-rate * w)) := by
  have hh := (poisson_size_biased_hasSum (rate * V) (1 - w / V)).div_const V
  have hexp : rate * V * (1 - w / V - 1) = -rate * w := by
    field_simp
    ring
  rw [hexp] at hh
  convert hh using 1
  field_simp
  ring

/-- Pointwise survival estimate used at the choice `rate = 1/W`. -/
theorem survival_density_lower {W w : ℝ} (hW : 0 < W) (hw : w ≤ W) :
    Real.exp (-1) / W ≤ Real.exp (-w / W) / W := by
  apply div_le_div_of_nonneg_right _ hW.le
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ hW).mpr
  linarith

end Hoffman
