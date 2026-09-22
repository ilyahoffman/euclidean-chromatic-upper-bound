import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The nonnegative-coefficient polynomial in Section 5

These are the coefficients printed in R006. Their identification with
spherical coordinate moments is a separate, unfinished obligation.
-/

namespace Hoffman

open scoped BigOperators

noncomputable def momentCoeff (d j : ℕ) : ℝ :=
  (d.choose (2 * j) : ℝ) * ∏ i ∈ Finset.range j,
    ((2 * i + 1 : ℕ) : ℝ) / ((d + 2 * i : ℕ) : ℝ)

noncomputable def momentPolynomial (d : ℕ) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d / 2 + 1), momentCoeff d j * a ^ (2 * j)

theorem momentCoeff_nonneg (d j : ℕ) : 0 ≤ momentCoeff d j := by
  unfold momentCoeff
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.prod_nonneg
  intro i hi
  positivity

theorem momentCoeff_zero (d : ℕ) : momentCoeff d 0 = 1 := by
  simp [momentCoeff]

theorem momentPolynomial_mono (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    momentPolynomial d a ≤ momentPolynomial d b := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (momentCoeff_nonneg d j)

theorem one_le_momentPolynomial (d : ℕ) (a : ℝ) : 1 ≤ momentPolynomial d a := by
  have h := Finset.single_le_sum
    (f := fun j => momentCoeff d j * a ^ (2 * j))
    (s := Finset.range (d / 2 + 1))
    (fun j _ => mul_nonneg (momentCoeff_nonneg d j) (by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg a) j))
    (show 0 ∈ Finset.range (d / 2 + 1) by simp)
  simpa [momentCoeff_zero, momentPolynomial] using h

theorem momentPolynomial_pos (d : ℕ) (a : ℝ) : 0 < momentPolynomial d a :=
  lt_of_lt_of_le zero_lt_one (one_le_momentPolynomial d a)

theorem momentPolynomial_le_at_one (d : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    momentPolynomial d a ≤ momentPolynomial d 1 :=
  momentPolynomial_mono d ha ha1

end Hoffman
