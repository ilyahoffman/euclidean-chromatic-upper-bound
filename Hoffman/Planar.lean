import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # The exact saddle-point constant (R006, Section 5) -/

namespace Hoffman

noncomputable def base : ℝ := 3 * Real.sqrt 3 / 2
noncomputable def triangleArea (u : ℝ) : ℝ := (1 + u) * Real.sqrt (1 - u ^ 2)

theorem base_pos : 0 < base := by unfold base; positivity

theorem planar_deficit_identity (u : ℝ) :
    27 / 16 - (1 + u) ^ 2 * (1 - u ^ 2) =
      (u - 1 / 2) ^ 2 * ((u + 3 / 2) ^ 2 + 1 / 2) := by ring

theorem triangleArea_le (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    triangleArea u ≤ 3 * Real.sqrt 3 / 4 := by
  have ha : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hs := Real.sq_sqrt ha
  have ht := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hd := planar_deficit_identity u
  have hp : 0 ≤ (u - 1 / 2) ^ 2 * ((u + 3 / 2) ^ 2 + 1 / 2) := by positivity
  have hsq : (triangleArea u) ^ 2 = (1 + u) ^ 2 * (1 - u ^ 2) := by
    rw [triangleArea, mul_pow, hs]
  have hh : 0 ≤ 3 * Real.sqrt 3 / 4 := by positivity
  nlinarith

theorem triangleArea_half : triangleArea (1 / 2) = 3 * Real.sqrt 3 / 4 := by
  have hs4 : Real.sqrt 4 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg 4]
  unfold triangleArea
  norm_num [Real.sqrt_div, hs4]
  ring

theorem triangleArea_eq_iff (u : ℝ) (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    triangleArea u = 3 * Real.sqrt 3 / 4 ↔ u = 1 / 2 := by
  constructor
  · intro heq
    have ha : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have hs : (triangleArea u) ^ 2 = (1 + u) ^ 2 * (1 - u ^ 2) := by
      rw [triangleArea, mul_pow, Real.sq_sqrt ha]
    have ht := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hd := planar_deficit_identity u
    have hz : (u - 1 / 2) ^ 2 * ((u + 3 / 2) ^ 2 + 1 / 2) = 0 := by
      rw [heq] at hs
      nlinarith
    have hpos : 0 < (u + 3 / 2) ^ 2 + (1 / 2 : ℝ) := by positivity
    have hzero : (u - 1 / 2) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_right hpos.ne'
    nlinarith [sq_nonneg (u - 1 / 2)]
  · rintro rfl
    exact triangleArea_half

theorem twice_maximum_eq_base : 2 * triangleArea (1 / 2) = base := by
  rw [triangleArea_half]
  unfold base
  ring

end Hoffman
