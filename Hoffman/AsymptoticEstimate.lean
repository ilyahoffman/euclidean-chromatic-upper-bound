import Hoffman.TorusNet
import Hoffman.ExclusionBall

namespace Hoffman

noncomputable def gapParameter (d : ℕ) : ℝ := 1 / (2 * d + 1)
def gridResolution (d : ℕ) : ℕ := 64 * d ^ 2
noncomputable def coverageProbability (d : ℕ) : ℝ :=
  1 / 4 * (radius (gapParameter d) / (base * offset (gapParameter d))) ^ d
noncomputable def colorBound (d : ℕ) : ℕ :=
  ⌈(1 + Real.log ((gridResolution d + 1 : ℕ) ^ d)) / coverageProbability d⌉₊

theorem gapParameter_pos (d : ℕ) : 0 < gapParameter d := by
  unfold gapParameter
  positivity

theorem gapParameter_lt_one {d : ℕ} (hd : 2 ≤ d) : gapParameter d < 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold gapParameter
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * d + 1)).mpr
  linarith

theorem offset_gapParameter_le {d : ℕ} (hd : 2 ≤ d) : offset (gapParameter d) ≤ 3 / 5 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : gapParameter d ≤ 1 / 5 := by
    unfold gapParameter
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d + 1)).mpr
    linarith
  unfold offset
  linarith

theorem exclusion_radius_small {d : ℕ} (hd : 2 ≤ d) :
    base * offset (gapParameter d) < 5 / 2 := by
  have hb : base < 3 := by nlinarith [base_sq, base_pos]
  have hh : 0 < offset (gapParameter d) := by unfold offset; linarith [gapParameter_pos d]
  have hm := mul_lt_mul_of_pos_right hb hh
  linarith [offset_gapParameter_le hd]

theorem gridResolution_pos {d : ℕ} (hd : 2 ≤ d) : 0 < gridResolution d := by
  unfold gridResolution
  positivity

theorem grid_mesh_small {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) * (5 / gridResolution d) < gapParameter d / 4 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hden : 0 < 2 * (d : ℝ) + 1 := by positivity
  unfold gridResolution gapParameter
  push_cast
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  apply (lt_div_iff₀ hden).mpr
  field_simp
  apply (div_lt_iff₀ (show (0 : ℝ) < 64 * (d : ℝ) ^ 2 by positivity)).mpr
  nlinarith

theorem offset_radius_ratio {d : ℕ} (hd : 2 ≤ d) :
    offset (gapParameter d) / radius (gapParameter d) = 1 + 1 / (d : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hden : 2 * (d : ℝ) + 1 ≠ 0 := by positivity
  unfold offset radius gapParameter
  field_simp
  ring

theorem coverageProbability_pos {d : ℕ} (hd : 2 ≤ d) : 0 < coverageProbability d := by
  have hR := (parameters (gapParameter_pos d) (gapParameter_lt_one hd)).1
  have hh : 0 < offset (gapParameter d) := by unfold offset; linarith [gapParameter_pos d]
  have hb := base_pos
  unfold coverageProbability
  positivity

theorem one_add_inv_pow_le_exp {d : ℕ} (hd : 2 ≤ d) :
    (1 + 1 / (d : ℝ)) ^ d ≤ Real.exp 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hle : 1 + 1 / (d : ℝ) ≤ Real.exp (1 / d) := by
    linarith [Real.add_one_le_exp (1 / (d : ℝ))]
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + 1 / (d : ℝ) by positivity) hle d
  rw [← Real.exp_nat_mul] at hp
  have he : (d : ℝ) * (1 / d) = 1 := by field_simp
  rwa [he] at hp

theorem coverageProbability_inv_eq {d : ℕ} (hd : 2 ≤ d) :
    (coverageProbability d)⁻¹ = 4 * (base * (1 + 1 / (d : ℝ))) ^ d := by
  have he : (coverageProbability d)⁻¹ =
      4 * ((base * offset (gapParameter d)) / radius (gapParameter d)) ^ d := by
    unfold coverageProbability
    simp [div_eq_mul_inv, mul_inv_rev, ← inv_pow, mul_comm]
  rw [he, mul_div_assoc, offset_radius_ratio hd]

theorem colorBound_eq_explicit {d : ℕ} (hd : 2 ≤ d) :
    colorBound d = ⌈4 * (1 + (d : ℝ) * Real.log (64 * (d : ℝ) ^ 2 + 1)) *
      (base * (1 + 1 / (d : ℝ))) ^ d⌉₊ := by
  unfold colorBound
  rw [Real.log_pow, div_eq_mul_inv, coverageProbability_inv_eq hd]
  unfold gridResolution
  push_cast
  congr 1
  ring

theorem coverageProbability_inv_le {d : ℕ} (hd : 2 ≤ d) :
    (coverageProbability d)⁻¹ ≤ 4 * Real.exp 1 * base ^ d := by
  rw [coverageProbability_inv_eq hd, mul_pow]
  have hp := mul_le_mul_of_nonneg_left (one_add_inv_pow_le_exp hd)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg base_pos.le d))
  nlinarith

theorem dimension_log_ge_one {d : ℕ} (hd : 2 ≤ d) : 1 ≤ (d : ℝ) * Real.log d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hl
  have hld := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hd'
  nlinarith

theorem grid_log_bound {d : ℕ} (hd : 2 ≤ d) :
    Real.log (gridResolution d + 1 : ℕ) ≤ 9 * Real.log d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hq0 : (0 : ℝ) < (gridResolution d + 1 : ℕ) := by positivity
  have hq : ((gridResolution d + 1 : ℕ) : ℝ) ≤ 128 * (d : ℝ) ^ 2 := by
    norm_num [gridResolution]
    nlinarith
  have hh := Real.log_le_log hq0 hq
  rw [Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (pow_ne_zero _ hd0.ne'), Real.log_pow] at hh
  have h128 : Real.log 128 = 7 * Real.log 2 := by
    have he := Real.log_pow (2 : ℝ) 7
    norm_num at he
    exact he
  rw [h128] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hd'
  linarith

theorem colorBound_le {d : ℕ} (hd : 2 ≤ d) :
    (colorBound d : ℝ) ≤ (40 * Real.exp 1 + 1) * d * Real.log d * base ^ d := by
  have hδ := coverageProbability_pos hd
  have hlog : 0 ≤ Real.log ((gridResolution d + 1 : ℕ) ^ d) := by
    apply Real.log_nonneg
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ gridResolution d + 1 by omega))
  have hnum : 1 + Real.log ((gridResolution d + 1 : ℕ) ^ d) ≤ 10 * d * Real.log d := by
    rw [Real.log_pow]
    have hh := mul_le_mul_of_nonneg_left (grid_log_bound hd) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    nlinarith [dimension_log_ge_one hd]
  have hceil := Nat.ceil_lt_add_one (div_nonneg (by linarith :
    0 ≤ 1 + Real.log ((gridResolution d + 1 : ℕ) ^ d)) hδ.le)
  have hdiv : (1 + Real.log ((gridResolution d + 1 : ℕ) ^ d)) / coverageProbability d ≤
      40 * Real.exp 1 * d * Real.log d * base ^ d := by
    rw [div_eq_mul_inv]
    have hh := mul_le_mul hnum (coverageProbability_inv_le hd)
      (inv_nonneg.mpr hδ.le) (by nlinarith [dimension_log_ge_one hd])
    convert hh using 1
    ring
  have hb : (1 : ℝ) ≤ base := by nlinarith [base_sq, base_pos]
  have hpow : (1 : ℝ) ≤ base ^ d := one_le_pow₀ hb
  have hone : 1 ≤ (d : ℝ) * Real.log d * base ^ d := by
    simpa using mul_le_mul (dimension_log_ge_one hd) hpow zero_le_one
      (show (0 : ℝ) ≤ d * Real.log d by linarith [dimension_log_ge_one hd])
  change (⌈(1 + Real.log ((gridResolution d + 1 : ℕ) ^ d)) / coverageProbability d⌉₊ : ℝ) ≤ _
  nlinarith

end Hoffman
