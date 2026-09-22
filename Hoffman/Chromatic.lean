import Hoffman.Main
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Hoffman

open Filter
open scoped Topology

/-- The usual unit-distance graph on real Euclidean space. -/
def unitDistanceGraph (d : ℕ) : SimpleGraph (Euclidean d) where
  Adj x y := dist x y = 1
  symm := by intro x y h; simpa only [dist_comm] using h
  loopless := by intro x; simp

theorem unitDistanceGraph_adj_iff_coordinates (d : ℕ) (x y : Euclidean d) :
    (unitDistanceGraph d).Adj x y ↔ ∑ i, (x i - y i) ^ 2 = 1 := by
  change dist x y = 1 ↔ _
  rw [EuclideanSpace.dist_eq]
  simp only [Real.dist_eq, sq_abs]
  constructor
  · intro h
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ∑ i, (x i - y i) ^ 2 by positivity)
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- This is mathlib's ordinary chromatic number, taking values in the extended naturals. -/
noncomputable def euclideanChromaticNumber (d : ℕ) : ℕ∞ :=
  (unitDistanceGraph d).chromaticNumber

theorem ordinary_chromaticNumber_le {d : ℕ} (hd : 2 ≤ d) :
    euclideanChromaticNumber d ≤ (colorBound d : ℕ∞) := by
  obtain ⟨c, _, hc, _⟩ := colorBound_periodic_borel hd
  apply SimpleGraph.Colorable.chromaticNumber_le
  exact ⟨SimpleGraph.Coloring.mk c (fun {x y} hxy => hc x y hxy)⟩

theorem ordinary_chromaticNumber_finite {d : ℕ} (hd : 2 ≤ d) :
    euclideanChromaticNumber d ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (ordinary_chromaticNumber_le hd)

/-- For dimensions at least two this real value is exactly the finite ordinary chromatic number. -/
noncomputable def chromaticReal (d : ℕ) : ℝ := (euclideanChromaticNumber d).toNat

theorem chromaticReal_le {d : ℕ} (hd : 2 ≤ d) :
    chromaticReal d ≤ (40 * Real.exp 1 + 1) * d * Real.log d * base ^ d := by
  have hh := ENat.toNat_le_of_le_coe (ordinary_chromaticNumber_le hd)
  have hh' : chromaticReal d ≤ (colorBound d : ℝ) := by
    unfold chromaticReal
    exact_mod_cast hh
  exact hh'.trans (colorBound_le hd)

noncomputable def rootEnvelope (d : ℕ) : ℝ :=
  Real.exp (Real.log base +
    Real.log (40 * Real.exp 1 + 1) / d + 2 * (Real.log d / d))

theorem chromatic_root_le_envelope {d : ℕ} (hd : 2 ≤ d) :
    (chromaticReal d) ^ (1 / (d : ℝ)) ≤ rootEnvelope d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hc0 : 0 < 40 * Real.exp 1 + 1 := by positivity
  have hχ0 : 0 ≤ chromaticReal d := Nat.cast_nonneg _
  have hb0 := base_pos
  have hlog : Real.log d ≤ (d : ℝ) := by linarith [Real.log_le_sub_one_of_pos hd0]
  have hpoly : chromaticReal d ≤ (40 * Real.exp 1 + 1) * (d : ℝ) ^ 2 * base ^ d := by
    apply (chromaticReal_le hd).trans
    have hh := mul_le_mul_of_nonneg_left hlog (mul_nonneg hc0.le hd0.le)
    have hh' := mul_le_mul_of_nonneg_right hh (pow_nonneg hb0.le d)
    nlinarith
  have hp := Real.rpow_le_rpow hχ0 hpoly (show (0 : ℝ) ≤ 1 / (d : ℝ) by positivity)
  apply hp.trans_eq
  rw [Real.rpow_def_of_pos (by positivity :
    0 < (40 * Real.exp 1 + 1) * (d : ℝ) ^ 2 * base ^ d)]
  unfold rootEnvelope
  congr 1
  rw [Real.log_mul (mul_ne_zero hc0.ne' (pow_ne_zero _ hd0.ne')) (pow_ne_zero _ hb0.ne'),
    Real.log_mul hc0.ne' (pow_ne_zero _ hd0.ne'), Real.log_pow, Real.log_pow]
  push_cast
  field_simp
  ring

theorem rootEnvelope_tendsto : Tendsto rootEnvelope atTop (𝓝 base) := by
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun d : ℕ => (d : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hlog : Tendsto (fun d : ℕ => Real.log d / (d : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hsum : Tendsto (fun d : ℕ => Real.log base +
      Real.log (40 * Real.exp 1 + 1) * (d : ℝ)⁻¹ + 2 * (Real.log d / (d : ℝ))) atTop
      (𝓝 (Real.log base + Real.log (40 * Real.exp 1 + 1) * 0 + 2 * 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add (tendsto_const_nhds.mul hlog)
  have he := Real.continuous_exp.continuousAt.tendsto.comp hsum
  simpa only [rootEnvelope, div_eq_mul_inv, mul_zero, add_zero, Real.exp_log base_pos] using he

/-- The exponential-base conclusion of Theorem 1 for the ordinary chromatic number. -/
theorem chromatic_root_limsup :
    Filter.limsup (fun d : ℕ => (chromaticReal d) ^ (1 / (d : ℝ))) atTop ≤ base := by
  have hlo : ∀ d : ℕ, (0 : ℝ) ≤ (chromaticReal d) ^ (1 / (d : ℝ)) := by
    intro d
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcob := Filter.isCoboundedUnder_le_of_le (l := (atTop : Filter ℕ)) hlo
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  apply (Filter.limsup_le_of_le hcob ?_)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    rootEnvelope_tendsto.eventually (gt_mem_nhds hb)] with d hd he
  exact (chromatic_root_le_envelope hd).trans he.le

end Hoffman
