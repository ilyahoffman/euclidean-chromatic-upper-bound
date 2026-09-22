import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# Separated Voronoi cores (R006, Section 2)

The defining inequality is multiplied by the positive distance between the
centers. `normalized_halfspace_iff` identifies it with the manuscript's
inward-offset halfspace. The results hold in any real inner product space.
-/

namespace Hoffman

open Set Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def radius (η : ℝ) : ℝ := (1 - η) / 2
noncomputable def offset (η : ℝ) : ℝ := (1 + η) / 2

def halfspace (h : ℝ) (p z : E) : Set E :=
  {x | ⟪x - p, z - p⟫ ≤ ‖z - p‖ ^ 2 / 2 - h * ‖z - p‖}

def core (Λ : Set E) (R h : ℝ) (p : E) : Set E :=
  {x | ‖x - p‖ ≤ R ∧ ∀ z ∈ Λ, z ≠ p → x ∈ halfspace h p z}

def coreUnion (Λ : Set E) (R h : ℝ) : Set E :=
  {x | ∃ p ∈ Λ, x ∈ core Λ R h p}

def AvoidsGap (A : Set E) (η : ℝ) : Prop :=
  ∀ ⦃x y : E⦄, x ∈ A → y ∈ A →
    ¬ (1 - η < dist x y ∧ dist x y < 1 + η)

theorem radius_offset (η : ℝ) : radius η + offset η = 1 := by
  unfold radius offset
  ring

theorem parameters {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    0 < radius η ∧ radius η < offset η ∧
      2 * radius η < 1 ∧ 1 < 2 * offset η := by
  unfold radius offset
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem normalized_halfspace_iff (h : ℝ) (x p z : E) (hzp : z ≠ p) :
    (⟪x - (1 / 2 : ℝ) • (p + z), (‖z - p‖)⁻¹ • (z - p)⟫ ≤ -h)
      ↔ x ∈ halfspace h p z := by
  have hn : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have hv : x - (1 / 2 : ℝ) • (p + z) =
      (x - p) - (1 / 2 : ℝ) • (z - p) := by module
  rw [hv, inner_smul_right, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  change (‖z - p‖)⁻¹ * (⟪x - p, z - p⟫ -
      (1 / 2 : ℝ) * ‖z - p‖ ^ 2) ≤ -h ↔ _
  rw [inv_mul_eq_div, div_le_iff₀ hn]
  simp only [halfspace, Set.mem_setOf_eq]
  constructor <;> intro hh <;> linarith

theorem same_core_distance_le {Λ : Set E} {R h : ℝ} {p x y : E}
    (hx : x ∈ core Λ R h p) (hy : y ∈ core Λ R h p) :
    dist x y ≤ 2 * R := by
  have hb := norm_sub_le (x - p) (y - p)
  have heq : (x - p) - (y - p) = x - y := by abel
  rw [heq] at hb
  rw [dist_eq_norm]
  linarith [hx.1, hy.1]

theorem different_cores_distance_ge {Λ : Set E} {R h : ℝ} {p z x y : E}
    (hp : p ∈ Λ) (hz : z ∈ Λ) (hzp : z ≠ p)
    (hx : x ∈ core Λ R h p) (hy : y ∈ core Λ R h z) :
    2 * h ≤ dist x y := by
  have hn : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have hxcut := hx.2 z hz hzp
  have hycut := hy.2 p hp (Ne.symm hzp)
  change ⟪x - p, z - p⟫ ≤ ‖z - p‖ ^ 2 / 2 - h * ‖z - p‖ at hxcut
  change ⟪y - z, p - z⟫ ≤ ‖p - z‖ ^ 2 / 2 - h * ‖p - z‖ at hycut
  rw [norm_sub_rev p z] at hycut
  have hid : ⟪y - x, z - p⟫ = ‖z - p‖ ^ 2 -
      ⟪x - p, z - p⟫ - ⟪y - z, p - z⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hlower : (2 * h) * ‖z - p‖ ≤ ⟪y - x, z - p⟫ := by linarith
  have hupper := real_inner_le_norm (y - x) (z - p)
  have hh : 2 * h ≤ ‖y - x‖ :=
    (mul_le_mul_right hn).mp (hlower.trans hupper)
  simpa only [dist_eq_norm, norm_sub_rev y x] using hh

theorem core_union_avoids_gap (Λ : Set E) (η : ℝ) :
    AvoidsGap (coreUnion Λ (radius η) (offset η)) η := by
  rintro x y ⟨p, hp, hx⟩ ⟨z, hz, hy⟩ ⟨hlo, hhi⟩
  by_cases heq : z = p
  · subst z
    have hh := same_core_distance_le hx hy
    unfold radius at hh
    linarith
  · have hh := different_cores_distance_ge hp hz heq hx hy
    unfold offset at hh
    linarith

omit [InnerProductSpace ℝ E] in
theorem gap_implies_unit_distance_free {A : Set E} {η : ℝ}
    (hη : 0 < η) (hA : AvoidsGap A η) {x y : E}
    (hx : x ∈ A) (hy : y ∈ A) : dist x y ≠ 1 := by
  intro hxy
  apply hA hx hy
  constructor <;> linarith

theorem far_center_does_not_cut {R h : ℝ} {x p z : E}
    (hx : ‖x - p‖ ≤ R) (hfar : 2 * (R + h) ≤ ‖z - p‖) :
    x ∈ halfspace h p z := by
  have hn := norm_nonneg (z - p)
  have h1 := real_inner_le_norm (x - p) (z - p)
  have h2 := mul_le_mul_of_nonneg_right hx hn
  have h3 := mul_le_mul_of_nonneg_right hfar hn
  change ⟪x - p, z - p⟫ ≤ ‖z - p‖ ^ 2 / 2 - h * ‖z - p‖
  nlinarith

/-- Exact radial cutoff, equation (4) of R006. -/
theorem radial_exclusion_iff (h : ℝ) (p v θ : E) {t : ℝ}
    (ht : 0 < t) (hθ : ‖θ‖ = 1) :
    p + v ∉ halfspace h p (p + t • θ) ↔ t < 2 * h + 2 * ⟪v, θ⟫ := by
  simp only [halfspace, Set.mem_setOf_eq, add_sub_cancel_left,
    inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hθ, mul_one,
    not_le]
  constructor <;> intro hh
  · nlinarith
  · nlinarith

theorem radial_reach_pos {h : ℝ} {v θ : E} (hv : ‖v‖ < h) (hθ : ‖θ‖ = 1) :
    0 < 2 * h + 2 * ⟪v, θ⟫ := by
  have hh := real_inner_le_norm (-v) θ
  simp only [inner_neg_left, norm_neg, hθ, mul_one] at hh
  linarith

theorem core_translate_iff (Λ : Set E) (R h : ℝ) (p x t : E) :
    x + t ∈ core ((fun z => z + t) '' Λ) R h (p + t) ↔
      x ∈ core Λ R h p := by
  constructor
  · intro hx
    refine ⟨by simpa using hx.1, ?_⟩
    intro z hz hzp
    have hh := hx.2 (z + t) ⟨z, hz, rfl⟩ (by simpa using hzp)
    simpa [halfspace] using hh
  · intro hx
    refine ⟨by simpa using hx.1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩ hzp
    have hh := hx.2 z hz (by simpa using hzp)
    simpa [halfspace] using hh

theorem coreUnion_translate_iff (Λ : Set E) (R h : ℝ) (x t : E) :
    x + t ∈ coreUnion ((fun z => z + t) '' Λ) R h ↔
      x ∈ coreUnion Λ R h := by
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hx⟩
    exact ⟨p, hp, (core_translate_iff Λ R h p x t).mp hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨p + t, ⟨p, hp, rfl⟩, (core_translate_iff Λ R h p x t).mpr hx⟩

theorem coreUnion_periodic {Λ : Set E} (R h : ℝ) {t : E}
    (hΛ : (fun z => z + t) '' Λ = Λ) (x : E) :
    x + t ∈ coreUnion Λ R h ↔ x ∈ coreUnion Λ R h := by
  simpa only [hΛ] using coreUnion_translate_iff Λ R h x t

theorem isClosed_halfspace (h : ℝ) (p z : E) : IsClosed (halfspace h p z) := by
  apply isClosed_le
  · fun_prop
  · fun_prop

theorem isClosed_core (Λ : Set E) (R h : ℝ) (p : E) :
    IsClosed (core Λ R h p) := by
  have heq : core Λ R h p =
      {x | ‖x - p‖ ≤ R} ∩ ⋂ z ∈ Λ, ⋂ (_ : z ≠ p), halfspace h p z := by
    ext x
    simp [core]
  rw [heq]
  refine IsClosed.inter ?_ (isClosed_iInter fun z =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_halfspace h p z)
  apply isClosed_le <;> fun_prop

theorem measurableSet_core [MeasurableSpace E] [BorelSpace E]
    (Λ : Set E) (R h : ℝ) (p : E) : MeasurableSet (core Λ R h p) :=
  (isClosed_core Λ R h p).measurableSet

theorem measurableSet_coreUnion [MeasurableSpace E] [BorelSpace E]
    {Λ : Set E} (hΛ : Λ.Countable) (R h : ℝ) :
    MeasurableSet (coreUnion Λ R h) := by
  have heq : coreUnion Λ R h = ⋃ p ∈ Λ, core Λ R h p := by
    ext x
    simp [coreUnion]
  rw [heq]
  exact MeasurableSet.biUnion hΛ (fun p _ => measurableSet_core Λ R h p)

end Hoffman
