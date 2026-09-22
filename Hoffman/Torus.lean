import Hoffman.Targets
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

set_option maxHeartbeats 800000

namespace Hoffman

open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal BigOperators

instance torusPeriodPositive : Fact (0 < (5 : ℝ)) := ⟨by norm_num⟩

abbrev FlatTorus (d : ℕ) := Fin d → AddCircle (5 : ℝ)

def torusProjection (d : ℕ) : Euclidean d →+ FlatTorus d where
  toFun x i := (x i : AddCircle (5 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; rfl

noncomputable def torusRepresentative (d : ℕ) (z : FlatTorus d) : Euclidean d :=
  (EuclideanSpace.measurableEquiv (Fin d)).symm (fun i =>
    ((AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))) (z i) : ℝ))

theorem torusProjection_representative (d : ℕ) (z : FlatTorus d) :
    torusProjection d (torusRepresentative d z) = z := by
  ext i
  exact (AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))).symm_apply_apply (z i)

theorem torusProjection_surjective (d : ℕ) : Function.Surjective (torusProjection d) :=
  fun z => ⟨torusRepresentative d z, torusProjection_representative d z⟩

theorem torusRepresentative_measurable (d : ℕ) : Measurable (torusRepresentative d) := by
  apply (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))).measurable.comp (measurable_pi_apply i))

theorem torusProjection_measurable (d : ℕ) : Measurable (torusProjection d) := by
  apply measurable_pi_iff.mpr
  intro i
  exact AddCircle.measurable_mk'.comp (measurable_pi_apply i)

noncomputable def circleProbability : Measure (AddCircle (5 : ℝ)) :=
  (5 : ℝ≥0∞)⁻¹ • volume

instance circleProbability_isProbability : IsProbabilityMeasure circleProbability := by
  constructor
  simp only [circleProbability, Measure.smul_apply, smul_eq_mul,
    AddCircle.measure_univ]
  norm_num only [ENNReal.ofReal_ofNat]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance circleProbability_leftInvariant : IsAddLeftInvariant circleProbability := by
  unfold circleProbability
  infer_instance

instance circleProbability_rightInvariant : IsAddRightInvariant circleProbability := by
  unfold circleProbability
  infer_instance

noncomputable def torusVolume (d : ℕ) : Measure (FlatTorus d) :=
  Measure.pi (fun _ => (volume : Measure (AddCircle (5 : ℝ))))

noncomputable def torusProbability (d : ℕ) : Measure (FlatTorus d) :=
  ((5 : ℝ≥0∞) ^ d)⁻¹ • torusVolume d

instance torusVolume_finite (d : ℕ) : IsFiniteMeasure (torusVolume d) := by
  unfold torusVolume
  infer_instance

instance torusVolume_leftInvariant (d : ℕ) : IsAddLeftInvariant (torusVolume d) := by
  unfold torusVolume
  infer_instance

instance torusVolume_rightInvariant (d : ℕ) : IsAddRightInvariant (torusVolume d) := by
  unfold torusVolume
  infer_instance

theorem torusVolume_univ (d : ℕ) : torusVolume d Set.univ = (5 : ℝ≥0∞) ^ d := by
  simp [torusVolume, Measure.pi_univ, AddCircle.measure_univ]

instance torusProbability_isProbability (d : ℕ) : IsProbabilityMeasure (torusProbability d) := by
  constructor
  simp only [torusProbability, Measure.smul_apply, smul_eq_mul, torusVolume_univ]
  exact ENNReal.inv_mul_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num))

instance torusProbability_leftInvariant (d : ℕ) : IsAddLeftInvariant (torusProbability d) := by
  unfold torusProbability
  infer_instance

instance torusProbability_rightInvariant (d : ℕ) : IsAddRightInvariant (torusProbability d) := by
  unfold torusProbability
  infer_instance

def fundamentalCube (d : ℕ) : Set (Euclidean d) :=
  {x | ∀ i, x i ∈ Set.Ioc (-(5 / 2 : ℝ)) (-(5 / 2 : ℝ) + 5)}

theorem representative_mem_cube (d : ℕ) (z : FlatTorus d) :
    torusRepresentative d z ∈ fundamentalCube d := by
  intro i
  exact ((AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))) (z i)).property

theorem representative_projection {d : ℕ} {x : Euclidean d}
    (hx : x ∈ fundamentalCube d) : torusRepresentative d (torusProjection d x) = x := by
  ext i
  have hh : (AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ)))
      ((x i : ℝ) : AddCircle (5 : ℝ)) = ⟨x i, hx i⟩ := by
    apply (AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))).symm.injective
    exact (AddCircle.measurableEquivIoc (5 : ℝ) (-(5 / 2 : ℝ))).symm_apply_apply _
  exact congrArg Subtype.val hh

theorem ball_subset_cube {d : ℕ} {r : ℝ} (hr : r < 5 / 2) :
    Metric.ball (0 : Euclidean d) r ⊆ fundamentalCube d := by
  intro x hx i
  have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hc : |x i| ≤ ‖x‖ := PiLp.norm_apply_le x i
  have ha := (abs_le.mp hc)
  constructor <;> linarith

theorem torusProjection_measurePreserving (d : ℕ) :
    MeasurePreserving (torusProjection d)
      (volume.restrict (fundamentalCube d)) (torusVolume d) := by
  let box : Set (Fin d → ℝ) :=
    Set.univ.pi (fun _ => Set.Ioc (-(5 / 2 : ℝ)) (-(5 / 2 : ℝ) + 5))
  have hbox : MeasurableSet box := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have he := (EuclideanSpace.volume_preserving_measurableEquiv (Fin d)).restrict_preimage hbox
  have hp : MeasurePreserving (fun x : Fin d → ℝ => fun i =>
      (x i : AddCircle (5 : ℝ))) (volume.restrict box) (torusVolume d) := by
    change MeasurePreserving _ ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ => Set.Ioc (-(5 / 2 : ℝ)) (-(5 / 2 : ℝ) + 5)))) _
    rw [Measure.restrict_pi_pi]
    exact measurePreserving_pi _ _ (fun _ => AddCircle.measurePreserving_mk 5 (-(5 / 2 : ℝ)))
  have hcube : (EuclideanSpace.measurableEquiv (Fin d)) ⁻¹' box = fundamentalCube d := by
    apply Set.ext
    intro x
    simp [fundamentalCube, box]
    rfl
  rw [hcube] at he
  exact hp.comp he

noncomputable def torusBall (d : ℕ) (r : ℝ) : Set (FlatTorus d) :=
  torusRepresentative d ⁻¹' Metric.ball 0 r

theorem torusBall_measurable (d : ℕ) (r : ℝ) : MeasurableSet (torusBall d r) :=
  Metric.isOpen_ball.measurableSet.preimage (torusRepresentative_measurable d)

theorem projection_mem_torusBall {d : ℕ} {r : ℝ} (hr : r < 5 / 2)
    {x : Euclidean d} (hx : ‖x‖ < r) : torusProjection d x ∈ torusBall d r := by
  have hb : x ∈ Metric.ball 0 r := by simpa using hx
  change torusRepresentative d (torusProjection d x) ∈ Metric.ball 0 r
  rw [representative_projection (ball_subset_cube hr hb)]
  exact hb

theorem torusBall_volume {d : ℕ} {r : ℝ} (hr : r < 5 / 2) :
    torusVolume d (torusBall d r) = volume (Metric.ball (0 : Euclidean d) r) := by
  have heq : torusProjection d ⁻¹' torusBall d r ∩ fundamentalCube d =
      Metric.ball (0 : Euclidean d) r := by
    apply Set.ext
    intro x
    simp only [Set.mem_inter_iff, Set.mem_preimage, torusBall]
    constructor
    · rintro ⟨hx, hc⟩
      change torusRepresentative d (torusProjection d x) ∈ Metric.ball 0 r at hx
      rwa [representative_projection hc] at hx
    · intro hx
      refine ⟨?_, ball_subset_cube hr hx⟩
      change torusRepresentative d (torusProjection d x) ∈ Metric.ball 0 r
      rwa [representative_projection (ball_subset_cube hr hx)]
  rw [← (torusProjection_measurePreserving d).measure_preimage
    (torusBall_measurable d r).nullMeasurableSet,
    Measure.restrict_apply ((torusBall_measurable d r).preimage (torusProjection_measurable d)), heq]

theorem torus_kernel_norm {d : ℕ} {v : Euclidean d}
    (hv : torusProjection d v = 0) (hv0 : v ≠ 0) : 5 ≤ ‖v‖ := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! hh
    apply hv0
    ext i
    exact hh i
  obtain ⟨i, hi⟩ := hex
  have hz : (v i : AddCircle (5 : ℝ)) = 0 := congrFun hv i
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (5 : ℝ)).mp hz
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp only [zero_zsmul] at hn
    exact hi hn.symm
  have hna : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  have hc := PiLp.norm_apply_le v i
  rw [← hn, Real.norm_eq_abs, zsmul_eq_mul, abs_mul] at hc
  norm_num only [abs_of_pos (show (0 : ℝ) < 5 by norm_num)] at hc
  nlinarith

theorem torusBall_probability {d : ℕ} {r : ℝ} (hr0 : 0 < r) (hr : r < 5 / 2) :
    torusProbability d (torusBall d r) =
      ((5 : ℝ≥0∞) ^ d)⁻¹ * ENNReal.ofReal (r ^ d) *
        volume (Metric.ball (0 : Euclidean d) 1) := by
  rw [torusProbability, Measure.smul_apply, smul_eq_mul, torusBall_volume hr,
    addHaar_ball_of_pos (volume : Measure (Euclidean d)) 0 hr0]
  simp [mul_assoc]

theorem torusBall_probability_pos {d : ℕ} {r : ℝ} (hr0 : 0 < r) (hr : r < 5 / 2) :
    0 < torusProbability d (torusBall d r) := by
  rw [torusProbability, Measure.smul_apply, smul_eq_mul, torusBall_volume hr]
  exact ENNReal.mul_pos (ENNReal.inv_pos.mpr (ENNReal.pow_ne_top (by norm_num))).ne'
    (Metric.measure_ball_pos volume 0 hr0).ne'

end Hoffman
