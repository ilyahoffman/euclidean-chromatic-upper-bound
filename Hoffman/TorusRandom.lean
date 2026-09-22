import Hoffman.Torus
import Hoffman.PeriodicCores
import Hoffman.RandomCover

namespace Hoffman

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal

noncomputable def ballMass (d : ℕ) (r : ℝ) : ℝ :=
  (torusProbability d (torusBall d r)).toReal

theorem ballMass_pos {d : ℕ} {r : ℝ} (hr0 : 0 < r) (hr : r < 5 / 2) :
    0 < ballMass d r :=
  ENNReal.toReal_pos (torusBall_probability_pos hr0 hr).ne' (measure_ne_top _ _)

theorem ballMass_le_one (d : ℕ) (r : ℝ) : ballMass d r ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by simpa using (prob_le_one (μ := torusProbability d) (s := torusBall d r)))

theorem ofReal_ballMass (d : ℕ) (r : ℝ) :
    ENNReal.ofReal (ballMass d r) = torusProbability d (torusBall d r) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem ballMass_eq {d : ℕ} {r : ℝ} (hr0 : 0 < r) (hr : r < 5 / 2) :
    ballMass d r = ((5 : ℝ) ^ d)⁻¹ * r ^ d *
      (volume (Metric.ball (0 : Euclidean d) 1)).toReal := by
  unfold ballMass
  rw [torusBall_probability hr0 hr]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (pow_nonneg hr0.le d)]

theorem ballMass_ratio {d : ℕ} {R r : ℝ} (hR0 : 0 < R) (hR : R < 5 / 2)
    (hr0 : 0 < r) (hr : r < 5 / 2) :
    ballMass d R / (4 * ballMass d r) = 1 / 4 * (R / r) ^ d := by
  have hv : (volume (Metric.ball (0 : Euclidean d) 1)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1)).ne'
      measure_ball_lt_top.ne).ne'
  rw [ballMass_eq hR0 hR, ballMass_eq hr0 hr, div_pow]
  field_simp
  ring

theorem torus_near_measurable (d : ℕ) (x : Euclidean d) (R : ℝ) :
    MeasurableSet (nearCenters (torusProjection d) (torusRepresentative d) x R) := by
  have he : nearCenters (torusProjection d) (torusRepresentative d) x R =
      (fun p => p - torusProjection d x) ⁻¹' torusBall d R := by
    apply Set.ext
    intro p
    simp [nearCenters, localVector, torusBall]
  rw [he]
  exact (torusBall_measurable d R).preimage (measurable_id.sub measurable_const)

theorem torus_near_mass (d : ℕ) (x : Euclidean d) (R : ℝ) :
    torusProbability d (nearCenters (torusProjection d) (torusRepresentative d) x R) =
      ENNReal.ofReal (ballMass d R) := by
  have he : nearCenters (torusProjection d) (torusRepresentative d) x R =
      (fun p => p - torusProjection d x) ⁻¹' torusBall d R := by
    apply Set.ext
    intro p
    simp [nearCenters, localVector, torusBall]
  rw [he, (measurePreserving_sub_right (torusProbability d) (torusProjection d x)).measure_preimage
    (torusBall_measurable d R).nullMeasurableSet, ofReal_ballMass]

theorem torus_forbiddenCenter_measurable (d : ℕ) (x : Euclidean d) :
    Measurable (forbiddenCenter (torusProjection d) (torusRepresentative d) x) := by
  exact (torusProjection_measurable d).comp
    (measurable_const.sub (((torusRepresentative_measurable d).comp
      (measurable_id.sub measurable_const)).const_smul (1 / 2 : ℝ)))

/-- Explicit coverage probability for finite random periodic Voronoi cores. -/
theorem torus_survival_lower (d : ℕ) (x : Euclidean d)
    {R r : ℝ} (hR0 : 0 < R) (hR : R < 5 / 2) (hr0 : 0 < r) (hr : r < 5 / 2)
    (hRr : 3 / 2 * R ≤ r) :
    ENNReal.ofReal (1 / 4 * (R / r) ^ d) ≤
      Measure.pi (fun _ : Fin (⌊1 / (2 * ballMass d r)⌋₊ + 1) => torusProbability d)
        (⋃ i, survivalEvent i
          (nearCenters (torusProjection d) (torusRepresentative d) x R)
          (torusBall d r) (forbiddenCenter (torusProjection d) (torusRepresentative d) x)) := by
  rw [← ballMass_ratio hR0 hR hr0 hr]
  exact any_survival_lower (torusProbability d)
    (torus_near_measurable d x R) (torusBall_measurable d r)
    (torus_forbiddenCenter_measurable d x)
    (nearCenters_conflict (torusProjection d) (torusRepresentative d)
      (torusProjection_representative d) x hRr (torusBall d r)
      (fun _ hv => projection_mem_torusBall hr hv))
    (ballMass_pos hR0 hR).le (ballMass_pos hr0 hr) (ballMass_le_one d r)
    (torus_near_mass d x R) (ofReal_ballMass d r).symm

end Hoffman
