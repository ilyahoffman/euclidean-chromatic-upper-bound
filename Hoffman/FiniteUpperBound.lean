import Hoffman.TorusRandom
import Hoffman.TorusNet

namespace Hoffman

open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal

/-- A complete finite-dimensional upper bound from the enclosing-ball construction. -/
theorem finite_upper_bound {d q : ℕ} (hq : 0 < q)
    {η ρ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hsmall : base * offset η < 5 / 2)
    (hρη : 2 * ρ < η) (hmesh : (d : ℝ) * (5 / q) < ρ) :
    PeriodicBorelColoring d
      ⌈(1 + Real.log ((q + 1 : ℕ) ^ d)) /
        (1 / 4 * (radius η / (base * offset η)) ^ d)⌉₊ := by
  classical
  let R := radius η
  let r := base * offset η
  let δ := 1 / 4 * (R / r) ^ d
  have hR0 : 0 < R := (parameters hη hη1).1
  have hh0 : 0 < offset η := by unfold offset; linarith
  have hr0 : 0 < r := mul_pos base_pos hh0
  have hR : R < 5 / 2 := by dsimp [R, radius]; linarith
  have hbase : (3 / 2 : ℝ) ≤ base := by nlinarith [base_sq, base_pos]
  have hRr : 3 / 2 * R ≤ r := by
    have hRh : R ≤ offset η := (parameters hη hη1).2.1.le
    exact (mul_le_mul_of_nonneg_left hRh (by norm_num)).trans
      (mul_le_mul_of_nonneg_right hbase hh0.le)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let n : ℕ := ⌊1 / (2 * ballMass d r)⌋₊
  let Ω := Fin (n + 1) → FlatTorus d
  let μ : Measure Ω := Measure.pi (fun _ => torusProbability d)
  let A : Ω → Set (Euclidean d) := fun s =>
    coreUnion (configurationCenters (torusProjection d) s) (radius η) (offset η)
  let m := (q + 1) ^ d
  have hm : 0 < m := by dsimp [m]; positivity
  let e : (Fin d → Fin (q + 1)) ≃ Fin m := Fintype.equivFinOfCardEq (by simp [m])
  let z : Fin m → Euclidean d := fun j => gridPoint d q (e.symm j)
  let B : Fin m → Set Ω := fun j => ⋃ i, survivalEvent i
    (nearCenters (torusProjection d) (torusRepresentative d) (z j) R)
    (torusBall d r) (forbiddenCenter (torusProjection d) (torusRepresentative d) (z j))
  have hB (j : Fin m) : MeasurableSet (B j) :=
    MeasurableSet.iUnion (fun i => survivalEvent_measurable i
      (torus_near_measurable d (z j) R) (torusBall_measurable d r)
      (torus_forbiddenCenter_measurable d (z j)))
  have hmass (j : Fin m) : ENNReal.ofReal δ ≤ μ (B j) :=
    torus_survival_lower d (z j) hR0 hR hr0 hsmall hRr
  have hδ1 : δ ≤ 1 := by
    have hh : ENNReal.ofReal δ ≤ ENNReal.ofReal 1 := by
      simpa only [ENNReal.ofReal_one] using
        (hmass ⟨0, hm⟩).trans (prob_le_one (μ := μ) (s := B ⟨0, hm⟩))
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp hh
  have hnet (x : Euclidean d) : ∃ j t, torusProjection d t = 0 ∧ dist x (z j + t) < ρ := by
    obtain ⟨j, t, ht, hd⟩ := periodic_grid_net hq hmesh x
    exact ⟨e j, t, ht, by simpa [z] using hd⟩
  have hBA (j : Fin m) (s : Ω) (hs : s ∈ B j) : z j ∈ A s := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
    exact survivalEvent_mem_core (torusProjection d) (torusRepresentative d)
      (torusProjection_representative d)
      (fun v hv hv0 => (by norm_num : (2 : ℝ) ≤ 5).trans (torus_kernel_norm hv hv0))
      hη.le hη1 (z j) (torusBall d r)
      (fun _ hv => projection_mem_torusBall hsmall hv) hi
  obtain ⟨c, hc, hproper, hper⟩ := random_net_coloring μ A
    {t | torusProjection d t = 0}
    (fun s => core_union_avoids_gap (configurationCenters (torusProjection d) s) η)
    hρη
    (fun s t ht x => configurationCore_periodic (torusProjection d) s _ _ ht x)
    hm z hnet B hB hBA hδ hδ1 hmass
  have hmeas_eq : (inferInstance : MeasurableSpace (Euclidean d)) = borel (Euclidean d) :=
    BorelSpace.measurable_eq
  simp only [← Nat.cast_pow]
  refine ⟨c, ?_, hproper, periodBasis d, ?_⟩
  · rw [← hmeas_eq]
    exact hc
  · intro x j
    exact hper (periodBasis d j) (periodBasis_projection d j) x

end Hoffman
