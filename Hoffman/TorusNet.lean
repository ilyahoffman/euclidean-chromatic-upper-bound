import Hoffman.Torus
import Mathlib.LinearAlgebra.Basis.SMul

namespace Hoffman

open Set Metric MeasureTheory
open scoped BigOperators

theorem euclidean_norm_le_sum {d : ℕ} (v : Euclidean d) :
    ‖v‖ ≤ ∑ i, |v i| := by
  classical
  have he : ∑ i, EuclideanSpace.single i (v i) = v := by
    ext j
    change (∑ i, EuclideanSpace.single i (v i)) j = v j
    change (∑ i, (fun k => EuclideanSpace.single i (v i) k)) j = v j
    simp [EuclideanSpace.single_apply]
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := congrArg norm he.symm
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| := by simp [Real.norm_eq_abs]

noncomputable def gridPoint (d q : ℕ) (j : Fin d → Fin (q + 1)) : Euclidean d :=
  (EuclideanSpace.measurableEquiv (Fin d)).symm (fun i =>
    -(5 / 2 : ℝ) + (j i : ℝ) * (5 / q))

theorem periodic_grid_net {d q : ℕ} (hq : 0 < q) {ρ : ℝ}
    (hρ : (d : ℝ) * (5 / q) < ρ) :
    ∀ x : Euclidean d, ∃ j : Fin d → Fin (q + 1), ∃ t : Euclidean d,
      torusProjection d t = 0 ∧ dist x (gridPoint d q j + t) < ρ := by
  intro x
  let v := torusRepresentative d (torusProjection d x)
  let mesh : ℝ := 5 / q
  have hm : 0 < mesh := by dsimp [mesh]; positivity
  have hmq : mesh * (q : ℝ) = 5 := by dsimp [mesh]; field_simp
  have hv : v ∈ fundamentalCube d := representative_mem_cube d _
  have hu (i : Fin d) : 0 ≤ v i + 5 / 2 ∧ v i + 5 / 2 ≤ 5 := by
    have hh := hv i
    constructor <;> linarith [hh.1, hh.2]
  let a : Fin d → ℕ := fun i => ⌊(v i + 5 / 2) / mesh⌋₊
  have hal (i : Fin d) : (a i : ℝ) * mesh ≤ v i + 5 / 2 :=
    (le_div_iff₀ hm).mp (Nat.floor_le (div_nonneg (hu i).1 hm.le))
  have hau (i : Fin d) : v i + 5 / 2 < ((a i : ℝ) + 1) * mesh :=
    (div_lt_iff₀ hm).mp (Nat.lt_floor_add_one ((v i + 5 / 2) / mesh))
  have haq (i : Fin d) : a i < q + 1 := by
    have hh : (a i : ℝ) ≤ (q : ℝ) := by
      apply (mul_le_mul_right hm).mp
      nlinarith [hal i, (hu i).2]
    exact Nat.lt_succ_of_le (by exact_mod_cast hh)
  let j : Fin d → Fin (q + 1) := fun i => ⟨a i, haq i⟩
  let t := x - v
  refine ⟨j, t, ?_, ?_⟩
  · dsimp [t, v]
    rw [map_sub, torusProjection_representative, sub_self]
  · have hdist : dist x (gridPoint d q j + t) = ‖v - gridPoint d q j‖ := by
      rw [dist_eq_norm]
      congr 1
      dsimp [t]
      abel
    rw [hdist]
    have hb (i : Fin d) : |(v - gridPoint d q j) i| ≤ mesh := by
      change |v i - (-(5 / 2 : ℝ) + (a i : ℝ) * mesh)| ≤ mesh
      apply abs_le.mpr
      constructor <;> linarith [hal i, hau i]
    calc
      ‖v - gridPoint d q j‖ ≤ ∑ i, |(v - gridPoint d q j) i| := euclidean_norm_le_sum _
      _ ≤ ∑ _ : Fin d, mesh := Finset.sum_le_sum (fun i _ => hb i)
      _ = (d : ℝ) * (5 / q) := by simp [mesh]
      _ < ρ := hρ

noncomputable def periodBasis (d : ℕ) : Basis (Fin d) ℝ (Euclidean d) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.unitsSMul
    (fun _ => Units.mk0 (5 : ℝ) (by norm_num))

theorem periodBasis_projection (d : ℕ) (j : Fin d) :
    torusProjection d (periodBasis d j) = 0 := by
  ext i
  simp [periodBasis, Basis.unitsSMul_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply, torusProjection]
  split_ifs
  · exact AddSubgroup.mem_zmultiples (5 : ℝ)
  · exact (AddSubgroup.zmultiples (5 : ℝ)).zero_mem

end Hoffman
