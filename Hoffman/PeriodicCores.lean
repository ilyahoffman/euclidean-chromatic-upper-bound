import Hoffman.ExclusionBall
import Hoffman.RandomSurvival

namespace Hoffman

open Set Metric MeasureTheory

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddCommGroup G]

def configurationCenters {n : ℕ} (π : E →+ G) (s : Fin n → G) : Set E :=
  π ⁻¹' Set.range s

omit [InnerProductSpace ℝ E] in
theorem configurationCenters_periodic {n : ℕ} (π : E →+ G) (s : Fin n → G)
    {t : E} (ht : π t = 0) :
    (fun z => z + t) '' configurationCenters π s = configurationCenters π s := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [configurationCenters, Set.mem_preimage, map_add, ht, add_zero] using hz
  · intro hx
    refine ⟨x - t, ?_, sub_add_cancel x t⟩
    simpa only [configurationCenters, Set.mem_preimage, map_sub, ht, sub_zero] using hx

theorem configurationCore_periodic {n : ℕ} (π : E →+ G) (s : Fin n → G)
    (R h : ℝ) {t : E} (ht : π t = 0) (x : E) :
    x + t ∈ coreUnion (configurationCenters π s) R h ↔
      x ∈ coreUnion (configurationCenters π s) R h :=
  coreUnion_periodic R h (configurationCenters_periodic π s ht) x

noncomputable def localVector (π : E →+ G) (rep : G → E) (x : E) (p : G) : E :=
  rep (p - π x)

noncomputable def nearCenters (π : E →+ G) (rep : G → E) (x : E) (R : ℝ) : Set G :=
  {p | ‖localVector π rep x p‖ < R}

noncomputable def forbiddenCenter (π : E →+ G) (rep : G → E) (x : E) (p : G) : G :=
  π (x - (1 / 2 : ℝ) • localVector π rep x p)

omit [InnerProductSpace ℝ E] in
theorem localVector_projection (π : E →+ G) (rep : G → E)
    (hrep : ∀ p, π (rep p) = p) (x : E) (p : G) :
    π (localVector π rep x p) = p - π x := hrep _

theorem nearCenters_conflict (π : E →+ G) (rep : G → E)
    (hrep : ∀ p, π (rep p) = p) (x : E) {R r : ℝ}
    (hRr : 3 / 2 * R ≤ r) (forbidden : Set G)
    (hball : ∀ v : E, ‖v‖ < r → π v ∈ forbidden) :
    ∀ p ∈ nearCenters π rep x R, ∀ q ∈ nearCenters π rep x R,
      q - forbiddenCenter π rep x p ∈ forbidden := by
  intro p hp q hq
  let vp := localVector π rep x p
  let vq := localVector π rep x q
  have hn : ‖vq + (1 / 2 : ℝ) • vp‖ < r := by
    have hh := norm_add_le vq ((1 / 2 : ℝ) • vp)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hh
    change ‖vp‖ < R at hp
    change ‖vq‖ < R at hq
    linarith
  have hpj := localVector_projection π rep hrep x p
  have hqj := localVector_projection π rep hrep x q
  have heq : q - forbiddenCenter π rep x p = π (vq + (1 / 2 : ℝ) • vp) := by
    simp only [forbiddenCenter, map_sub, map_add]
    change q - (π x - π ((1 / 2 : ℝ) • vp)) = π vq + π ((1 / 2 : ℝ) • vp)
    rw [hqj]
    abel
  rw [heq]
  exact hball _ hn

theorem survivalEvent_mem_core (π : E →+ G) (rep : G → E)
    (hrep : ∀ p, π (rep p) = p)
    (hperiod : ∀ v : E, π v = 0 → v ≠ 0 → 2 ≤ ‖v‖)
    {η : ℝ} (hη : 0 ≤ η) (_hη1 : η < 1) (x : E)
    (forbidden : Set G)
    (hball : ∀ v : E, ‖v‖ < base * offset η → π v ∈ forbidden)
    {n : ℕ} {i : Fin (n + 1)} {s : Fin (n + 1) → G}
    (hs : s ∈ survivalEvent i (nearCenters π rep x (radius η)) forbidden
      (forbiddenCenter π rep x)) :
    x ∈ coreUnion (configurationCenters π s) (radius η) (offset η) := by
  let v := localVector π rep x (s i)
  let p := x + v
  have hv : ‖v‖ < radius η := hs.1
  have hpr : π p = s i := by
    change π (x + localVector π rep x (s i)) = s i
    rw [map_add, localVector_projection π rep hrep]
    abel
  have hxp : ‖x - p‖ ≤ radius η := by
    have he : x - p = -v := by dsimp [p]; abel
    rw [he, norm_neg]
    exact hv.le
  refine ⟨p, ⟨i, hpr.symm⟩, hxp, ?_⟩
  intro z hz hzp
  obtain ⟨j, hj⟩ := hz
  by_cases hji : j = i
  · have hzj : π (z - p) = 0 := by rw [map_sub, hpr, ← hj, hji, sub_self]
    apply far_center_does_not_cut hxp
    rw [radius_offset, mul_one]
    exact hperiod (z - p) hzj (sub_ne_zero.mpr hzp)
  · by_contra hcut
    have hex : z ∈ exclusionRegion (offset η) p x := hcut
    have hxh : ‖x - p‖ ≤ offset η := by
      have hrh : radius η ≤ offset η := by unfold radius offset; linarith
      exact hxp.trans hrh
    have hnorm := exclusionRegion_subset_ball (show 0 ≤ offset η by unfold offset; linarith) hxh hex
    have he : p + (3 / 2 : ℝ) • (x - p) = x - (1 / 2 : ℝ) • v := by dsimp [p]; module
    rw [he, Metric.mem_ball, dist_eq_norm] at hnorm
    have hforb := hball (z - (x - (1 / 2 : ℝ) • v)) hnorm
    have heq : π (z - (x - (1 / 2 : ℝ) • v)) = s j - forbiddenCenter π rep x (s i) := by
      rw [map_sub, ← hj]
      rfl
    rw [heq] at hforb
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hji
    have hnot := hs.2 a
    rw [ha] at hnot
    exact hnot hforb

end Hoffman
