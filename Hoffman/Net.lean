import Hoffman.Geometry
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# From a robust cover to a Borel coloring

This proves the deterministic last step of the finite-net argument. It does
not assert that a small family of translates covering the net exists.
-/

namespace Hoffman

open Set Metric

variable {E : Type*} [NormedAddCommGroup E]

def openNeighborhood (A : Set E) (ρ : ℝ) : Set E :=
  ⋃ a ∈ A, ball a ρ

theorem isOpen_openNeighborhood (A : Set E) (ρ : ℝ) :
    IsOpen (openNeighborhood A ρ) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem neighborhood_unit_distance_free {A : Set E} {ρ η : ℝ}
    (hA : AvoidsGap A η) (hρη : 2 * ρ < η)
    {x y : E} (hx : x ∈ openNeighborhood A ρ)
    (hy : y ∈ openNeighborhood A ρ) : dist x y ≠ 1 := by
  obtain ⟨a, ha, hxa⟩ : ∃ a ∈ A, dist x a < ρ := by
    simpa [openNeighborhood] using hx
  obtain ⟨b, hb, hyb⟩ : ∃ b ∈ A, dist y b < ρ := by
    simpa [openNeighborhood] using hy
  intro hxy
  have hd := dist_dist_dist_le x y a b
  rw [hxy, Real.dist_eq] at hd
  have he := abs_le.mp hd
  apply hA ha hb
  constructor <;> linarith [he.1, he.2]

section FirstColor

omit [NormedAddCommGroup E]
variable [MeasurableSpace E]

/-- Pick the least member of a countable measurable cover. -/
noncomputable def firstColor (S : ℕ → Set E) (hS : ∀ x, ∃ n, x ∈ S n)
    (x : E) : ℕ := by
  classical
  exact Nat.find (hS x)

omit [MeasurableSpace E] in
theorem firstColor_mem (S : ℕ → Set E) (hS : ∀ x, ∃ n, x ∈ S n) (x : E) :
    x ∈ S (firstColor S hS x) := by
  classical
  exact Nat.find_spec (hS x)

theorem measurable_firstColor (S : ℕ → Set E) (hS : ∀ x, ∃ n, x ∈ S n)
    (hm : ∀ n, MeasurableSet (S n)) : Measurable (firstColor S hS) := by
  classical
  apply measurable_to_countable'
  intro n
  have heq : (firstColor S hS) ⁻¹' {n} = S n ∩ ⋂ j < n, (S j)ᶜ := by
    ext x
    simp [firstColor, Nat.find_eq_iff]
  rw [heq]
  exact (hm n).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (hm j).compl)

omit [MeasurableSpace E] in
theorem firstColor_lt (S : ℕ → Set E) (hS : ∀ x, ∃ n, x ∈ S n)
    {k : ℕ} (hk : ∀ x, ∃ n < k, x ∈ S n) (x : E) : firstColor S hS x < k := by
  classical
  obtain ⟨n, hnk, hn⟩ := hk x
  exact lt_of_le_of_lt (Nat.find_min' (hS x) hn) hnk

omit [MeasurableSpace E] in
theorem firstColor_invariant (S : ℕ → Set E) (hS : ∀ x, ∃ n, x ∈ S n)
    (f : E → E) (hf : ∀ n x, f x ∈ S n ↔ x ∈ S n) (x : E) :
    firstColor S hS (f x) = firstColor S hS x := by
  classical
  apply le_antisymm
  · exact Nat.find_min' (hS (f x)) ((hf _ x).mpr (firstColor_mem S hS x))
  · exact Nat.find_min' (hS x) ((hf _ x).mp (firstColor_mem S hS (f x)))

end FirstColor

/-- A finite cover by small open neighborhoods of gap-avoiding sets gives
a measurable coloring with at most `k` colors. -/
theorem borel_coloring_of_robust_cover [MeasurableSpace E] [BorelSpace E]
    (A : ℕ → Set E) {η ρ : ℝ} {k : ℕ}
    (hA : ∀ n, AvoidsGap (A n) η) (hρη : 2 * ρ < η)
    (hcover : ∀ x, ∃ n < k, x ∈ openNeighborhood (A n) ρ) :
    ∃ c : E → Fin k, Measurable c ∧
      ∀ x y, dist x y = 1 → c x ≠ c y := by
  classical
  let S := fun n => openNeighborhood (A n) ρ
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨n, _, hn⟩ := hcover x
    exact ⟨n, hn⟩
  let c : E → Fin k := fun x =>
    ⟨firstColor S hS x, firstColor_lt S hS hcover x⟩
  refine ⟨c, ?_, ?_⟩
  · apply measurable_to_countable'
    intro j
    have heq : c ⁻¹' {j} = firstColor S hS ⁻¹' {j.val} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff]
      rfl
    rw [heq]
    exact (measurable_firstColor S hS fun n =>
      (isOpen_openNeighborhood (A n) ρ).measurableSet) (measurableSet_singleton _)
  · intro x y hxy heq
    have hi : firstColor S hS x = firstColor S hS y := congrArg Fin.val heq
    have hx := firstColor_mem S hS x
    have hy := firstColor_mem S hS y
    rw [← hi] at hy
    exact neighborhood_unit_distance_free (hA _) hρη hx hy hxy

end Hoffman
