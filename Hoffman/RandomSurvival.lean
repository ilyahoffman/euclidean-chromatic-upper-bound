import Hoffman.ProbabilityCover

/-!
# A finite random-center calculation

This supplies the probability step for the enclosing-ball construction.
The configuration is a finite product probability space. No Poisson process
or expected-volume interchange is needed for this calculation.
-/

namespace Hoffman

open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G]
  [MeasurableAdd₂ G] [MeasurableNeg G]

def survivalEvent {n : ℕ} (i : Fin (n + 1))
    (near forbidden : Set G) (center : G → G) : Set (Fin (n + 1) → G) :=
  {s | s i ∈ near ∧ ∀ j : Fin n, s (i.succAbove j) - center (s i) ∉ forbidden}

theorem survivalEvent_measurable {n : ℕ} (i : Fin (n + 1))
    {near forbidden : Set G} (hn : MeasurableSet near) (hb : MeasurableSet forbidden)
    {center : G → G} (hc : Measurable center) :
    MeasurableSet (survivalEvent i near forbidden center) := by
  have heq : survivalEvent i near forbidden center =
      ((fun s : Fin (n + 1) → G => s i) ⁻¹' near) ∩
        ⋂ j : Fin n, ((fun s : Fin (n + 1) → G =>
          s (i.succAbove j) - center (s i)) ⁻¹' forbidden)ᶜ := by
    ext s
    simp [survivalEvent]
  rw [heq]
  exact (hn.preimage (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun j =>
      (hb.preimage ((measurable_pi_apply _).sub (hc.comp (measurable_pi_apply i)))).compl)

theorem survivalEvent_measure (μ : Measure G) [IsProbabilityMeasure μ]
    [IsAddRightInvariant μ] {n : ℕ} (i : Fin (n + 1))
    {near forbidden : Set G} (hn : MeasurableSet near) (hb : MeasurableSet forbidden)
    {center : G → G} (hc : Measurable center) :
    Measure.pi (fun _ : Fin (n + 1) => μ) (survivalEvent i near forbidden center) =
      μ near * (1 - μ forbidden) ^ n := by
  let ν : Measure (Fin n → G) := Measure.pi (fun _ => μ)
  let shear : G × (Fin n → G) → G × (Fin n → G) :=
    fun p => (p.1, fun j => p.2 j - center p.1)
  have hs : MeasurePreserving shear (μ.prod ν) (μ.prod ν) := by
    refine (MeasurePreserving.id μ).skew_product (μc := ν) (μd := ν)
      (g := fun p q => fun j => q j - center p) ?_ ?_
    · exact measurable_pi_lambda _ fun j =>
        ((measurable_pi_apply j).comp measurable_snd).sub (hc.comp measurable_fst)
    · exact Filter.Eventually.of_forall fun p =>
        (measurePreserving_sub_right ν (fun _ => center p)).map_eq
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) i
  have hsplit : MeasurePreserving split (Measure.pi (fun _ => μ)) (μ.prod ν) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) i
  have hrect : MeasurableSet (near ×ˢ Set.pi Set.univ (fun _ : Fin n => forbiddenᶜ)) :=
    hn.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => hb.compl))
  have heq : survivalEvent i near forbidden center =
      (shear ∘ split) ⁻¹' (near ×ˢ Set.pi Set.univ (fun _ : Fin n => forbiddenᶜ)) := by
    ext s
    simp [survivalEvent, shear, split, Fin.removeNth]
  rw [heq, (hs.comp hsplit).measure_preimage hrect.nullMeasurableSet,
    Measure.prod_prod, Measure.pi_pi]
  simp [ν, measure_compl hb (measure_ne_top μ forbidden), measure_univ]

omit [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] in
theorem survivalEvents_disjoint {n : ℕ} {near forbidden : Set G} {center : G → G}
    (hconflict : ∀ p ∈ near, ∀ q ∈ near, q - center p ∈ forbidden) :
    Pairwise (fun i j : Fin (n + 1) =>
      Disjoint (survivalEvent i near forbidden center) (survivalEvent j near forbidden center)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro s hi hj
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hij.symm
  have hs := hi.2 a
  rw [ha] at hs
  exact hs (hconflict (s i) hi.1 (s j) hj.1)

theorem any_survival_measure (μ : Measure G) [IsProbabilityMeasure μ]
    [IsAddRightInvariant μ] (n : ℕ)
    {near forbidden : Set G} (hn : MeasurableSet near) (hb : MeasurableSet forbidden)
    {center : G → G} (hc : Measurable center)
    (hconflict : ∀ p ∈ near, ∀ q ∈ near, q - center p ∈ forbidden) :
    Measure.pi (fun _ : Fin (n + 1) => μ) (⋃ i, survivalEvent i near forbidden center) =
      (n + 1 : ℝ≥0∞) * μ near * (1 - μ forbidden) ^ n := by
  rw [measure_iUnion (survivalEvents_disjoint hconflict)
    (fun i => survivalEvent_measurable i hn hb hc)]
  simp_rw [survivalEvent_measure μ _ hn hb hc]
  simp [mul_assoc]

theorem bernoulli_survival (n : ℕ) {w : ℝ} (_hw : 0 ≤ w) (hw1 : w ≤ 1) :
    1 - (n : ℝ) * w ≤ (1 - w) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    calc
      1 - ((n : ℝ) + 1) * w ≤ (1 - (n : ℝ) * w) * (1 - w) := by
        nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg w)]
      _ ≤ (1 - w) ^ n * (1 - w) := mul_le_mul_of_nonneg_right ih (by linarith)

theorem normalized_survival_lower {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    1 / (4 * w) ≤ ((⌊1 / (2 * w)⌋₊ : ℝ) + 1) * (1 - w) ^ ⌊1 / (2 * w)⌋₊ := by
  let n : ℕ := ⌊1 / (2 * w)⌋₊
  have hn : (n : ℝ) * w ≤ 1 / 2 := by
    have hh := Nat.floor_le (show (0 : ℝ) ≤ 1 / (2 * w) by positivity)
    have hh' := (le_div_iff₀ (show 0 < 2 * w by positivity)).mp hh
    nlinarith
  have hn' : 1 / 2 ≤ ((n : ℝ) + 1) * w := by
    have hh := Nat.lt_floor_add_one (1 / (2 * w))
    have hh' := (div_lt_iff₀ (show 0 < 2 * w by positivity)).mp hh
    nlinarith
  have hp : 1 / 2 ≤ (1 - w) ^ n := by
    linarith [bernoulli_survival n hw.le hw1]
  calc
    1 / (4 * w) ≤ ((n : ℝ) + 1) / 2 := by
      apply (div_le_iff₀ (show 0 < 4 * w by positivity)).mpr
      nlinarith
    _ ≤ ((n : ℝ) + 1) * (1 - w) ^ n := by
      have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ n + 1 by positivity)
      linarith

theorem any_survival_lower (μ : Measure G) [IsProbabilityMeasure μ]
    [IsAddRightInvariant μ]
    {near forbidden : Set G} (hn : MeasurableSet near) (hb : MeasurableSet forbidden)
    {center : G → G} (hc : Measurable center)
    (hconflict : ∀ p ∈ near, ∀ q ∈ near, q - center p ∈ forbidden)
    {a w : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hw1 : w ≤ 1)
    (hmn : μ near = ENNReal.ofReal a) (hmb : μ forbidden = ENNReal.ofReal w) :
    ENNReal.ofReal (a / (4 * w)) ≤
      Measure.pi (fun _ : Fin (⌊1 / (2 * w)⌋₊ + 1) => μ)
        (⋃ i, survivalEvent i near forbidden center) := by
  let n : ℕ := ⌊1 / (2 * w)⌋₊
  have hs : a / (4 * w) ≤ ((n : ℝ) + 1) * a * (1 - w) ^ n := by
    have hh := mul_le_mul_of_nonneg_left (normalized_survival_lower hw hw1) ha
    change a * (1 / (4 * w)) ≤ a * (((n : ℝ) + 1) * (1 - w) ^ n) at hh
    convert hh using 1 <;> ring
  rw [any_survival_measure μ _ hn hb hc hconflict, hmn, hmb]
  have heq : (n + 1 : ℝ≥0∞) * ENNReal.ofReal a * (1 - ENNReal.ofReal w) ^ n =
      ENNReal.ofReal (((n : ℝ) + 1) * a * (1 - w) ^ n) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hw.le]
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) ha),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n + 1),
      ENNReal.ofReal_pow (sub_nonneg.mpr hw1)]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hs

end Hoffman
