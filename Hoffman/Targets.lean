import Hoffman.Planar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The main statement and its semantic definitions

`MainUpperBound` is proved by `Hoffman.main_upper_bound` in `Hoffman/Main.lean`.
These definitions encode real Euclidean space, Borel measurability, finitely
many colors, and a full-rank lattice of periods. The ordinary chromatic
number and the root-limsup conclusion are treated in `Hoffman/Chromatic.lean`.
-/

namespace Hoffman

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

def ProperUnitColoring {X K : Type*} [PseudoMetricSpace X] (c : X → K) : Prop :=
  ∀ x y, dist x y = 1 → c x ≠ c y

/-- Periods contain a real basis, hence generate a full-rank period lattice. -/
def PeriodicBorelColoring (d k : ℕ) : Prop :=
  letI : MeasurableSpace (Euclidean d) := borel (Euclidean d)
  ∃ c : Euclidean d → Fin k, Measurable c ∧ ProperUnitColoring c ∧
    ∃ b : Basis (Fin d) ℝ (Euclidean d), ∀ x j, c (x + b j) = c x

/-- First assertion of Theorem 1 of R006, proved in `Hoffman.Main`. -/
def MainUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
    ∃ k : ℕ, (k : ℝ) ≤ C * d * Real.log d * base ^ d ∧
      PeriodicBorelColoring d k

end Hoffman
