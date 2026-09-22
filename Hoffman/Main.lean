import Hoffman.FiniteUpperBound
import Hoffman.AsymptoticEstimate

namespace Hoffman

/-- The explicit dimension-dependent construction satisfies the full coloring specification. -/
theorem colorBound_periodic_borel {d : ℕ} (hd : 2 ≤ d) :
    PeriodicBorelColoring d (colorBound d) := by
  exact finite_upper_bound (gridResolution_pos hd)
    (gapParameter_pos d) (gapParameter_lt_one hd) (exclusion_radius_small hd)
    (show 2 * (gapParameter d / 4) < gapParameter d by linarith [gapParameter_pos d])
    (grid_mesh_small hd)

/-- Full main upper bound, with the explicit universal constant `40 * exp 1 + 1`.
The conclusion includes Borel measurability and a full-rank lattice of periods. -/
theorem main_upper_bound_explicit (d : ℕ) (hd : 2 ≤ d) :
    ∃ k : ℕ, (k : ℝ) ≤ (40 * Real.exp 1 + 1) * d * Real.log d * base ^ d ∧
      PeriodicBorelColoring d k :=
  ⟨colorBound d, colorBound_le hd, colorBound_periodic_borel hd⟩

/-- The main proposition is proved, with no manuscript assertions assumed as axioms. -/
theorem main_upper_bound : MainUpperBound := by
  refine ⟨40 * Real.exp 1 + 1, by positivity, ?_⟩
  exact main_upper_bound_explicit

end Hoffman
