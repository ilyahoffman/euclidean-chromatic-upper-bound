import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Numerical estimate in the random covering argument

The union bound is connected to this estimate in `ProbabilityCover` and
instantiated on the torus in `FiniteUpperBound`. The ceiling and the strict
bound below one are fully part of the statement proved here.
-/

namespace Hoffman

theorem covering_failure_lt_one {m δ : ℝ} (hm : 0 < m)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    m * (1 - δ) ^ ⌈(1 + Real.log m) / δ⌉₊ < 1 := by
  let k : ℕ := ⌈(1 + Real.log m) / δ⌉₊
  have hk : 1 + Real.log m ≤ (k : ℝ) * δ := by
    exact (div_le_iff₀ hδ).mp (Nat.le_ceil ((1 + Real.log m) / δ))
  have hbase : 1 - δ ≤ Real.exp (-δ) := by
    linarith [Real.add_one_le_exp (-δ)]
  have hp : (1 - δ) ^ k ≤ Real.exp ((k : ℝ) * (-δ)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) hbase k
  have he : m * Real.exp ((k : ℝ) * (-δ)) ≤ Real.exp (-1) := by
    conv_lhs => rw [← Real.exp_log hm]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hp hm.le).trans he)
    (Real.exp_lt_one_iff.mpr (by norm_num))

end Hoffman
