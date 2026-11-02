module

public import FreezingGrowth.RRTDeepestParent
public import FreezingGrowth.RemovalStarProbability

/-! Eventual expected-height reversal, the stronger assertion in Section 2.5. -/

@[expose] public section
namespace FreezingGrowth

open Filter
open scoped Topology

theorem removal_reversal_eventually :
    ∀ᶠ n : ℕ in atTop, (removalLong n).expectedHeight < (removalShort n).expectedHeight := by
  have hf : Tendsto (fun n : ℕ => (1 : ℝ) / (6 * ((n + 1).factorial : ℝ)))
      atTop (𝓝 0) := by
    have h := (inverse_factorial_tendsto_zero.comp (tendsto_add_atTop_nat 1)).div_const 6
    simpa only [Function.comp_def, zero_div, div_div, mul_comm] using h
  have hlim := RRT.meanHeight_increment_tendsto_zero.add hf
  simp only [add_zero] at hlim
  have he := (tendsto_order.mp hlim).2 (1 / 12) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ), he] with n hn hsmall
  have h := removal_expectedHeight_comparison hn
  linarith

end FreezingGrowth
