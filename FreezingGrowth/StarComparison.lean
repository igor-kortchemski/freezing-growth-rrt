module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Numerical comparisons used for star probabilities

The Observation in Section 2.2 compares `1 / n!` and `1 / 2^(n-1)`.
This module proves that numerical comparison, and the vanishing factorial
reciprocal used near `eq:dif`. Identification of these numbers with actual
tree probabilities is a separate obligation; no stochastic comparison is
claimed here.
-/

@[expose] public section

namespace FreezingGrowth

open Filter
open scoped Topology

/-- The strict comparison behind the star-probability argument for `n ≥ 3`. -/
theorem two_pow_pred_lt_factorial {n : ℕ} (hn : 3 ≤ n) :
    2 ^ (n - 1) < Nat.factorial n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hone : 1 ≤ n := (by decide : 1 ≤ 3).trans hn
    have htwo : 2 ≤ n + 1 := ((by decide : 2 ≤ 3).trans hn).trans (Nat.le_succ n)
    calc
      2 ^ (n + 1 - 1) = 2 ^ (n - 1 + 1) := by
        simp only [Nat.add_sub_cancel_right, Nat.sub_add_cancel hone]
      _ = 2 ^ (n - 1) * 2 := pow_succ _ _
      _ < Nat.factorial n * 2 := Nat.mul_lt_mul_of_pos_right ih (by decide)
      _ = 2 * Nat.factorial n := Nat.mul_comm _ _
      _ ≤ (n + 1) * Nat.factorial n := Nat.mul_le_mul_right _ htwo
      _ = Nat.factorial (n + 1) := (Nat.factorial_succ n).symm

/-- Numerical inequality in the proof of the Section 2.2 Observation.
The factorial and exponential denominators are positive, so reciprocation
reverses their strict inequality. -/
theorem inv_factorial_lt_inv_two_pow_pred {n : ℕ} (hn : 3 ≤ n) :
    (1 : ℝ) / (Nat.factorial n : ℝ) < 1 / ((2 ^ (n - 1) : ℕ) : ℝ) := by
  have hpow : (0 : ℝ) < ((2 ^ (n - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have hlt : ((2 ^ (n - 1) : ℕ) : ℝ) < (Nat.factorial n : ℝ) :=
    Nat.cast_lt.mpr (two_pow_pred_lt_factorial hn)
  exact one_div_lt_one_div_of_lt hpow hlt

/-- The factorial reciprocal appearing in the star probability tends to zero. -/
theorem inverse_factorial_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.factorial n : ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp factorial_tendsto_atTop

end FreezingGrowth
