module

public import FreezingGrowth.RRTLowerTailExponential
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Boosting the lower-tail rate to the paper's numerical rate

A finite shift of the proved constant-success seed boosts its success to
three quarters. The resulting contraction rate is at least `1/(3e)`. The
center remains the regularized lower center; no mean-centered E2 estimate
is asserted by this module.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open Filter
open scoped Topology

theorem seed_three_quarters_of_constantSuccessSeed {c : ℝ} (hc : 0 ≤ c)
    (hs : ConstantSuccessSeed c) :
    ∃ A : ℝ, 0 ≤ A ∧ SeedAt c A (3 / 4) := by
  obtain ⟨A, p, hA, hp, hp1, hseed⟩ := hs
  have hρ : 0 ≤ 1 - p / 2 := by linarith
  have hρ1 : 1 - p / 2 < 1 := by linarith
  have hlim : Tendsto (fun j : ℕ => (1 - p) * (1 - p / 2) ^ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1).const_mul (1 - p)
  obtain ⟨J, hJ⟩ := (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).exists
  refine ⟨A + (J : ℝ) * lowerTailStep,
    add_nonneg hA (mul_nonneg (Nat.cast_nonneg _) lowerTailStep_pos.le), fun n => ?_⟩
  have he : lowerCenter c n - (A + (J : ℝ) * lowerTailStep) =
      lowerCenter c n - A - (J : ℝ) * lowerTailStep := by ring
  rw [he]
  calc
    _ ≤ (1 - p) * (1 - p / 2) ^ J := lowerTail_geometric_of_seed hc hA hp hp1 hseed J n
    _ ≤ 1 / 4 := hJ.le
    _ = 1 - 3 / 4 := by norm_num

theorem lowerTailRate_three_quarters_ge :
    1 / (3 * Real.exp 1) ≤ lowerTailRate (3 / 4) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < (5 / 8 : ℝ) ^ 3)
    (by norm_num : (5 / 8 : ℝ) ^ 3 ≤ 1 / 4)
  rw [Real.log_pow, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (4 : ℝ) ≠ 0), Real.log_one] at hh
  have hlog : Real.log 4 ≤ -3 * Real.log (5 / 8 : ℝ) := by
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  change 1 / (3 * Real.exp 1) ≤
    -Real.log (1 - (3 / 4 : ℝ) / 2) / (Real.exp 1 * Real.log 4)
  rw [show 1 - (3 / 4 : ℝ) / 2 = 5 / 8 by norm_num]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.exp 1)
    lowerTailStep_pos).mpr
  have he := mul_le_mul_of_nonneg_left hlog (Real.exp_pos 1).le
  dsimp [lowerTailStep]
  nlinarith

/-- Every actual seed at a nonnegative center coefficient yields the fixed
numerical lower-tail rate, after absorbing one finite offset in a constant. -/
theorem lowerTail_paperRate_of_seed {c : ℝ} (hc : 0 ≤ c) (hs : ConstantSuccessSeed c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      lowerTail n (lowerCenter c n - x) ≤ C * Real.exp (-x / (3 * Real.exp 1)) := by
  obtain ⟨A, hA, hseed⟩ := seed_three_quarters_of_constantSuccessSeed hc hs
  let β := lowerTailRate (3 / 4)
  refine ⟨Real.exp (β * (A + lowerTailStep)), Real.exp_pos _, fun n x hx => ?_⟩
  have hbound := lowerTail_exp_of_seed hc hA
    (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1)
    hseed n (lowerCenter c n - x)
  have he : β * (A + lowerTailStep + (lowerCenter c n - x) - lowerCenter c n) =
      β * (A + lowerTailStep) + -(β * x) := by ring
  change lowerTail n (lowerCenter c n - x) ≤
    Real.exp (β * (A + lowerTailStep + (lowerCenter c n - x) - lowerCenter c n)) at hbound
  rw [he, Real.exp_add] at hbound
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right lowerTailRate_three_quarters_ge hx
  calc
    -(β * x) ≤ -(1 / (3 * Real.exp 1) * x) := neg_le_neg hmul
    _ = -x / (3 * Real.exp 1) := by ring

/-- The actual RRT lower tail, with coefficient two and rate `1/(3e)`. -/
theorem uniformLowerTailPaperRate :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      lowerTail n (lowerCenter 2 n - x) ≤ C * Real.exp (-x / (3 * Real.exp 1)) :=
  lowerTail_paperRate_of_seed (by norm_num : (0 : ℝ) ≤ 2)
    (constantSuccessSeed_of_clockLowerSeed PWIT.clockLowerSeed)

end FreezingGrowth.RRT
