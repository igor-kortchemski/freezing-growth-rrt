module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The paper's exact prefix size floor(n^(1/9)). These elementary comparisons
transfer estimates between the full continuation index and its prefix size. -/

@[expose] public section
namespace FreezingGrowth

open Filter

noncomputable def paperPrefixSize (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ (1 / 9 : ℝ))

private theorem ninthRoot_pow_nine (n : ℕ) :
    ((n : ℝ) ^ (1 / 9 : ℝ)) ^ (9 : ℕ) = (n : ℝ) := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (n := 9) (Nat.cast_nonneg (α := ℝ) n) (by norm_num)

theorem paperPrefixSize_pow_nine_le (n : ℕ) : paperPrefixSize n ^ 9 ≤ n := by
  have hx : 0 ≤ (n : ℝ) ^ (1 / 9 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hfloor : (paperPrefixSize n : ℝ) ≤ (n : ℝ) ^ (1 / 9 : ℝ) := Nat.floor_le hx
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (paperPrefixSize n)) hfloor 9
  rw [ninthRoot_pow_nine] at hh
  exact_mod_cast hh

theorem lt_paperPrefixSize_succ_pow_nine (n : ℕ) : n < (paperPrefixSize n + 1) ^ 9 := by
  have hx : 0 ≤ (n : ℝ) ^ (1 / 9 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hfloor : (n : ℝ) ^ (1 / 9 : ℝ) < (paperPrefixSize n : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hh := pow_lt_pow_left₀ hfloor hx (by norm_num : (9 : ℕ) ≠ 0)
  rw [ninthRoot_pow_nine] at hh
  exact_mod_cast hh

theorem tendsto_paperPrefixSize_atTop : Tendsto paperPrefixSize atTop atTop := by
  change Tendsto (fun n : ℕ => Nat.floor ((n : ℝ) ^ (1 / 9 : ℝ))) atTop atTop
  simpa only [Function.comp_def] using (tendsto_nat_floor_atTop (α := ℝ)).comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem le_paperPrefixSize_pow_eighteen (n : ℕ) (hm : 2 ≤ paperPrefixSize n) :
    n ≤ paperPrefixSize n ^ 18 := by
  have hbase : paperPrefixSize n + 1 ≤ paperPrefixSize n ^ 2 := by nlinarith
  have hp := pow_le_pow_left₀ (Nat.zero_le (paperPrefixSize n + 1)) hbase 9
  have hpower : (paperPrefixSize n + 1) ^ 9 ≤ paperPrefixSize n ^ 18 := by
    simpa only [← pow_mul, show (2 : ℕ) * 9 = 18 by norm_num] using hp
  exact (lt_paperPrefixSize_succ_pow_nine n).le.trans hpower

theorem eventually_le_paperPrefixSize_pow_eighteen :
    ∀ᶠ n : ℕ in atTop, n ≤ paperPrefixSize n ^ 18 := by
  filter_upwards [tendsto_paperPrefixSize_atTop.eventually (eventually_ge_atTop 2)] with n hn
  exact le_paperPrefixSize_pow_eighteen n hn

end FreezingGrowth
