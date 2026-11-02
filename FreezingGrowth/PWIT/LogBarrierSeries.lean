module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Summable logarithmic weights used in the ballot occupancy estimate. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open Filter
open scoped Topology

theorem summable_log_power_three_halves (P : ℕ) :
    Summable (fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) ^ P /
      (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) ^ P /
      ((n : ℝ) + 1) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (isLittleO_log_rpow_rpow_atTop (P : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hx
  have hg : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) := by
    convert (Real.summable_one_div_nat_add_rpow 1 (5 / 4)).mpr (by norm_num) using 1
    funext n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  apply hg.of_norm_bounded_eventually_nat
  have hsmall := (tendsto_order.mp hlim).2 (1 / (2 : ℝ) ^ P) (by positivity)
  filter_upwards [hsmall, (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1] with n hn hlog
  dsimp only [Function.comp_apply] at hlog
  let x := (n : ℝ) + 1
  have hxp : 0 < x := by dsimp [x]; positivity
  have hlogp : 0 ≤ Real.log x := by dsimp [x]; linarith
  have hpow : (1 + Real.log x) ^ P ≤ (2 : ℝ) ^ P * Real.log x ^ P := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith)
    dsimp [x] at *
    linarith
  have hn' : Real.log x ^ P ≤ (1 / (2 : ℝ) ^ P) * x ^ (1 / 4 : ℝ) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hxp _)).mp hn.le
  have hnum : (1 + Real.log x) ^ P ≤ x ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ P * Real.log x ^ P := hpow
      _ ≤ (2 : ℝ) ^ P * ((1 / (2 : ℝ) ^ P) * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by field_simp
  have hden : x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
    calc
      _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hxp]; norm_num
  have he : x ^ (1 / 4 : ℝ) / (x * Real.sqrt x) = 1 / x ^ (5 / 4 : ℝ) := by
    rw [hden, ← Real.rpow_sub hxp]
    norm_num
    rw [Real.rpow_neg hxp.le]
  change ‖(1 + Real.log x) ^ P / (x * Real.sqrt x)‖ ≤ 1 / x ^ (5 / 4 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq he

end FreezingGrowth.PWIT
