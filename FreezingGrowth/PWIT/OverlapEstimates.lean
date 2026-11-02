module

public import FreezingGrowth.PWIT.TimeCenterEstimates
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Analytic estimates for summing common-ancestor overlap bounds.
These do not assert a probabilistic pair estimate. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open Filter
open scoped Topology

/-- The apparent loss from a short suffix is uniformly bounded. -/
theorem overlap_log_factor_le {d q : ℝ} (hq : 1 ≤ q) (hqd : q ≤ d) :
    q / d * Real.log d - Real.log q ≤ 1 := by
  have hqpos : 0 < q := by linarith
  have hdpos : 0 < d := hqpos.trans_le hqd
  have hα : 0 ≤ q / d := by positivity
  have hα1 : q / d ≤ 1 := (div_le_one hdpos).mpr hqd
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hl := Real.log_le_sub_one_of_pos (div_pos hdpos hqpos)
  rw [Real.log_div hdpos.ne' hqpos.ne'] at hl
  have hh := mul_le_mul_of_nonneg_left hl hα
  have he : q / d * (d / q - 1) = 1 - q / d := by field_simp
  rw [he] at hh
  nlinarith [mul_nonneg (sub_nonneg.mpr hα1) hlq]

theorem overlap_factor_le {d q : ℝ} (hq : 1 ≤ q) (hqd : q ≤ d) :
    q ^ (-3 / 2 : ℝ) * d ^ (3 * q / (2 * d)) ≤ Real.exp (3 / 2 : ℝ) := by
  have hqpos : 0 < q := by linarith
  have hdpos : 0 < d := hqpos.trans_le hqd
  rw [Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hdpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := overlap_log_factor_le hq hqd
  have he : Real.log q * (-3 / 2) + Real.log d * (3 * q / (2 * d)) =
      (3 / 2) * (q / d * Real.log d - Real.log q) := by ring
  rw [he]
  linarith

/-- Any polynomial prefactor is summable against a stretched exponential.
The constants and positive exponent are fixed before the summation index. -/
theorem summable_pow_mul_exp_neg_rpow (k : ℕ) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ β)) := by
  have hsmall := (isLittleO_log_rpow_atTop hβ).bound
    (by positivity : (0 : ℝ) < c / ((k : ℝ) + 2))
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  have hdom : ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ β)‖ ≤ 1 / (n : ℝ) ^ 2 := by
    filter_upwards [hnat, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hnreal),
      abs_of_nonneg (Real.rpow_nonneg hnpos.le β)] at hn
    have harg : ((k : ℝ) + 2) * Real.log (n : ℝ) ≤ c * (n : ℝ) ^ β := by
      have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mp
        (show Real.log (n : ℝ) ≤ c * (n : ℝ) ^ β / ((k : ℝ) + 2) by
          simpa only [div_mul_eq_mul_div] using hn)
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (n : ℝ) ^ k * Real.exp (-(((k : ℝ) + 2) * Real.log (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      _ = 1 / (n : ℝ) ^ 2 := by
        rw [show ((k : ℝ) + 2) * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ (k + 2)) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity),
          pow_add]
        field_simp
  exact Summable.of_norm_bounded_eventually_nat
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))) hdom

end FreezingGrowth.PWIT
