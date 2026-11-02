module

public import FreezingGrowth.RRTDepthGap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual two-vertex depth gap dominates every fixed multiple of the
regularized log-log error at a polynomially larger continuation horizon. -/

@[expose] public section
namespace FreezingGrowth.RRT

open Filter
open scoped Topology

/-- A positive square-root term dominates a fixed logarithmic correction. -/
theorem tendsto_sqrt_sub_log_atTop (a : ℝ) (ha : 0 < a) (C D : ℝ) :
    Tendsto (fun x : ℝ => a * Real.sqrt x - C * Real.log (1 + x) - D) atTop atTop := by
  have hsmall : ∀ᶠ x : ℝ in atTop,
      |C| * Real.log x ≤ (a / 2) * Real.sqrt x := by
    have hh := ((isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left |C|).bound (half_pos ha)
    filter_upwards [hh] with x hx
    simp only [Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg x)] at hx
    exact (le_abs_self _).trans hx
  have hbase : Tendsto
      (fun x : ℝ => (a / 2) * Real.sqrt x - (|C| * Real.log 2 + D)) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop
      (-(|C| * Real.log 2 + D))
      (Real.tendsto_sqrt_atTop.const_mul_atTop (half_pos ha))
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hsmall hx
  have hxpos : 0 < x := by linarith
  have hlog : Real.log (1 + x) ≤ Real.log 2 + Real.log x := by
    have hh := Real.log_le_log (by linarith : 0 < 1 + x)
      (show 1 + x ≤ 2 * x by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'] at hh
  have hlognonneg : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) hlognonneg
  have hh := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
  nlinarith

/-- A deterministic bound for the regularized log-log of a polynomial horizon.
It includes exponent zero, although the eventual applications use exponent nine. -/
theorem polynomialSuffixLogLog_le {x : ℝ} (hx : 1 ≤ x) (K : ℕ) :
    Real.log (1 + Real.log (x ^ K + 1)) ≤
      Real.log ((K : ℝ) + 2) + Real.log (1 + Real.log x) := by
  have hxpos : 0 < x := by linarith
  have hp : 1 ≤ x ^ K := one_le_pow₀ hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog₂ : Real.log (x ^ K + 1) ≤ Real.log 2 + (K : ℝ) * Real.log x := by
    have hh := Real.log_le_log (by positivity : 0 < x ^ K + 1)
      (show x ^ K + 1 ≤ 2 * x ^ K by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hxpos K).ne',
      Real.log_pow] at hh
  have htwo : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hinner : 1 + Real.log (x ^ K + 1) ≤
      ((K : ℝ) + 2) * (1 + Real.log x) := by
    have hK := Nat.cast_nonneg (α := ℝ) K
    nlinarith
  have hpositive : 0 < 1 + Real.log (x ^ K + 1) := by
    have hh : 0 ≤ Real.log (x ^ K + 1) := Real.log_nonneg (by linarith)
    linarith
  have hh := Real.log_le_log hpositive hinner
  rwa [Real.log_mul (by positivity : (K : ℝ) + 2 ≠ 0)
    (by positivity : 1 + Real.log x ≠ 0)] at hh

theorem eventually_sqrt_log_le_twice_sqrt_depthMean :
    ∀ᶠ m : ℕ in atTop, Real.sqrt (Real.log (m : ℝ)) / 2 ≤ Real.sqrt (depthMean m) := by
  have hratio : ∀ᶠ m : ℕ in atTop, (1 / 2 : ℝ) < depthMean m / Real.log (m : ℝ) :=
    depthMean_div_log_tendsto_one.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hratio, eventually_ge_atTop 2] with m hm hm₂
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hmreal
  have hmul := (lt_div_iff₀ hlogpos).mp hm
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt hlogpos.le, Real.sq_sqrt (depthMean_nonneg m)]
  norm_num
  linarith

/-- Polynomial continuation sizes leave enough room for the depth gap to
dominate the proved logarithmic-logarithmic component-height error. -/
theorem tendsto_expectedDistinctDepthGap_sub_polynomialSuffixLogLog (C : ℝ) (K : ℕ) :
    Tendsto (fun m : ℕ => expectedDistinctDepthGap m -
      C * Real.log (1 + Real.log ((m : ℝ) ^ K + 1))) atTop atTop := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun m : ℕ =>
      (1 / 32 : ℝ) * Real.sqrt (Real.log (m : ℝ)) -
        |C| * Real.log (1 + Real.log (m : ℝ)) -
          (1 + |C| * Real.log ((K : ℝ) + 2))) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_sqrt_sub_log_atTop (1 / 32) (by norm_num) |C|
        (1 + |C| * Real.log ((K : ℝ) + 2))).comp hlog
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [eventually_sqrt_log_le_twice_sqrt_depthMean,
    eventually_one_le_depthMean, eventually_ge_atTop 1] with m hs hm hm₁
  have hgap := expectedDistinctDepthGap_lower m hm₁ hm
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm₁
  have hlogbound := polynomialSuffixLogLog_le hmreal K
  have hnonneg : 0 ≤ Real.log (1 + Real.log ((m : ℝ) ^ K + 1)) := by
    apply Real.log_nonneg
    have hh : 0 ≤ Real.log ((m : ℝ) ^ K + 1) :=
      Real.log_nonneg (by have := pow_nonneg (Nat.cast_nonneg (α := ℝ) m) K; linarith)
    linarith
  have hC := mul_le_mul_of_nonneg_right (le_abs_self C) hnonneg
  have hh := mul_le_mul_of_nonneg_left hlogbound (abs_nonneg C)
  nlinarith

theorem tendsto_expectedDistinctDepthGap_sub_natPolynomialSuffixLogLog (C : ℝ) (K : ℕ) :
    Tendsto (fun m : ℕ => expectedDistinctDepthGap m -
      C * Real.log (1 + Real.log (((m ^ K : ℕ) : ℝ) + 1))) atTop atTop := by
  simpa only [Nat.cast_pow] using
    tendsto_expectedDistinctDepthGap_sub_polynomialSuffixLogLog C K

end FreezingGrowth.RRT
