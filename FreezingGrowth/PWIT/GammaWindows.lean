module

public import FreezingGrowth.PWIT.Erlang
public import FreezingGrowth.PWIT.TimeCenterEstimates

/-!
# Uniform density and window estimates for integer-shape Gamma laws

For Gamma shape `n + 1`, the density is centered here at its mode `n`.
A bounded number of standard deviations from that mode has a density bounded
below by an explicit constant divided by `sqrt n`. The constants are uniform
in `n`; later uses centered at the shape must account for the unit shift.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem log_one_add_lower_quadratic_half {u : ℝ} (hu : -(1 / 2 : ℝ) ≤ u) :
    u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
  rw [he] at hh
  apply le_trans _ hh
  apply (le_div_iff₀ hp).mpr
  have hpoly := mul_nonneg (sq_nonneg u) (show 0 ≤ 1 + 2 * u by linarith)
  nlinarith

theorem gammaPDFReal_nat_succ_formula (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaPDFReal ((n : ℝ) + 1) 1 x = x ^ n * Real.exp (-x) / n.factorial := by
  simp only [gammaPDFReal, ite_eq_left hx, Real.one_rpow, Real.Gamma_nat_eq_factorial,
    add_sub_cancel_right, Real.rpow_natCast, one_mul]
  ring

private theorem gamma_stirling_exponential_identity {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    Real.exp ((n : ℝ) * Real.log (x / n) - x + n - 1) / Real.sqrt n =
      (x ^ n * Real.exp (-x)) /
        (Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq : 0 < x / (n : ℝ) := div_pos hx hn'
  have hen : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) n
  rw [show (n : ℝ) * Real.log (x / n) - x + n - 1 =
    ((n : ℝ) * Real.log (x / n) + (-x)) + n - 1 by ring,
    Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hq,
    hen, div_pow]
  field_simp
  rw [← mul_pow]
  congr 1
  field_simp

theorem gammaPDFReal_nat_succ_lower_logRatio {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    Real.exp ((n : ℝ) * Real.log (x / n) - x + n - 1) / Real.sqrt n ≤
      gammaPDFReal ((n : ℝ) + 1) 1 x := by
  rw [gamma_stirling_exponential_identity hn hx, gammaPDFReal_nat_succ_formula n hx.le]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (factorial_le_stirling_upper hn)

theorem gamma_window_deviation_bounds {n : ℕ} (hn : 0 < n) {C x : ℝ}
    (_hC : 0 ≤ C) (hsize : 4 * C ^ 2 ≤ (n : ℝ))
    (hx : |x - n| ≤ C * Real.sqrt n) :
    0 < x ∧ -(1 / 2 : ℝ) ≤ (x - n) / n ∧
      (n : ℝ) * ((x - n) / n) ^ 2 ≤ C ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hn'.le
  have hCs : 2 * C ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hhalf : C * Real.sqrt (n : ℝ) ≤ (n : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hCs hs
    nlinarith
  have habs := abs_le.mp hx
  have hpos : 0 < x := by linarith
  refine ⟨hpos, ?_, ?_⟩
  · apply (le_div_iff₀ hn').mpr
    linarith
  · have hsq := pow_le_pow_left₀ (abs_nonneg (x - n)) hx 2
    rw [sq_abs, mul_pow, hs2] at hsq
    have he : (n : ℝ) * ((x - n) / n) ^ 2 = (x - n) ^ 2 / n := by
      field_simp
    rw [he]
    exact (div_le_iff₀ hn').mpr hsq

/-- A uniform lower bound throughout a bounded standardized Gamma window. -/
theorem gammaPDFReal_nat_succ_lower_window {n : ℕ} (hn : 0 < n) {C x : ℝ}
    (hC : 0 ≤ C) (hsize : 4 * C ^ 2 ≤ (n : ℝ))
    (hx : |x - n| ≤ C * Real.sqrt n) :
    Real.exp (-1 - 2 * C ^ 2) / Real.sqrt n ≤
      gammaPDFReal ((n : ℝ) + 1) 1 x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hxpos, hu, hu2⟩ := gamma_window_deviation_bounds hn hC hsize hx
  have hl := mul_le_mul_of_nonneg_left (log_one_add_lower_quadratic_half hu) hn'.le
  have hratio : 1 + (x - n) / (n : ℝ) = x / n := by field_simp; ring
  have hmul : (n : ℝ) * ((x - n) / n) = x - n := by field_simp
  rw [hratio] at hl
  have harg : -1 - 2 * C ^ 2 ≤ (n : ℝ) * Real.log (x / n) - x + n - 1 := by
    nlinarith
  exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr harg) (Real.sqrt_nonneg _)).trans
    (gammaPDFReal_nat_succ_lower_logRatio hn hxpos)

/-- The square-root density upper bound is global, including negative inputs. -/
theorem gammaPDFReal_nat_succ_upper {n : ℕ} (hn : 0 < n) (x : ℝ) :
    gammaPDFReal ((n : ℝ) + 1) 1 x ≤ 1 / Real.sqrt n := by
  by_cases hx : 0 ≤ x
  · rw [gammaPDFReal_nat_succ_formula n hx, le_div_iff₀ (by positivity : 0 < Real.sqrt (n : ℝ))]
    have h := generation_intensity_exp_upper hn
      (div_nonneg hx (Real.exp_pos (1 : ℝ)).le)
    have harg : Real.exp 1 * (x / Real.exp 1) - n = x - n := by field_simp
    rw [harg, div_pow] at h
    have he : (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
      simpa only [mul_one] using (Real.exp_nat_mul (1 : ℝ) n).symm
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos ((n : ℝ) - x)).le
    rw [← Real.exp_add, show (x - n) + ((n : ℝ) - x) = 0 by ring, Real.exp_zero] at hh
    have hmul : Real.sqrt (n : ℝ) * (x ^ n / (Real.exp 1) ^ n / n.factorial) *
        Real.exp ((n : ℝ) - x) =
          (x ^ n * Real.exp (-x) / n.factorial) * Real.sqrt n := by
      rw [he, Real.exp_sub, Real.exp_neg]
      field_simp
    rwa [hmul] at hh
  · simp only [gammaPDFReal, ite_eq_right hx]
    positivity

theorem gammaMeasure_nat_succ_window_lower_of_density (n : ℕ) {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c)
    (hpdf : ∀ x ∈ Icc a b, c ≤ gammaPDFReal ((n : ℝ) + 1) 1 x) :
    c * (b - a) ≤ (gammaMeasure ((n : ℝ) + 1) 1).real (Icc a b) := by
  have : IsProbabilityMeasure (gammaMeasure ((n : ℝ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hbound : ENNReal.ofReal (c * (b - a)) ≤ gammaMeasure ((n : ℝ) + 1) 1 (Icc a b) := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Icc]
    calc
      _ = ∫⁻ _x in Icc a b, ENNReal.ofReal c := by
        simp [lintegral_const, Real.volume_Icc, ENNReal.ofReal_mul hc]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact ENNReal.ofReal_le_ofReal (hpdf x hx)
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hbound
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hc (sub_nonneg.mpr hab)), measureReal_def] using hreal

/-- Every fixed standardized interval has a uniformly positive mass once
the integer mode is large enough. The displayed constant is explicit. -/
theorem gammaMeasure_nat_succ_standardized_window_lower {n : ℕ} (hn : 0 < n)
    {A B C : ℝ} (hC : 0 ≤ C) (hsize : 4 * C ^ 2 ≤ (n : ℝ))
    (hA : -C ≤ A) (hAB : A ≤ B) (hB : B ≤ C) :
    (B - A) * Real.exp (-1 - 2 * C ^ 2) ≤
      (gammaMeasure ((n : ℝ) + 1) 1).real
        (Icc ((n : ℝ) + A * Real.sqrt n) ((n : ℝ) + B * Real.sqrt n)) := by
  have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hab : (n : ℝ) + A * Real.sqrt n ≤ (n : ℝ) + B * Real.sqrt n := by
    nlinarith
  have hpdf : ∀ x ∈ Icc ((n : ℝ) + A * Real.sqrt n) ((n : ℝ) + B * Real.sqrt n),
      Real.exp (-1 - 2 * C ^ 2) / Real.sqrt n ≤ gammaPDFReal ((n : ℝ) + 1) 1 x := by
    intro x hx
    obtain ⟨hxl, hxu⟩ := hx
    have hAl := mul_le_mul_of_nonneg_right hA hs
    have hBu := mul_le_mul_of_nonneg_right hB hs
    apply gammaPDFReal_nat_succ_lower_window hn hC hsize
    apply abs_le.mpr
    constructor <;> nlinarith
  have h := gammaMeasure_nat_succ_window_lower_of_density n hab (by positivity) hpdf
  have he : Real.exp (-1 - 2 * C ^ 2) / Real.sqrt n *
      (((n : ℝ) + B * Real.sqrt n) - ((n : ℝ) + A * Real.sqrt n)) =
        (B - A) * Real.exp (-1 - 2 * C ^ 2) := by
    field_simp
    ring
  rwa [he] at h

end FreezingGrowth.PWIT
