module

public import FreezingGrowth.PWIT.StirlingBounds
public import FreezingGrowth.PWIT.GoodPaths
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniform analytic estimates for the generation first moment. -/

@[expose] public section
namespace FreezingGrowth.PWIT

/-- A quadratic logarithm lower bound requiring no asymptotic assumption. -/
theorem log_one_add_lower_quadratic {u : ℝ} (hu : 0 ≤ u) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hp
  apply le_trans _ hh
  have he : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
  rw [he]
  apply (le_div_iff₀ hp).mpr
  nlinarith [pow_nonneg hu 3]

/-- The factorial denominator retains the square-root prefactor uniformly. -/
theorem generation_intensity_exp_upper {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt n * (t ^ n / (n.factorial : ℝ)) ≤ Real.exp (Real.exp 1 * t - n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := Real.exp_pos (1 : ℝ)
  have ha : 0 < ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hy : 0 ≤ Real.exp 1 * t / n := by positivity
  have hbase : Real.exp 1 * t / n ≤ Real.exp (Real.exp 1 * t / n - 1) := by
    have hh := Real.add_one_le_exp (Real.exp 1 * t / n - 1)
    linarith
  have hpow := pow_le_pow_left₀ hy hbase n
  rw [← Real.exp_nat_mul] at hpow
  have harg : (n : ℝ) * (Real.exp 1 * t / n - 1) = Real.exp 1 * t - n := by
    field_simp
  rw [harg] at hpow
  have htbound : t ^ n ≤ ((n : ℝ) / Real.exp 1) ^ n * Real.exp (Real.exp 1 * t - n) := by
    calc
      t ^ n = ((n : ℝ) / Real.exp 1) ^ n * (Real.exp 1 * t / n) ^ n := by
        rw [← mul_pow]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow ha.le
  have hπ : 1 ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * Real.pi * n) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hfac : Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) :=
    (mul_le_mul_of_nonneg_right hsqrt ha.le).trans (Stirling.le_factorial_stirling n)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  calc
    Real.sqrt (n : ℝ) * t ^ n ≤ Real.sqrt (n : ℝ) *
        (((n : ℝ) / Real.exp 1) ^ n * Real.exp (Real.exp 1 * t - n)) :=
      mul_le_mul_of_nonneg_left htbound (Real.sqrt_nonneg _)
    _ = (Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) *
        Real.exp (Real.exp 1 * t - n) := by ring
    _ ≤ (n.factorial : ℝ) * Real.exp (Real.exp 1 * t - n) :=
      mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
    _ = _ := mul_comm _ _

open Filter
open scoped Topology

theorem tendsto_shifted_log_square_div (a c : ℝ) :
    Tendsto (fun n : ℕ => (a * Real.log (n : ℝ) - c) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero, pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := ((h2.const_mul (a ^ 2)).sub (h1.const_mul (2 * a * c))).add (h0.const_mul (c ^ 2))
  have he : (fun n : ℕ => (a * Real.log (n : ℝ) - c) ^ 2 / (n : ℝ)) =
      (fun n : ℕ => a ^ 2 * (Real.log (n : ℝ) ^ 2 / (n : ℝ)) -
        2 * a * c * (Real.log (n : ℝ) / (n : ℝ)) + c ^ 2 * (1 / (n : ℝ))) := by
    funext n
    ring
  rw [he]
  simpa only [mul_zero, sub_zero, add_zero] using hh

/-- The logarithmic Taylor error vanishes even on the moving log(n)/n scale. -/
theorem tendsto_log_power_remainder (c : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.log
      (1 + (((3 / 2 : ℝ) * Real.log (n : ℝ) - c) / (n : ℝ))) -
        ((3 / 2 : ℝ) * Real.log (n : ℝ) - c)) atTop (𝓝 0) := by
  let f (n : ℕ) : ℝ := (n : ℝ) * Real.log
      (1 + (((3 / 2 : ℝ) * Real.log (n : ℝ) - c) / (n : ℝ))) -
        ((3 / 2 : ℝ) * Real.log (n : ℝ) - c)
  have hevent : ∀ᶠ n : ℕ in atTop, 0 ≤ -f n ∧
      -f n ≤ (((3 / 2 : ℝ) * Real.log (n : ℝ) - c) ^ 2 / (n : ℝ)) := by
    have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hl := hlog.eventually (eventually_ge_atTop ((2 / 3 : ℝ) * c))
    filter_upwards [hl, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu : 0 ≤ ((3 / 2 : ℝ) * Real.log (n : ℝ) - c) / (n : ℝ) := by
      apply div_nonneg _ hnpos.le
      simp only [Function.comp_def] at hn
      linarith
    let u : ℝ := ((3 / 2 : ℝ) * Real.log (n : ℝ) - c) / (n : ℝ)
    have hlower := log_one_add_lower_quadratic hu
    have hupper := Real.log_le_sub_one_of_pos (show 0 < 1 + u by dsimp [u]; linarith)
    have he : (n : ℝ) * u = (3 / 2 : ℝ) * Real.log (n : ℝ) - c := by
      dsimp [u]
      field_simp
    have he2 : (n : ℝ) * u ^ 2 =
        ((3 / 2 : ℝ) * Real.log (n : ℝ) - c) ^ 2 / (n : ℝ) := by
      dsimp [u]
      field_simp
    have h1 := mul_le_mul_of_nonneg_left hlower hnpos.le
    have h2 := mul_le_mul_of_nonneg_left hupper hnpos.le
    change u - u ^ 2 ≤ Real.log (1 + u) at hlower
    dsimp [f]
    change 0 ≤ -((n : ℝ) * Real.log (1 + u) - _) ∧ _
    constructor <;> nlinarith
  have hh : Tendsto (fun n => -f n) atTop (𝓝 0) :=
    squeeze_zero' (hevent.mono fun _ hh => hh.1)
      (hevent.mono fun _ hh => hh.2) (tendsto_shifted_log_square_div (3 / 2) c)
  simpa only [neg_neg, neg_zero] using hh.neg

/-- Logarithmic asymptotic of the first moment at the critical generation time. -/
theorem tendsto_critical_log_intensity (s : ℝ) :
    Tendsto (fun n : ℕ => Real.log ((timeCenter n - s) ^ n /
      ((n.factorial : ℝ) * (n : ℝ)))) atTop
      (𝓝 (-Real.exp 1 * s - Real.log (Real.sqrt Real.pi) - (1 / 2 : ℝ) * Real.log 2)) := by
  let rem (n : ℕ) : ℝ := (n : ℝ) * Real.log
      (1 + (((3 / 2 : ℝ) * Real.log (n : ℝ) - Real.exp 1 * s) / (n : ℝ))) -
        ((3 / 2 : ℝ) * Real.log (n : ℝ) - Real.exp 1 * s)
  have hr : Tendsto rem atTop (𝓝 0) := tendsto_log_power_remainder (Real.exp 1 * s)
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity : Real.sqrt Real.pi ≠ 0)
  have haux : Tendsto (fun n => rem n - Real.exp 1 * s -
      Real.log (Stirling.stirlingSeq n) - (1 / 2 : ℝ) * Real.log 2) atTop
      (𝓝 (-Real.exp 1 * s - Real.log (Real.sqrt Real.pi) - (1 / 2 : ℝ) * Real.log 2)) := by
    simpa only [zero_sub, neg_mul] using ((hr.sub_const (Real.exp 1 * s)).sub hs).sub_const
      ((1 / 2 : ℝ) * Real.log 2)
  apply haux.congr'
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := hlog.eventually (eventually_ge_atTop ((2 / 3 : ℝ) * (Real.exp 1 * s)))
  filter_upwards [hl, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let u : ℝ := ((3 / 2 : ℝ) * Real.log (n : ℝ) - Real.exp 1 * s) / n
  have hu : 0 ≤ u := by
    dsimp [u]
    apply div_nonneg _ hnpos.le
    simp only [Function.comp_def] at hn
    linarith
  have htime : timeCenter n - s = ((n : ℝ) / Real.exp 1) * (1 + u) := by
    unfold timeCenter
    dsimp [u]
    field_simp
    ring
  have htpos : 0 < timeCenter n - s := by rw [htime]; positivity
  have hlog : Real.log (timeCenter n - s) =
      Real.log ((n : ℝ) / Real.exp 1) + Real.log (1 + u) := by
    rw [htime, Real.log_mul (by positivity) (by linarith : 1 + u ≠ 0)]
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hst
  symm
  rw [Real.log_div (pow_pos htpos _).ne' (by positivity), Real.log_pow,
    Real.log_mul (by positivity : (n.factorial : ℝ) ≠ 0) hnpos.ne', hlog]
  dsimp [rem]
  change (n : ℝ) * (Real.log ((n : ℝ) / Real.exp 1) + Real.log (1 + u)) -
      (Real.log (n.factorial : ℝ) + Real.log (n : ℝ)) =
    (n : ℝ) * Real.log (1 + u) - ((3 / 2 : ℝ) * Real.log n - Real.exp 1 * s) -
      Real.exp 1 * s - Real.log (Stirling.stirlingSeq n) - (1 / 2 : ℝ) * Real.log 2
  nlinarith

end FreezingGrowth.PWIT
