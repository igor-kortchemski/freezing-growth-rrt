module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Elementary absolute-moment bounds used in the next depth-gap argument.
These inequalities do not assert any unproved moment formula for tree depths. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory

theorem sq_le_scaled_abs_add_fourth (x : ℝ) {t : ℝ} (ht : 0 < t) :
    x ^ 2 ≤ t * |x| + x ^ 4 / t ^ 2 := by
  by_cases hx : |x| ≤ t
  · have hh : |x| ^ 2 ≤ t * |x| := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hx (abs_nonneg x)
    rw [sq_abs] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hsq : t ^ 2 ≤ x ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ ht.le (le_of_not_ge hx) 2
    have hh : x ^ 2 ≤ x ^ 4 / t ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
      have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg x)
      nlinarith
    exact hh.trans (le_add_of_nonneg_left (by positivity))

theorem integral_sq_le_scaled_abs_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ)
    (h2 : Integrable (fun ω => f ω ^ 2) μ) (h4 : Integrable (fun ω => f ω ^ 4) μ)
    {t : ℝ} (ht : 0 < t) :
    (∫ ω, f ω ^ 2 ∂μ) ≤ t * (∫ ω, |f ω| ∂μ) + (∫ ω, f ω ^ 4 ∂μ) / t ^ 2 := by
  have hiabs := hf.abs
  calc
    _ ≤ ∫ ω, t * |f ω| + f ω ^ 4 / t ^ 2 ∂μ :=
      integral_mono h2 ((hiabs.const_mul t).add (h4.div_const (t ^ 2)))
        (fun ω => sq_le_scaled_abs_add_fourth (f ω) ht)
    _ = _ := by
      rw [integral_add (hiabs.const_mul t) (h4.div_const (t ^ 2)),
        integral_const_mul, integral_div]

/-- Matching second and fourth moment scales give a growing absolute first
moment by an elementary split inequality, without a limit theorem. -/
theorem sqrt_le_integral_abs_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ)
    (h2 : Integrable (fun ω => f ω ^ 2) μ) (h4 : Integrable (fun ω => f ω ^ 4) μ)
    {a : ℝ} (ha : 1 ≤ a) (hlower : a / 2 ≤ ∫ ω, f ω ^ 2 ∂μ)
    (hupper : (∫ ω, f ω ^ 4 ∂μ) ≤ 3 * a ^ 2 + a) :
    Real.sqrt a / 16 ≤ ∫ ω, |f ω| ∂μ := by
  have hap : 0 < a := by linarith
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr hap
  have hs2 := Real.sq_sqrt hap.le
  have ht : 0 < 4 * Real.sqrt a := by positivity
  have hh := integral_sq_le_scaled_abs_add_fourth hf h2 h4 ht
  have h4bound : (∫ ω, f ω ^ 4 ∂μ) / (4 * Real.sqrt a) ^ 2 ≤ a / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    rw [mul_pow, hs2]
    have ha2 : a ≤ a ^ 2 := by nlinarith
    nlinarith [hupper]
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith [hlower, hh, h4bound]

/-- A uniformly bounded variance gives a uniformly bounded absolute deviation.
The probability normalization is explicit. -/
theorem integral_abs_le_one_of_sq_le_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (h2 : Integrable (fun ω => f ω ^ 2) μ)
    (hbound : (∫ ω, f ω ^ 2 ∂μ) ≤ 1) : (∫ ω, |f ω| ∂μ) ≤ 1 := by
  have hh : (∫ ω, 2 * |f ω| ∂μ) ≤ ∫ ω, 1 + f ω ^ 2 ∂μ := by
    apply integral_mono (hf.abs.const_mul 2) ((integrable_const 1).add h2)
    intro ω
    change 2 * |f ω| ≤ 1 + f ω ^ 2
    nlinarith [sq_nonneg (|f ω| - 1), sq_abs (f ω)]
  rw [integral_const_mul, integral_add (integrable_const 1) h2] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hh
  linarith

end FreezingGrowth
