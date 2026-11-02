module

public import FreezingGrowth.PWIT.PathClocks
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Integer-shape Gamma convolution

The convolution with one more rate-one exponential is proved by integrating a
polynomial on `[0,x]`. These are distribution identities, not new assumptions
about the path clocks.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Density of the sum of `n + 1` independent rate-one exponential waits. -/
noncomputable def erlangPDF (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x then ENNReal.ofReal (x ^ n * Real.exp (-x) / n.factorial) else 0

theorem gammaPDF_nat_succ (n : ℕ) (x : ℝ) :
    gammaPDF ((n : ℝ) + 1) 1 x = erlangPDF n x := by
  unfold gammaPDF gammaPDFReal erlangPDF
  split_ifs with hx
  · simp [Real.Gamma_nat_eq_factorial, Real.rpow_natCast]
    congr 1
    ring
  · simp

@[fun_prop] theorem measurable_erlangPDF (n : ℕ) : Measurable (erlangPDF n) := by
  have he : erlangPDF n = gammaPDF ((n : ℝ) + 1) 1 :=
    funext fun x => (gammaPDF_nat_succ n x).symm
  rw [he]
  change Measurable (fun x => ENNReal.ofReal (gammaPDFReal ((n : ℝ) + 1) 1 x))
  exact (measurable_gammaPDFReal _ _).ennreal_ofReal

theorem erlangPDF_zero (x : ℝ) : erlangPDF 0 x = exponentialPDF 1 x := by
  by_cases hx : 0 ≤ x <;> simp [erlangPDF, exponentialPDF_eq, hx]

private theorem erlang_integrand (n : ℕ) (x y : ℝ) :
    erlangPDF n y * erlangPDF 0 (-y + x) =
      (Set.Icc 0 x).indicator
        (fun y => ENNReal.ofReal (y ^ n * Real.exp (-x) / n.factorial)) y := by
  by_cases hy : 0 ≤ y
  · by_cases hx : y ≤ x
    · have hxy : 0 ≤ -y + x := by linarith
      rw [Set.indicator_of_mem (show y ∈ Set.Icc 0 x from ⟨hy, hx⟩)]
      simp only [erlangPDF, ite_eq_left hy, ite_eq_left hxy, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have he : Real.exp (-y) * Real.exp (-(-y + x)) = Real.exp (-x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = y ^ n * (Real.exp (-y) * Real.exp (-(-y + x))) / n.factorial := by ring
        _ = _ := by rw [he]
    · have hxy : ¬ 0 ≤ -y + x := by linarith
      simp [erlangPDF, hxy, Set.indicator_of_notMem, hx]
  · simp [erlangPDF, hy, Set.indicator_of_notMem]

private theorem erlang_polynomial_integral (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ y in Set.Icc 0 x, y ^ n * Real.exp (-x) / n.factorial) =
      x ^ (n + 1) * Real.exp (-x) / (n + 1).factorial := by
  rw [integral_div, integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem lconvolution_erlangPDF (n : ℕ) :
    erlangPDF n ⋆ₗ erlangPDF 0 = erlangPDF (n + 1) := by
  funext x
  rw [lconvolution_def]
  simp_rw [erlang_integrand]
  rw [lintegral_indicator measurableSet_Icc]
  by_cases hx : 0 ≤ x
  · have hi : IntegrableOn (fun y : ℝ => y ^ n * Real.exp (-x) / n.factorial)
        (Set.Icc 0 x) := by
      exact ((continuous_pow n).mul_const _ |>.div_const _).continuousOn.integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [erlang_polynomial_integral n hx]
      simp [erlangPDF, hx]
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact div_nonneg (mul_nonneg (pow_nonneg hy.1 _) (Real.exp_pos _).le)
        (Nat.cast_nonneg _)
  · have he : Set.Icc 0 x = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hx)
    simp [erlangPDF, hx]

theorem gammaMeasure_nat_succ_conv_exp (n : ℕ) :
    gammaMeasure ((n : ℝ) + 1) 1 ∗ clockLaw = gammaMeasure ((n : ℝ) + 2) 1 := by
  have h₁ : gammaMeasure ((n : ℝ) + 1) 1 = volume.withDensity (erlangPDF n) := by
    unfold gammaMeasure
    congr 1
    funext x
    exact gammaPDF_nat_succ _ x
  have h₀ : clockLaw = volume.withDensity (erlangPDF 0) := by
    simp only [clockLaw, expMeasure, gammaMeasure]
    congr 1
    funext x
    simpa using gammaPDF_nat_succ 0 x
  have h₂ : gammaMeasure ((n : ℝ) + 2) 1 = volume.withDensity (erlangPDF (n + 1)) := by
    have he : (n : ℝ) + 2 = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [he]
    unfold gammaMeasure
    congr 1
    funext x
    exact gammaPDF_nat_succ _ x
  rw [h₁, h₀, h₂,
    conv_withDensity_eq_lconvolution (measurable_erlangPDF n) (measurable_erlangPDF 0),
    lconvolution_erlangPDF]

/-- The sum of the first `m` waits at the root. -/
def clockSum (m : ℕ) (ω : Sample) : ℝ := ∑ i ∈ Finset.range m, ω ([], i)

@[fun_prop] theorem measurable_clockSum (m : ℕ) : Measurable (clockSum m) := by
  unfold clockSum
  fun_prop

theorem map_clockSum_succ (n : ℕ) :
    law.map (clockSum (n + 1)) = gammaMeasure ((n : ℝ) + 1) 1 := by
  induction n with
  | zero =>
    have he : clockSum 1 = (fun ω : Sample => ω ([], 0)) := by
      funext ω
      simp [clockSum]
    rw [he]
    simpa only [clockLaw, expMeasure, Nat.cast_zero, zero_add] using map_coordinate ([], 0)
  | succ n ih =>
    have hi : iIndepFun (fun i (ω : Sample) => ω ([], i)) law :=
      independent_clocks.precomp (by intro i j hij; simpa using hij)
    have h := hi.indepFun_finsetSum_of_notMem
      (fun i => measurable_pi_apply ([], i)) (by simp : n + 1 ∉ Finset.range (n + 1))
    have hs : (∑ j ∈ Finset.range (n + 1), fun ω : Sample => ω ([], j)) =
        clockSum (n + 1) := by
      funext ω
      simp [clockSum]
    rw [hs] at h
    have he : clockSum (n + 1 + 1) =
        clockSum (n + 1) + (fun ω : Sample => ω ([], n + 1)) := by
      funext ω
      exact Finset.sum_range_succ _ _
    rw [he, h.map_add_eq_map_conv_map (by fun_prop) (by fun_prop), ih, map_coordinate,
      gammaMeasure_nat_succ_conv_exp]
    congr 1
    push_cast
    ring

theorem map_clockSum_finite_sum (m : ℕ) :
    law.map (clockSum m) =
      (Measure.pi (fun _ : Fin m => clockLaw)).map (fun x => ∑ j, x j) := by
  have hi : iIndepFun (fun i : Fin m => fun ω : Sample => ω ([], i)) law :=
    independent_clocks.precomp (by intro i j hij; apply Fin.ext; simpa using hij)
  have hj : law.map (fun ω (i : Fin m) => ω ([], i)) =
      Measure.pi (fun _ : Fin m => clockLaw) := by
    rw [hi.map_fun_eq_pi_map (fun i : Fin m => (measurable_pi_apply ([], (i : ℕ))).aemeasurable)]
    simp only [map_coordinate]
  rw [← hj, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  exact Finset.sum_range _

/-- Actual path marginal, with the empty path explicitly excluded because its
law is a point mass rather than a Gamma measure of shape zero. -/
theorem map_birth_gamma {v : Vertex} (hv : v ≠ []) :
    law.map (fun ω => birth ω v) = gammaMeasure (rankSum v) 1 := by
  rw [map_birth_finite_sum, ← map_clockSum_finite_sum, pathCoordinates_length]
  have hp : 0 < rankSum v := by
    rw [rankSum_eq_length_add_sum]
    have hl : 0 < v.length := by
      cases v with
      | nil => exact (hv rfl).elim
      | cons i v => simp
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hn]
  simpa using map_clockSum_succ n

@[simp] theorem map_birth_nil : law.map (fun ω => birth ω []) = Measure.dirac 0 := by
  simp

end FreezingGrowth.PWIT
