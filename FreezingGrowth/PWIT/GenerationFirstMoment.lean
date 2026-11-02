module

public import FreezingGrowth.PWIT.FirstMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual finite generation counts and the first-moment upper bound. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped Classical

theorem integral_rankBirthCount_density (d k : ℕ) {t : ℝ} (_ht : 0 ≤ t) :
    (∫ ω, rankBirthCount (d + 1) k t ω ∂law) =
      ∫ x in Set.Icc 0 t, (x ^ k / k.factorial) *
        (x ^ d * Real.exp (-x) / d.factorial) := by
  let a : ℝ := ((d + k : ℕ) : ℝ) + 1
  let : IsProbabilityMeasure (gammaMeasure a 1) :=
    isProbabilityMeasure_gammaMeasure (by dsimp [a]; positivity) (by norm_num)
  rw [integral_rankBirthCount_eq_choose (Nat.succ_pos d)]
  have hn : d + 1 + k - 1 = d + k := by omega
  have ha : ((d + 1 : ℕ) : ℝ) + k = a := by dsimp [a]; push_cast; ring
  rw [hn, ha, ← cdf_eq_real, cdf_gammaMeasure_eq_integral
    (by dsimp [a]; positivity) (by norm_num), ← integral_const_mul]
  have hf : (fun x => ((d + k).choose k : ℝ) * gammaPDFReal a 1 x) =
      (Set.Ici 0).indicator (fun x => (x ^ k / k.factorial) *
        (x ^ d * Real.exp (-x) / d.factorial)) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [Set.indicator_apply, Set.mem_Ici, ite_eq_left hx]
      exact rank_density_factor d k hx
    · simp [gammaPDFReal, hx]
  rw [hf, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hs : Set.Ici (0 : ℝ) ∩ Set.Iic t = Set.Icc 0 t := by ext x; simp
  rw [hs]

/-- Uniform first-moment bound for every finite excess-rank cutoff. -/
theorem sum_integral_rankBirthCount_le (d M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range M, ∫ ω, rankBirthCount (d + 1) k t ω ∂law) ≤
      t ^ (d + 1) / (d + 1).factorial := by
  simp_rw [integral_rankBirthCount_density d _ ht]
  have hi (k : ℕ) : IntegrableOn (fun x : ℝ => (x ^ k / k.factorial) *
      (x ^ d * Real.exp (-x) / d.factorial)) (Set.Icc 0 t) :=
    (by fun_prop : Continuous (fun x : ℝ => (x ^ k / k.factorial) *
      (x ^ d * Real.exp (-x) / d.factorial))).integrableOn_Icc
  rw [← integral_finsetSum _ (fun k _ => hi k)]
  have hp : IntegrableOn (fun x : ℝ => x ^ d / d.factorial) (Set.Icc 0 t) :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ d / d.factorial)).integrableOn_Icc
  calc
    _ ≤ ∫ x in Set.Icc 0 t, x ^ d / d.factorial := by
      apply integral_mono_ae (integrable_finsetSum _ (fun k _ => hi k)) hp
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [← Finset.sum_mul]
      have hx0 : (0 : ℝ) ≤ x := hx.1
      have hh := mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg hx0 M)
        (by positivity : 0 ≤ x ^ d * Real.exp (-x) / (d.factorial : ℝ))
      apply hh.trans_eq
      have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
      calc
        _ = (x ^ d / (d.factorial : ℝ)) * (Real.exp x * Real.exp (-x)) := by ring
        _ = _ := by rw [he, mul_one]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const, integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero d), sub_zero, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp

/-- Rank slices recover the total generation intensity without an assumed
branching-process counting formula. -/
theorem hasSum_integral_rankBirthCount (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun k => ∫ ω, rankBirthCount (d + 1) k t ω ∂law)
      (t ^ (d + 1) / (d + 1).factorial) := by
  let F (M : ℕ) (x : ℝ) := (∑ k ∈ Finset.range M, x ^ k / k.factorial) *
    (x ^ d * Real.exp (-x) / d.factorial)
  let G (x : ℝ) := x ^ d / d.factorial
  have hF (M : ℕ) : Continuous (F M) := by dsimp [F]; fun_prop
  have hbound (M : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 t) :
      0 ≤ F M x ∧ F M x ≤ G x := by
    have hx0 : 0 ≤ x := hx.1
    have hn : 0 ≤ x ^ d * Real.exp (-x) / (d.factorial : ℝ) := by positivity
    refine ⟨mul_nonneg (Finset.sum_nonneg (fun k _ => by positivity)) hn, ?_⟩
    have hh := mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg hx0 M) hn
    apply hh.trans_eq
    have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    dsimp [G]
    calc
      _ = (x ^ d / (d.factorial : ℝ)) * (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [he, mul_one]
  have hlim : Filter.Tendsto (fun M => ∫ x in Set.Icc 0 t, F M x) Filter.atTop
      (nhds (∫ x in Set.Icc 0 t, G x)) := by
    apply tendsto_integral_filter_of_norm_le_const
      (Filter.Eventually.of_forall (fun M => (hF M).aestronglyMeasurable.restrict))
    · refine ⟨t ^ d / (d.factorial : ℝ), Filter.Eventually.of_forall (fun M => ?_)⟩
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound M x hx).1]
      exact (hbound M x hx).2.trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hx.2 d) (by positivity))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hs := (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat.mul_const
        (x ^ d * Real.exp (-x) / d.factorial)
      have he : Real.exp x * (x ^ d * Real.exp (-x) / d.factorial) = G x := by
        have hh : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
        dsimp [G]
        calc
          _ = (x ^ d / (d.factorial : ℝ)) * (Real.exp x * Real.exp (-x)) := by ring
          _ = _ := by rw [hh, mul_one]
      rw [← Real.exp_eq_exp_ℝ] at hs
      simpa only [he] using hs
  have he (M : ℕ) : (∑ k ∈ Finset.range M, ∫ ω, rankBirthCount (d + 1) k t ω ∂law) =
      ∫ x in Set.Icc 0 t, F M x := by
    simp_rw [integral_rankBirthCount_density d _ ht]
    rw [← integral_finsetSum]
    · congr 1
      funext x
      dsimp [F]
      rw [Finset.sum_mul]
    · intro k hk
      exact (by fun_prop : Continuous (fun x : ℝ => (x ^ k / k.factorial) *
        (x ^ d * Real.exp (-x) / d.factorial))).integrableOn_Icc
  have hval : (∫ x in Set.Icc 0 t, G x) = t ^ (d + 1) / (d + 1).factorial := by
    dsimp [G]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero d), sub_zero, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hlim' := hlim.congr' (Filter.Eventually.of_forall (fun M => (he M).symm))
  rw [hval] at hlim'
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => integral_nonneg (fun ω => Finset.sum_nonneg
      (fun v _ => Set.indicator_nonneg (fun _ _ => by norm_num) ω))) _).mpr
  exact hlim'

end FreezingGrowth.PWIT
