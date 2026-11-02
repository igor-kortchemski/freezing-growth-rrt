module

public import FreezingGrowth.PWIT.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Density and interval integrals for the actual rate-one clock. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Integration against the actual exponential law, with its support explicit. -/
theorem integral_clockLaw (f : ℝ → ℝ) :
    (∫ s, f s ∂clockLaw) = ∫ s in Set.Ici 0, Real.exp (-s) * f s := by
  have hμ : clockLaw = volume.withDensity (exponentialPDF 1) := rfl
  have hpdf : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [hμ, integral_withDensity_eq_integral_toReal_smul hpdf
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun s => (exponentialPDF 1 s).toReal • f s) =
      (Set.Ici 0).indicator (fun s => Real.exp (-s) * f s) := by
    funext s
    by_cases hs : 0 ≤ s
    · simp [exponentialPDF_eq, hs, Real.exp_nonneg]
    · simp [exponentialPDF_eq, hs]
  rw [he, integral_indicator measurableSet_Ici]

/-- Restricting the clock above by t yields an ordinary integral on [0,t]. -/
theorem setIntegral_clockLaw_Iic (f : ℝ → ℝ) (t : ℝ) :
    (∫ s in Set.Iic t, f s ∂clockLaw) =
      ∫ s in Set.Icc 0 t, Real.exp (-s) * f s := by
  rw [← integral_indicator measurableSet_Iic, integral_clockLaw]
  have he : (fun s => Real.exp (-s) * (Set.Iic t).indicator f s) =
      (Set.Iic t).indicator (fun s => Real.exp (-s) * f s) := by
    funext s
    by_cases hs : s ∈ Set.Iic t <;> simp [hs]
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hs : Set.Iic t ∩ Set.Ici 0 = Set.Icc 0 t := by ext s; simp [and_comm]
  rw [hs]

theorem clockLaw_real_Ioi {t : ℝ} (ht : 0 ≤ t) :
    clockLaw.real (Set.Ioi t) = Real.exp (-t) := by
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real]
  simp [clockLaw, cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1), ht]

end FreezingGrowth.PWIT
