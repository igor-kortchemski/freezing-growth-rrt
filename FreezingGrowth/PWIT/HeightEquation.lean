module

public import FreezingGrowth.PWIT.HeightBase
public import FreezingGrowth.PWIT.ClockIntegral

/-! The exponential first-birth renewal equation for actual height CDFs. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

/-- The whole-clock equation becomes the classical finite-time convolution. -/
theorem heightCDF_renewal (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    heightCDF (h + 1) t = Real.exp (-t) +
      ∫ s in (0 : ℝ)..t, Real.exp (-s) *
        heightCDF (h + 1) (t - s) * heightCDF h (t - s) := by
  let f : ℝ → ℝ := fun s => heightCDF (h + 1) (t - s) * heightCDF h (t - s)
  have hf : Integrable f clockLaw := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (heightCDF_nonneg _ _) (heightCDF_nonneg _ _))]
    simpa using mul_le_mul (heightCDF_le_one _ _) (heightCDF_le_one _ _)
      (heightCDF_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 1)
  have htail : (∫ s in Set.Ioi t, f s ∂clockLaw) = Real.exp (-t) := by
    calc
      _ = ∫ s in Set.Ioi t, (1 : ℝ) ∂clockLaw := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        have hs' : t - s ≤ 0 := by have := hs; change t < s at this; linarith
        simp [f, heightCDF_eq_one_of_nonpos _ hs']
      _ = clockLaw.real (Set.Ioi t) := by simp
      _ = Real.exp (-t) := clockLaw_real_Ioi ht
  have hsplit := integral_add_compl (μ := clockLaw) (f := f) (s := Set.Iic t) measurableSet_Iic hf
  rw [Set.compl_Iic, htail, setIntegral_clockLaw_Iic] at hsplit
  rw [heightCDF_firstBirth_integral]
  change (∫ s, f s ∂clockLaw) = _
  rw [← hsplit, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  dsimp [f]
  rw [add_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  ring

/-- Integrating-factor form for scalar uniqueness, with no pathwise maximum. -/
theorem heightCDF_renewal_integratingFactor (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    heightCDF (h + 1) t = Real.exp (-t) + Real.exp (-t) *
      ∫ u in (0 : ℝ)..t, Real.exp u * heightCDF (h + 1) u * heightCDF h u := by
  rw [heightCDF_renewal h ht, ← intervalIntegral.integral_const_mul]
  congr 1
  have hc := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => Real.exp (-t) * (Real.exp u *
      heightCDF (h + 1) u * heightCDF h u)) (a := (0 : ℝ)) (b := t) t
  simp only [sub_self, sub_zero] at hc
  rw [← hc]
  apply intervalIntegral.integral_congr
  intro s _
  have he : Real.exp (-t) * Real.exp (t - s) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-t) * Real.exp (t - s)) *
      heightCDF (h + 1) (t - s) * heightCDF h (t - s) := by rw [he]
    _ = _ := by ring

end FreezingGrowth.PWIT
