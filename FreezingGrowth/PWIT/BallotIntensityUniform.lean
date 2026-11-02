module

public import FreezingGrowth.PWIT.BallotIntensity

/-!
# Ballot intensity bounds at every positive depth

The short-depth case uses the raw intensity and the probability bound one.
It requires no enumeration and includes endpoint zero at depth one.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory

theorem nearLeadingProbability_le_one (d : ℕ) (A s : ℝ) :
    nearLeadingProbability d A s ≤ 1 := measureReal_le_one

theorem nearLeadingIntensityDensity_le_raw (d : ℕ) (A s : ℝ) :
    nearLeadingIntensityDensity d A s ≤ (generationEndpointDensity d s).toReal := by
  exact mul_le_of_le_one_left (by positivity) (nearLeadingProbability_le_one d A s)

theorem nearLeadingIntensityDensity_eq_zero_of_neg (d : ℕ) (A : ℝ) {s : ℝ} (hs : s < 0) :
    nearLeadingIntensityDensity d A s = 0 := by
  simp [nearLeadingIntensityDensity, generationEndpointDensity, not_le.mpr hs]

/-- A coarse exponential bound suffices for the finitely bounded depths. -/
theorem generationEndpointDensity_exp_upper {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) :
    (generationEndpointDensity d s).toReal ≤
      Real.exp 1 * Real.exp (Real.exp 1 * s - d) := by
  unfold generationEndpointDensity
  rw [ite_eq_left hs, ENNReal.toReal_ofReal (by positivity)]
  by_cases hd1 : d = 1
  · subst d
    norm_num only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have hp := mul_nonneg (Real.exp_pos 1).le hs
    linarith
  · have hm : 0 < d - 1 := by omega
    have hm1 : (1 : ℝ) ≤ (d - 1 : ℕ) := by exact_mod_cast (show 1 ≤ d - 1 from hm)
    have hroot : 1 ≤ Real.sqrt (d - 1 : ℕ) := Real.one_le_sqrt.mpr hm1
    have hbound := generation_intensity_exp_upper hm hs
    have hraw : s ^ (d - 1) / ((d - 1).factorial : ℝ) ≤
        Real.sqrt (d - 1 : ℕ) * (s ^ (d - 1) / ((d - 1).factorial : ℝ)) :=
      le_mul_of_one_le_left (by positivity) hroot
    apply (hraw.trans hbound).trans_eq
    rw [← Real.exp_add, Nat.cast_sub hd]
    congr 1
    norm_num
    ring

noncomputable def uniformBallotIntensityConstant : ℝ :=
  ballotIntensityConstant + 144 * Real.exp 1

theorem uniformBallotIntensityConstant_pos : 0 < uniformBallotIntensityConstant := by
  unfold uniformBallotIntensityConstant
  exact add_pos ballotIntensityConstant_pos (by positivity)

theorem nearLeadingIntensityDensity_exp_upper_uniform_nonneg {d : ℕ} (hd : 1 ≤ d)
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 ≤ s) :
    nearLeadingIntensityDensity d A s ≤ uniformBallotIntensityConstant * (1 + A ^ 6) /
      ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * s - d) := by
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hden : 0 < (d : ℝ) * Real.sqrt d := by positivity
  by_cases hlarge : 12 ≤ d
  · apply (nearLeadingIntensityDensity_exp_upper hlarge hA hs).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply div_le_div_of_nonneg_right _ hden.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact le_add_of_nonneg_right (by positivity)
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hd12 : (d : ℝ) ≤ 12 := by exact_mod_cast (by omega : d ≤ 12)
    have hsqrt : Real.sqrt (d : ℝ) ≤ d := Real.sqrt_le_self_iff.mpr (Or.inr hd1)
    have hden144 : (d : ℝ) * Real.sqrt d ≤ 144 := by
      calc
        _ ≤ (d : ℝ) * d := mul_le_mul_of_nonneg_left hsqrt hdp.le
        _ ≤ 144 := by nlinarith
    have hsmall : 144 * Real.exp 1 ≤ uniformBallotIntensityConstant := by
      exact le_add_of_nonneg_left ballotIntensityConstant_pos.le
    have hfactor : Real.exp 1 ≤ uniformBallotIntensityConstant * (1 + A ^ 6) /
        ((d : ℝ) * Real.sqrt d) := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ Real.exp 1 * 144 := mul_le_mul_of_nonneg_left hden144 (Real.exp_pos _).le
        _ ≤ uniformBallotIntensityConstant := by simpa only [mul_comm] using hsmall
        _ ≤ _ := le_mul_of_one_le_right uniformBallotIntensityConstant_pos.le
          (le_add_of_nonneg_right (pow_nonneg hA 6))
    exact ((nearLeadingIntensityDensity_le_raw d A s).trans
      (generationEndpointDensity_exp_upper hd hs)).trans
        (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le)

/-- Negative endpoints have zero intensity, so the bound holds on the whole
real line while retaining the exact zero-endpoint convention. -/
theorem nearLeadingIntensityDensity_exp_upper_uniform {d : ℕ} (hd : 1 ≤ d)
    {A : ℝ} (hA : 0 ≤ A) (s : ℝ) :
    nearLeadingIntensityDensity d A s ≤ uniformBallotIntensityConstant * (1 + A ^ 6) /
      ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * s - d) := by
  by_cases hs : 0 ≤ s
  · exact nearLeadingIntensityDensity_exp_upper_uniform_nonneg hd hA hs
  · simp only [nearLeadingIntensityDensity, generationEndpointDensity, ite_eq_right hs,
      ENNReal.toReal_zero, mul_zero]
    have hK := uniformBallotIntensityConstant_pos
    positivity

theorem integrableOn_nearLeadingIntensityDensity_Icc {d : ℕ} (hd : 1 ≤ d)
    {A : ℝ} (hA : 0 ≤ A) (u v : ℝ) :
    IntegrableOn (nearLeadingIntensityDensity d A) (Set.Icc u v) := by
  let B : ℝ := uniformBallotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
    Real.exp (Real.exp 1 * v - d)
  have hK := uniformBallotIntensityConstant_pos
  have hiB : IntegrableOn (fun _ : ℝ => B) (Set.Icc u v) :=
    continuous_const.integrableOn_Icc
  apply hiB.mono' (measurable_nearLeadingIntensityDensity d A).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (nearLeadingIntensityDensity_nonneg d A s)]
  apply (nearLeadingIntensityDensity_exp_upper_uniform hd hA s).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hs.2 (Real.exp_pos 1).le) _

theorem integrableOn_nearLeadingIntensityDensity_Ioc {d : ℕ} (hd : 1 ≤ d)
    {A : ℝ} (hA : 0 ≤ A) (u v : ℝ) :
    IntegrableOn (nearLeadingIntensityDensity d A) (Set.Ioc u v) :=
  (integrableOn_nearLeadingIntensityDensity_Icc hd hA u v).mono_set Set.Ioc_subset_Icc_self

/-- Uniform control for any real endpoint window of width at most one. In
particular, windows crossing zero need no separate truncation argument. -/
theorem integral_nearLeadingIntensityDensity_window_uniform {d : ℕ} (hd : 1 ≤ d)
    {A u v : ℝ} (hA : 0 ≤ A) (huv : u ≤ v) (hwidth : v - u ≤ 1) :
    (∫ s in Set.Icc u v, nearLeadingIntensityDensity d A s) ≤
      uniformBallotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
        Real.exp (Real.exp 1 * v - d) := by
  let B : ℝ := uniformBallotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
    Real.exp (Real.exp 1 * v - d)
  have hK := uniformBallotIntensityConstant_pos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (s : ℝ) (hs : s ∈ Set.Icc u v) : nearLeadingIntensityDensity d A s ≤ B := by
    apply (nearLeadingIntensityDensity_exp_upper_uniform hd hA s).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hs.2 (Real.exp_pos 1).le) _
  have hiB : IntegrableOn (fun _ : ℝ => B) (Set.Icc u v) :=
    continuous_const.integrableOn_Icc
  have hiD : IntegrableOn (nearLeadingIntensityDensity d A) (Set.Icc u v) :=
    integrableOn_nearLeadingIntensityDensity_Icc hd hA u v
  have hh : (∫ s in Set.Icc u v, nearLeadingIntensityDensity d A s) ≤
      ∫ _s in Set.Icc u v, B := by
    apply integral_mono_ae hiD hiB
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound s hs
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Icc_of_le huv] at hh
  exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hwidth hB)

theorem integral_nearLeadingIntensityDensity_Ioc_uniform {d : ℕ} (hd : 1 ≤ d)
    {A u v : ℝ} (hA : 0 ≤ A) (huv : u ≤ v) (hwidth : v - u ≤ 1) :
    (∫ s in Set.Ioc u v, nearLeadingIntensityDensity d A s) ≤
      uniformBallotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
        Real.exp (Real.exp 1 * v - d) := by
  rw [← integral_Icc_eq_integral_Ioc]
  exact integral_nearLeadingIntensityDensity_window_uniform hd hA huv hwidth

end FreezingGrowth.PWIT
