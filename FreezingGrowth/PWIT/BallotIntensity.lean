module

public import FreezingGrowth.PWIT.GenerationBridge
public import FreezingGrowth.PWIT.BallotDensity
public import FreezingGrowth.PWIT.SimplexNearLeading

/-! Combining the actual simplex ballot probability with the generation
endpoint intensity. The density at nonpositive endpoints is kept explicit. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

noncomputable def nearLeadingProbability (d : ℕ) (A s : ℝ) : ℝ :=
  (simplexLaw d).real {p | vectorLeading A (s • p)}

@[fun_prop] theorem measurable_nearLeadingProbability_joint (d : ℕ) :
    Measurable (fun z : ℝ × ℝ => nearLeadingProbability d z.1 z.2) := by
  have hS : MeasurableSet
      {z : (ℝ × ℝ) × (Fin d → ℝ) | vectorLeading z.1.1 (z.1.2 • z.2)} :=
    (measurableSet_vectorLeading_joint d).preimage
      (show Measurable (fun z : (ℝ × ℝ) × (Fin d → ℝ) => (z.1.1, z.1.2 • z.2)) by fun_prop)
  exact (measurable_measure_prodMk_left (ν := simplexLaw d) hS).ennreal_toReal

@[fun_prop] theorem measurable_nearLeadingProbability (d : ℕ) (A : ℝ) :
    Measurable (nearLeadingProbability d A) := by
  have hS : MeasurableSet {z : ℝ × (Fin d → ℝ) | vectorLeading A (z.1 • z.2)} :=
    (measurableSet_vectorLeading d A).preimage (by fun_prop)
  exact (measurable_measure_prodMk_left (ν := simplexLaw d) hS).ennreal_toReal

noncomputable def nearLeadingIntensityDensity (d : ℕ) (A s : ℝ) : ℝ :=
  nearLeadingProbability d A s * (generationEndpointDensity d s).toReal

@[fun_prop] theorem measurable_nearLeadingIntensityDensity (d : ℕ) (A : ℝ) :
    Measurable (nearLeadingIntensityDensity d A) :=
  (measurable_nearLeadingProbability d A).mul
    (measurable_generationEndpointDensity d).ennreal_toReal

@[fun_prop] theorem measurable_nearLeadingIntensityDensity_joint (d : ℕ) :
    Measurable (fun z : ℝ × ℝ => nearLeadingIntensityDensity d z.1 z.2) :=
  (measurable_nearLeadingProbability_joint d).mul
    ((measurable_generationEndpointDensity d).ennreal_toReal.comp measurable_snd)

theorem nearLeadingIntensityDensity_nonneg (d : ℕ) (A s : ℝ) :
    0 ≤ nearLeadingIntensityDensity d A s := by
  unfold nearLeadingIntensityDensity nearLeadingProbability
  positivity

noncomputable def ballotIntensityConstant : ℝ := simplexNearLeadingConstant * ballotDensityConstant

theorem ballotIntensityConstant_pos : 0 < ballotIntensityConstant :=
  mul_pos simplexNearLeadingConstant_pos ballotDensityConstant_pos

theorem nearLeadingIntensityDensity_exp_upper {d : ℕ} (hd : 12 ≤ d) {A s : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) :
    nearLeadingIntensityDensity d A s ≤ ballotIntensityConstant * (1 + A ^ 6) /
      ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * s - d) := by
  by_cases hsp : 0 < s
  · have hprob := simplex_nearLeading_bound (n := d) (by omega) hA hsp
    have hscaled := mul_le_mul_of_nonneg_right hprob
      (by positivity : 0 ≤ s ^ (d - 1) / ((d - 1).factorial : ℝ))
    have he : (simplexNearLeadingConstant * (1 + (A * d / s) ^ 6) / d) *
        (s ^ (d - 1) / ((d - 1).factorial : ℝ)) =
        simplexNearLeadingConstant * ballotPolynomial d A s := by
      rw [ballotPolynomial_eq (by omega) A hsp]
      ring
    rw [he] at hscaled
    have hpoly := mul_le_mul_of_nonneg_left (ballotPolynomial_exp_upper hd hA hs)
      simplexNearLeadingConstant_pos.le
    unfold nearLeadingIntensityDensity nearLeadingProbability generationEndpointDensity
    rw [ite_eq_left hs, ENNReal.toReal_ofReal (by positivity)]
    exact hscaled.trans (hpoly.trans_eq (by unfold ballotIntensityConstant; ring))
  · have hz : s = 0 := le_antisymm (le_of_not_gt hsp) hs
    have he : d - 1 ≠ 0 := by omega
    subst s
    simp only [nearLeadingIntensityDensity, generationEndpointDensity, le_refl, ite_true,
      zero_pow he, zero_div, ENNReal.ofReal_zero, ENNReal.toReal_zero, mul_zero]
    have hK := ballotIntensityConstant_pos
    positivity

/-- Integrating over any nonnegative endpoint window of width at most one
preserves the uniform density bound at the upper endpoint. -/
theorem integral_nearLeadingIntensityDensity_window {d : ℕ} (hd : 12 ≤ d)
    {A u v : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) (huv : u ≤ v) (hwidth : v - u ≤ 1) :
    (∫ s in Set.Icc u v, nearLeadingIntensityDensity d A s) ≤
      ballotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
        Real.exp (Real.exp 1 * v - d) := by
  let B : ℝ := ballotIntensityConstant * (1 + A ^ 6) / ((d : ℝ) * Real.sqrt d) *
    Real.exp (Real.exp 1 * v - d)
  have hK := ballotIntensityConstant_pos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (s : ℝ) (hs : s ∈ Set.Icc u v) : nearLeadingIntensityDensity d A s ≤ B := by
    apply (nearLeadingIntensityDensity_exp_upper hd hA (hu.trans hs.1)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hs.2 (Real.exp_pos 1).le
    linarith
  have hiB : IntegrableOn (fun _ : ℝ => B) (Set.Icc u v) :=
    continuous_const.integrableOn_Icc
  have hiD : IntegrableOn (nearLeadingIntensityDensity d A) (Set.Icc u v) := by
    apply hiB.mono' (measurable_nearLeadingIntensityDensity d A).aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (nearLeadingIntensityDensity_nonneg d A s)]
    exact hbound s hs
  have hh : (∫ s in Set.Icc u v, nearLeadingIntensityDensity d A s) ≤
      ∫ _s in Set.Icc u v, B := by
    apply integral_mono_ae hiD hiB
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound s hs
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Icc_of_le huv] at hh
  exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hwidth hB)

end FreezingGrowth.PWIT
