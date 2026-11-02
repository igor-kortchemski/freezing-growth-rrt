module

public import FreezingGrowth.PWIT.OverlapIntegral
public import FreezingGrowth.PWIT.OverlapProduct

/-! Actual critical-window overlap bounds. The two sibling ranks have already
been summed in the actual pair law before applying the three ballot factors. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal

theorem lintegral_suffix_ballot_density_le {q : ℕ} (hq : 0 < q)
    {A : ℝ} (hA : 0 ≤ A) (m S : ℝ) :
    (∫⁻ U in Ioc (m - 1 - S) (m - S), ENNReal.ofReal (nearLeadingIntensityDensity q A U)) ≤
      ENNReal.ofReal (ballotExponentialEnvelope uniformBallotIntensityConstant q A (m - S)) := by
  have hi := integrableOn_nearLeadingIntensityDensity_Ioc hq hA (m - 1 - S) (m - S)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (nearLeadingIntensityDensity_nonneg q A))]
  apply ENNReal.ofReal_le_ofReal
  exact integral_nearLeadingIntensityDensity_Ioc_uniform hq hA (by linarith) (by linarith)

noncomputable def overlapMomentConstant : ℝ :=
  uniformBallotIntensityConstant ^ 3 * threeBallotIntegralConstant

theorem overlapMomentConstant_pos : 0 < overlapMomentConstant :=
  mul_pos (pow_pos uniformBallotIntensityConstant_pos 3) threeBallotIntegralConstant_pos

theorem overlapIntensity_critical_le {j q : ℕ} (hj : 0 < j) (hq : 0 < q) :
    overlapIntensity j q
      (endpointLeadingVectorEvent (j + q) (Ioc (timeCenter (j + q) - 1) (timeCenter (j + q))) ×ˢ
        endpointLeadingVectorEvent (j + q) (Ioc (timeCenter (j + q) - 1) (timeCenter (j + q)))) ≤
      ENNReal.ofReal (overlapMomentConstant * threeFactorDepthWeight j q) := by
  let m := timeCenter (j + q)
  let U := uniformBallotIntensityConstant
  let a : ℝ := (j : ℝ) * m / (j + q : ℕ) - 1
  let T : Set ℝ := {S | 0 ≤ S ∧ 0 ≤ overlapAllowance j q m S}
  let F : ℝ → ℝ := fun S =>
    ballotExponentialEnvelope U j (S - (j : ℝ) * m / (j + q : ℕ) + 1) S *
      ballotExponentialEnvelope U q (S - (j : ℝ) * m / (j + q : ℕ) + 1) (m - S) ^ 2
  have hU : 0 ≤ U := uniformBallotIntensityConstant_pos.le
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hA (S : ℝ) : overlapAllowance j q m S = S - (j : ℝ) * m / (j + q : ℕ) + 1 := by
    unfold overlapAllowance
    ring
  have hT : MeasurableSet T := measurableSet_Ici.inter
    (measurableSet_le measurable_const (measurable_overlapAllowance j q m))
  have hsub : T ⊆ Ici a := by
    intro S hS
    change 0 ≤ S ∧ 0 ≤ overlapAllowance j q m S at hS
    rw [hA S] at hS
    change (j : ℝ) * m / (j + q : ℕ) - 1 ≤ S
    linarith [hS.2]
  have hFn (S : ℝ) : 0 ≤ F S := by
    dsimp [F]
    exact mul_nonneg (ballotExponentialEnvelope_nonneg hU hjr.le _ _) (sq_nonneg _)
  have hm : Real.exp 1 * m = (j : ℝ) + q + (3 / 2 : ℝ) * Real.log ((j : ℝ) + q) := by
    simpa only [m, Nat.cast_add] using exp_mul_timeCenter (j + q)
  have hiF : IntegrableOn F (Ici a) := by
    simpa only [F, a, Nat.cast_add] using integrableOn_three_ballot_product_Ici hjr hqr hm U
  have hbound : (∫ S in Ici a, F S) ≤
      U ^ 3 * threeFactorDepthWeight j q * threeBallotIntegralConstant := by
    exact integral_three_ballot_product_timeCenter_Ici_le hj hq hU
  calc
    _ ≤ ∫⁻ S in T,
        ENNReal.ofReal (nearLeadingIntensityDensity j (overlapAllowance j q m S) S) *
          (∫⁻ V in Ioc (m - 1 - S) (m - S),
            ENNReal.ofReal (nearLeadingIntensityDensity q (overlapAllowance j q m S) V)) ^ 2 :=
      overlapIntensity_endpointLeading_le hj hq m
    _ ≤ ∫⁻ S in T, ENNReal.ofReal (F S) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hT] with S hS
      have hd := ENNReal.ofReal_le_ofReal
        (nearLeadingIntensityDensity_exp_upper_uniform hj hS.2 S)
      have hw := lintegral_suffix_ballot_density_le hq hS.2 m S
      have hp := mul_le_mul' hd (pow_le_pow_left₀ (by positivity) hw 2)
      apply hp.trans_eq
      dsimp [F, U]
      rw [hA S]
      rw [ENNReal.ofReal_mul (ballotExponentialEnvelope_nonneg
        uniformBallotIntensityConstant_pos.le hjr.le _ _),
        ENNReal.ofReal_pow (ballotExponentialEnvelope_nonneg
          uniformBallotIntensityConstant_pos.le hqr.le _ _) 2]
      rfl
    _ ≤ ∫⁻ S in Ici a, ENNReal.ofReal (F S) := lintegral_mono_set hsub
    _ = ENNReal.ofReal (∫ S in Ici a, F S) :=
      (ofReal_integral_eq_lintegral_ofReal hiF (Filter.Eventually.of_forall hFn)).symm
    _ ≤ ENNReal.ofReal (U ^ 3 * threeFactorDepthWeight j q * threeBallotIntegralConstant) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = _ := by unfold overlapMomentConstant; congr 1; dsimp [U]; ring

theorem extendedOverlapIntensity_critical_le {j q : ℕ} (hj : 0 < j) (hq : 0 < q) :
    extendedOverlapIntensity j q
      (((restrictSequence (j + q)) ⁻¹'
        endpointLeadingVectorEvent (j + q) (Ioc (timeCenter (j + q) - 1) (timeCenter (j + q)))) ×ˢ
       ((restrictSequence (j + q)) ⁻¹'
        endpointLeadingVectorEvent (j + q) (Ioc (timeCenter (j + q) - 1) (timeCenter (j + q))))) ≤
      ENNReal.ofReal (overlapMomentConstant * threeFactorDepthWeight j q) := by
  rw [extendedOverlapIntensity_preimage_restrict j q
    (measurableSet_endpointLeadingVectorEvent _ measurableSet_Ioc)]
  exact overlapIntensity_critical_le hj hq

end FreezingGrowth.PWIT
