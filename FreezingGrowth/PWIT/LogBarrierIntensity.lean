module

public import FreezingGrowth.PWIT.OverlapIntegral
public import FreezingGrowth.PWIT.PolynomialBallotDensity
public import FreezingGrowth.PWIT.LogBarrierBounds
public import FreezingGrowth.PWIT.SimplexCyclicBarrier

/-! Actual all-rank logarithmic-barrier intensities. The canonical simplex
estimate is an explicit input; the generation measure and its endpoint
transport are the actual PWIT measures already constructed. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal Classical

/-- The canonical estimate needed by the intensity adapter. -/
def LogSimplexBound (C : ℝ) : Prop :=
  ∀ (d : ℕ) [NeZero d] (A c : ℝ), 0 ≤ A → 0 ≤ c →
    (simplexLaw d).real {p | softBridge (logBarrierAllowance A c) (simplexCenteredBridge p)} ≤
      C * (1 + A + c) ^ 14 / d

def logVectorBarrier {d : ℕ} [NeZero d] (A c : ℝ) (x : Fin d → ℝ) : Prop :=
  softBridge (logBarrierAllowance A c) (centeredBridge x)

theorem measurableSet_logVectorBarrier (d : ℕ) [NeZero d] (A c : ℝ) :
    MeasurableSet {x : Fin d → ℝ | logVectorBarrier A c x} :=
  measurableSet_softBridge _ measurable_centeredBridge

/-- Scaling the actual increment vector scales both barrier coefficients. -/
theorem logVectorBarrier_scaled_iff {d : ℕ} [NeZero d] (A c : ℝ)
    {s : ℝ} (hs : 0 < s) (p : Fin d → ℝ) :
    logVectorBarrier A c (s • p) ↔
      softBridge (logBarrierAllowance (A * d / s) (c * d / s)) (simplexCenteredBridge p) := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  unfold logVectorBarrier softBridge simplexCenteredBridge
  rw [centeredBridge_smul, centeredBridge_smul]
  apply forall_congr'
  intro r
  simp only [Pi.smul_apply, smul_eq_mul, logBarrierAllowance]
  have he : -(A * (d : ℝ) / s + c * d / s *
      Real.log ((min r.val (d - r.val) : ℕ) + 1 : ℝ)) =
      (d / s) * -(A + c * Real.log ((min r.val (d - r.val) : ℕ) + 1 : ℝ)) := by ring
  rw [he]
  have hr : (d : ℝ) * centeredBridge p r - d * centeredBridge p 0 =
      (d / s) * (s * centeredBridge p r - s * centeredBridge p 0) := by field_simp
  rw [hr]
  exact (mul_le_mul_iff_right₀ (div_pos hd hs)).symm

noncomputable def logBarrierProbability (d : ℕ) [NeZero d] (A c s : ℝ) : ℝ :=
  (simplexLaw d).real {p | logVectorBarrier A c (s • p)}

@[fun_prop] theorem measurable_logBarrierProbability (d : ℕ) [NeZero d] (A c : ℝ) :
    Measurable (logBarrierProbability d A c) := by
  have hS : MeasurableSet {z : ℝ × (Fin d → ℝ) | logVectorBarrier A c (z.1 • z.2)} :=
    (measurableSet_logVectorBarrier d A c).preimage (by fun_prop)
  exact (measurable_measure_prodMk_left (ν := simplexLaw d) hS).ennreal_toReal

noncomputable def logBarrierIntensityDensity (d : ℕ) [NeZero d] (A c s : ℝ) : ℝ :=
  logBarrierProbability d A c s * (generationEndpointDensity d s).toReal

@[fun_prop] theorem measurable_logBarrierIntensityDensity (d : ℕ) [NeZero d] (A c : ℝ) :
    Measurable (logBarrierIntensityDensity d A c) :=
  (measurable_logBarrierProbability d A c).mul
    (measurable_generationEndpointDensity d).ennreal_toReal

theorem logBarrierIntensityDensity_nonneg (d : ℕ) [NeZero d] (A c s : ℝ) :
    0 ≤ logBarrierIntensityDensity d A c s := by
  unfold logBarrierIntensityDensity logBarrierProbability
  positivity

private theorem one_add_pow_fourteen {z : ℝ} (hz : 0 ≤ z) :
    (1 + z) ^ 14 ≤ (2 : ℝ) ^ 14 * (1 + z ^ 14) := by
  by_cases hz1 : z ≤ 1
  · have hp : (1 + z) ^ 14 ≤ (2 : ℝ) ^ 14 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 14
    exact hp.trans (le_mul_of_one_le_right (by positivity) (by have := pow_nonneg hz 14; linarith))
  · have hp : (1 + z) ^ 14 ≤ (2 * z) ^ 14 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 14
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

noncomputable def logBarrierIntensityConstant (C : ℝ) : ℝ :=
  C * (2 : ℝ) ^ 14 * degreeBallotDensityConstant 14

theorem logBarrierIntensityDensity_exp_upper {C : ℝ} (hC : 0 ≤ C)
    (hsoft : LogSimplexBound C) {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c s : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hs : 0 ≤ s) :
    logBarrierIntensityDensity d A c s ≤
      logBarrierIntensityConstant C * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * s - d) := by
  by_cases hsp : 0 < s
  · have hprob := hsoft d (A * d / s) (c * d / s) (by positivity) (by positivity)
    have hevent : {p : Fin d → ℝ | logVectorBarrier A c (s • p)} =
        {p | softBridge (logBarrierAllowance (A * d / s) (c * d / s)) (simplexCenteredBridge p)} := by
      ext p
      exact logVectorBarrier_scaled_iff A c hsp p
    have hp : logBarrierProbability d A c s ≤
        C * (2 : ℝ) ^ 14 * (1 + ((A + c) * d / s) ^ 14) / d := by
      unfold logBarrierProbability
      rw [hevent]
      apply hprob.trans
      have hpow := one_add_pow_fourteen (show 0 ≤ (A + c) * d / s by positivity)
      have he : 1 + A * (d : ℝ) / s + c * d / s = 1 + (A + c) * d / s := by ring
      rw [he]
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hC) (Nat.cast_nonneg d)
    have hscaled := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ s ^ (d - 1) / ((d - 1).factorial : ℝ))
    have he : (C * (2 : ℝ) ^ 14 * (1 + ((A + c) * d / s) ^ 14) / d) *
        (s ^ (d - 1) / ((d - 1).factorial : ℝ)) =
        (C * (2 : ℝ) ^ 14) * degreeBallotPolynomial 14 d (A + c) s := by
      rw [degreeBallotPolynomial_eq 14 (by omega) (A + c) hsp]
      ring
    rw [he] at hscaled
    have hpoly := mul_le_mul_of_nonneg_left
      (degreeBallotPolynomial_exp_upper 14 hd (add_nonneg hA hc) hs)
      (show 0 ≤ C * (2 : ℝ) ^ 14 by positivity)
    unfold logBarrierIntensityDensity generationEndpointDensity
    rw [ite_eq_left hs, ENNReal.toReal_ofReal (by positivity)]
    exact hscaled.trans (hpoly.trans_eq (by unfold logBarrierIntensityConstant; ring))
  · have hz : s = 0 := le_antisymm (le_of_not_gt hsp) hs
    have he : d - 1 ≠ 0 := by omega
    subst s
    simp only [logBarrierIntensityDensity, generationEndpointDensity, le_refl, ite_true,
      zero_pow he, zero_div, ENNReal.ofReal_zero, ENNReal.toReal_zero, mul_zero]
    have hK := degreeBallotDensityConstant_pos 14
    unfold logBarrierIntensityConstant
    positivity

def logBarrierVectorEvent (d : ℕ) [NeZero d] (A c : ℝ) (J : Set ℝ) : Set (Fin d → ℝ) :=
  {x | totalWait x ∈ J ∧ logVectorBarrier A c x}

theorem measurableSet_logBarrierVectorEvent (d : ℕ) [NeZero d] (A c : ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) : MeasurableSet (logBarrierVectorEvent d A c J) :=
  (hJ.preimage (measurable_totalWait d)).inter (measurableSet_logVectorBarrier d A c)

theorem ofReal_logBarrierIntensityDensity (d : ℕ) [NeZero d] (A c s : ℝ) :
    ENNReal.ofReal (logBarrierIntensityDensity d A c s) =
      simplexLaw d {p | logVectorBarrier A c (s • p)} * generationEndpointDensity d s := by
  unfold logBarrierIntensityDensity logBarrierProbability
  rw [ENNReal.ofReal_mul measureReal_nonneg]
  change ENNReal.ofReal ((simplexLaw d {p | logVectorBarrier A c (s • p)}).toReal) *
    ENNReal.ofReal (generationEndpointDensity d s).toReal = _
  rw [ENNReal.ofReal_toReal (measure_ne_top (simplexLaw d) {p | logVectorBarrier A c (s • p)})]
  congr 1
  apply ENNReal.ofReal_toReal
  unfold generationEndpointDensity
  split_ifs <;> simp

/-- Exact all-rank generation transport, retaining the unnormalized endpoint measure. -/
theorem generationIncrementIntensity_logBarrierVectorEvent (d : ℕ) [NeZero d]
    (A c : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    generationIncrementIntensity d (logBarrierVectorEvent d A c J) =
      ∫⁻ s in J, ENNReal.ofReal (logBarrierIntensityDensity d A c s) := by
  let E := logBarrierVectorEvent d A c J
  have hE : MeasurableSet E := measurableSet_logBarrierVectorEvent d A c hJ
  have hF : Measurable (E.indicator (1 : (Fin d → ℝ) → ℝ≥0∞)) := measurable_one.indicator hE
  rw [generationIncrementIntensity_eq, positiveOrthantVolume_eq_scaled_simplex,
    ← lintegral_indicator_one hE, lintegral_map hF (by fun_prop),
    lintegral_prod_symm _ (by fun_prop)]
  have hinner (s : ℝ) : (∫⁻ p, E.indicator (1 : (Fin d → ℝ) → ℝ≥0∞) (s • p) ∂simplexLaw d) =
      J.indicator (fun s => simplexLaw d {p | logVectorBarrier A c (s • p)}) s := by
    have he : (fun p => E.indicator (1 : (Fin d → ℝ) → ℝ≥0∞) (s • p)) =ᵐ[simplexLaw d]
        if s ∈ J then {p | logVectorBarrier A c (s • p)}.indicator 1 else 0 := by
      filter_upwards [simplexLaw_ae_nonnegative_sum_one d] with p hp
      have ht : totalWait (s • p) = s := by
        rw [totalWait_smul]
        change s * (∑ i, p i) = s
        rw [hp.2, mul_one]
      simp only [E, logBarrierVectorEvent, Set.indicator_apply, Set.mem_ofPred_eq, ht,
        Pi.one_apply]
      split_ifs <;> simp_all
    rw [lintegral_congr_ae he]
    by_cases hs : s ∈ J
    · have hscaled : MeasurableSet {p : Fin d → ℝ | logVectorBarrier A c (s • p)} :=
        (measurableSet_logVectorBarrier d A c).preimage
          (show Measurable (fun p : Fin d → ℝ => s • p) by fun_prop)
      rw [ite_eq_left hs, Set.indicator_of_mem hs]
      exact lintegral_indicator_one hscaled
    · simp [hs]
  dsimp only
  simp_rw [hinner]
  unfold generationEndpointMeasure
  have hscaledJoint : MeasurableSet
      {z : ℝ × (Fin d → ℝ) | logVectorBarrier A c (z.1 • z.2)} :=
    (measurableSet_logVectorBarrier d A c).preimage
      (show Measurable (fun z : ℝ × (Fin d → ℝ) => z.1 • z.2) by fun_prop)
  have hm : Measurable (fun s => simplexLaw d {p | logVectorBarrier A c (s • p)}) :=
    measurable_measure_prodMk_left hscaledJoint
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_generationEndpointDensity d)
    (hm.indicator hJ), ← lintegral_indicator hJ]
  apply lintegral_congr
  intro s
  change generationEndpointDensity d s *
    J.indicator (fun s => simplexLaw d {p | logVectorBarrier A c (s • p)}) s =
      J.indicator (fun s => ENNReal.ofReal (logBarrierIntensityDensity d A c s)) s
  by_cases hs : s ∈ J
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, ofReal_logBarrierIntensityDensity]
    exact mul_comm _ _
  · simp only [Set.indicator_of_notMem hs, mul_zero]

/-- The scalar exponential integral used after endpoint disintegration. -/
theorem integral_exp_generation_bound (d : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in Icc 0 b, Real.exp (Real.exp 1 * s - d)) ≤
      Real.exp (Real.exp 1 * b - d) / Real.exp 1 := by
  have hderiv (s : ℝ) : HasDerivAt
      (fun s : ℝ => Real.exp (Real.exp 1 * s - d) / Real.exp 1)
      (Real.exp (Real.exp 1 * s - d)) s := by
    convert ((((hasDerivAt_id s).const_mul (Real.exp 1)).sub_const (d : ℝ)).exp).div_const
      (Real.exp 1) using 1 <;> simp [Real.exp_ne_zero]
  have hi : IntervalIntegrable (fun s : ℝ => Real.exp (Real.exp 1 * s - d)) volume 0 b :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (Real.exp 1 * s - d))).intervalIntegrable 0 b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hi
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb, he]
  have hh : 0 ≤ Real.exp (Real.exp 1 * 0 - (d : ℝ)) / Real.exp 1 := by positivity
  linarith

theorem logBarrierIntensityDensity_integrable_Icc {C : ℝ} (hC : 0 ≤ C)
    (hsoft : LogSimplexBound C) {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) :
    IntegrableOn (logBarrierIntensityDensity d A c) (Icc 0 b) := by
  let B : ℝ := logBarrierIntensityConstant C * (1 + (A + c) ^ 14) /
    ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)
  have hiB : IntegrableOn (fun _ : ℝ => B) (Icc 0 b) :=
    continuous_const.integrableOn_Icc
  apply hiB.mono' (measurable_logBarrierIntensityDensity d A c).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (logBarrierIntensityDensity_nonneg d A c s)]
  apply (logBarrierIntensityDensity_exp_upper hC hsoft hd hA hc hs.1).trans
  have hK := degreeBallotDensityConstant_pos 14
  have hfac : 0 ≤ logBarrierIntensityConstant C * (1 + (A + c) ^ 14) /
      ((d : ℝ) * Real.sqrt d) := by unfold logBarrierIntensityConstant; positivity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hs.2 (Real.exp_pos 1).le) (d : ℝ))) hfac

theorem integral_logBarrierIntensityDensity_Icc_le {C : ℝ} (hC : 0 ≤ C)
    (hsoft : LogSimplexBound C) {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    (∫ s in Icc 0 b, logBarrierIntensityDensity d A c s) ≤
      (logBarrierIntensityConstant C / Real.exp 1) * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d) := by
  let F := logBarrierIntensityConstant C * (1 + (A + c) ^ 14) / ((d : ℝ) * Real.sqrt d)
  have hK := degreeBallotDensityConstant_pos 14
  have hF : 0 ≤ F := by dsimp [F]; unfold logBarrierIntensityConstant; positivity
  have hi : IntegrableOn (fun s : ℝ => F * Real.exp (Real.exp 1 * s - d)) (Icc 0 b) :=
    (by fun_prop : Continuous (fun s : ℝ => F * Real.exp (Real.exp 1 * s - d))).integrableOn_Icc
  calc
    _ ≤ ∫ s in Icc 0 b, F * Real.exp (Real.exp 1 * s - d) := by
      apply integral_mono_ae (logBarrierIntensityDensity_integrable_Icc hC hsoft hd hA hc) hi
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact logBarrierIntensityDensity_exp_upper hC hsoft hd hA hc hs.1
    _ = F * ∫ s in Icc 0 b, Real.exp (Real.exp 1 * s - d) := integral_const_mul F _
    _ ≤ F * (Real.exp (Real.exp 1 * b - d) / Real.exp 1) :=
      mul_le_mul_of_nonneg_left (integral_exp_generation_bound d hb) hF
    _ = _ := by dsimp [F]; ring

/-- Finite actual generation mass in the complete endpoint interval. -/
theorem generation_logBarrier_Icc_le {C : ℝ} (hC : 0 ≤ C)
    (hsoft : LogSimplexBound C) {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    generationIncrementIntensity d (logBarrierVectorEvent d A c (Icc 0 b)) ≤
      ENNReal.ofReal ((logBarrierIntensityConstant C / Real.exp 1) * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)) := by
  rw [generationIncrementIntensity_logBarrierVectorEvent d A c measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal (logBarrierIntensityDensity_integrable_Icc hC hsoft hd hA hc)
      (Filter.Eventually.of_forall (logBarrierIntensityDensity_nonneg d A c))]
  exact ENNReal.ofReal_le_ofReal (integral_logBarrierIntensityDensity_Icc_le hC hsoft hd hA hc hb)

/-- Markov's first-moment step for the actual collection of all labelled paths. -/
theorem probability_exists_vectorEvent_le_generation (d : ℕ)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    law {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ E} ≤ generationIncrementIntensity d E := by
  have hset : MeasurableSet {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ E} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun r => hE.preimage (measurable_tupleIncrement r))
  rw [← lintegral_vectorEventCount d hE, ← lintegral_indicator_one hset]
  apply lintegral_mono
  intro ω
  by_cases hh : ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ E
  · rw [Set.indicator_of_mem (show ω ∈ {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ E} from hh), Pi.one_apply]
    obtain ⟨r, hr⟩ := hh
    have ht := ENNReal.le_tsum (f := fun r : Fin d → ℕ => E.indicator (fun _ => (1 : ℝ≥0∞))
      (tupleIncrement r ω)) r
    simpa only [Set.indicator_of_mem hr, vectorEventCount] using ht
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ E} from hh)]
    exact bot_le

theorem probability_exists_logBarrier_Icc_le {C : ℝ} (hC : 0 ≤ C)
    (hsoft : LogSimplexBound C) {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    law {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ logBarrierVectorEvent d A c (Icc 0 b)} ≤
      ENNReal.ofReal ((logBarrierIntensityConstant C / Real.exp 1) * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)) :=
  (probability_exists_vectorEvent_le_generation d
    (measurableSet_logBarrierVectorEvent d A c measurableSet_Icc)).trans
      (generation_logBarrier_Icc_le hC hsoft hd hA hc hb)

end FreezingGrowth.PWIT
