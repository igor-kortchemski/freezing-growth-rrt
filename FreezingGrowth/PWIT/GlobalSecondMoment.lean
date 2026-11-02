module

public import FreezingGrowth.PWIT.OverlapBound
public import FreezingGrowth.PWIT.PairDecomposition
public import FreezingGrowth.PWIT.ClockSeedMoment

/-! Uniform global second moment of the actual exactly-leading window count.
All rank sums, moment identities and common-ancestor laws refer to the actual
clock model. No conditional fixed-labelled-path overlap estimate is used. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Filter Set
open scoped ENNReal Topology

def criticalLeadingVectorEvent (d : ℕ) : Set (Fin d → ℝ) :=
  endpointLeadingVectorEvent d (Ioc (timeCenter d - 1) (timeCenter d))

theorem measurableSet_criticalLeadingVectorEvent (d : ℕ) :
    MeasurableSet (criticalLeadingVectorEvent d) :=
  measurableSet_endpointLeadingVectorEvent d measurableSet_Ioc

noncomputable def depthWeightConstant : ℝ :=
  (8 + (2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)) *
    ∑' k : ℕ, 1 / (k : ℝ) ^ (3 / 2 : ℝ)

theorem depthWeightConstant_nonneg : 0 ≤ depthWeightConstant := by
  have hh : 0 ≤ ∑' k : ℕ, 1 / (k : ℝ) ^ (3 / 2 : ℝ) := tsum_nonneg (fun _ => by positivity)
  unfold depthWeightConstant
  positivity

theorem criticalLeadingMean_le {d : ℕ} (hd : 0 < d) :
    generationIncrementIntensity d (criticalLeadingVectorEvent d) ≤
      ENNReal.ofReal ((timeCenter d) ^ d / ((d.factorial : ℝ) * (d : ℝ))) := by
  let : NeZero d := ⟨hd.ne'⟩
  have ht : 0 ≤ timeCenter d := by unfold timeCenter; positivity
  rw [← lintegral_vectorEventCount d (measurableSet_criticalLeadingVectorEvent d)]
  unfold criticalLeadingVectorEvent
  simp_rw [vectorEventCount_endpointLeading]
  calc
    _ ≤ ∫⁻ ω, pathEventCount d (endpointLeadingEvent (Iic (timeCenter d))) ω ∂law := by
      apply lintegral_mono
      intro ω
      apply pathEventCount_mono
      intro v _ ω hω
      exact ⟨hω.1.2, hω.2⟩
    _ = _ := lintegral_leadingCount_le ht

theorem criticalLeadingPair_le {d : ℕ} (hd : 0 < d) {M : ℝ} (hM : 0 ≤ M)
    (hmean : generationIncrementIntensity d (criticalLeadingVectorEvent d) ≤ ENNReal.ofReal M) :
    generationPairIntensity d (criticalLeadingVectorEvent d ×ˢ criticalLeadingVectorEvent d) ≤
      ENNReal.ofReal (M + M ^ 2 + overlapMomentConstant * depthWeightConstant) := by
  let S := Finset.Icc 1 (d - 1)
  have hover (j : ℕ) (hj : j ∈ S) :
      extendedOverlapIntensity j (d - j)
        (((restrictSequence d) ⁻¹' criticalLeadingVectorEvent d) ×ˢ
          ((restrictSequence d) ⁻¹' criticalLeadingVectorEvent d)) ≤
        ENNReal.ofReal (overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ)) := by
    have hmem := Finset.mem_Icc.mp hj
    have hjp : 0 < j := by omega
    have hqp : 0 < d - j := by omega
    have he : j + (d - j) = d := by omega
    let F (n : ℕ) : Set IncrementSequence :=
      (restrictSequence n) ⁻¹' criticalLeadingVectorEvent n
    have hb : extendedOverlapIntensity j (d - j) (F (j + (d - j)) ×ˢ F (j + (d - j))) ≤
        ENNReal.ofReal (overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ)) :=
      extendedOverlapIntensity_critical_le hjp hqp
    rw [he] at hb
    exact hb
  have hnonneg (j : ℕ) : 0 ≤ overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ) :=
    mul_nonneg overlapMomentConstant_pos.le
      (threeFactorDepthWeight_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hsum : (∑ j ∈ S, ENNReal.ofReal
      (overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ))) =
      ENNReal.ofReal (overlapMomentConstant * ∑ j ∈ S, threeFactorDepthWeight j (d - j : ℕ)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnonneg j), ← Finset.mul_sum]
  have hsum_bound : (∑ j ∈ S, ENNReal.ofReal
      (overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ))) ≤
      ENNReal.ofReal (overlapMomentConstant * depthWeightConstant) := by
    rw [hsum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_threeFactorDepthWeight_le d) overlapMomentConstant_pos.le)
  rw [generationPairIntensity_event_decomposition_pos hd (measurableSet_criticalLeadingVectorEvent d)]
  calc
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal M ^ 2 +
        ∑ j ∈ S, ENNReal.ofReal (overlapMomentConstant * threeFactorDepthWeight j (d - j : ℕ)) :=
      add_le_add (add_le_add hmean (pow_le_pow_left₀ (by positivity) hmean 2))
        (Finset.sum_le_sum hover)
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal M ^ 2 +
        ENNReal.ofReal (overlapMomentConstant * depthWeightConstant) :=
      add_le_add le_rfl hsum_bound
    _ = _ := by
      rw [← ENNReal.ofReal_pow hM 2, ← ENNReal.ofReal_add hM (sq_nonneg M),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg overlapMomentConstant_pos.le depthWeightConstant_nonneg)]

/-- Actual square integrability and a bound independent of the generation. -/
theorem uniform_exactLeadingWindow_secondMoment :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ d : ℕ in atTop,
      Integrable (fun ω => exactLeadingWindowCount d ω ^ 2) law ∧
        (∫ ω, exactLeadingWindowCount d ω ^ 2 ∂law) ≤ B := by
  let M : ℝ := criticalIntensityConstant + 1
  have hM : 0 < M := by dsimp [M]; have := criticalIntensityConstant_pos; linarith
  have hlim : Tendsto (fun d : ℕ => (timeCenter d) ^ d / ((d.factorial : ℝ) * (d : ℝ)))
      atTop (𝓝 criticalIntensityConstant) := by
    simpa only [mul_zero, neg_zero, Real.exp_zero, one_mul, sub_zero] using tendsto_critical_intensity 0
  have hevent := hlim.eventually_le_const (by dsimp [M]; linarith : criticalIntensityConstant < M)
  let B : ℝ := 1 + (M + M ^ 2 + overlapMomentConstant * depthWeightConstant)
  have hB : 0 < B := by
    have hC := overlapMomentConstant_pos
    have hD := depthWeightConstant_nonneg
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hevent, eventually_ge_atTop 1] with d hd hd1
  have hdp : 0 < d := by omega
  let E := criticalLeadingVectorEvent d
  have hE : MeasurableSet E := measurableSet_criticalLeadingVectorEvent d
  have hmean : generationIncrementIntensity d E ≤ ENNReal.ofReal M :=
    (criticalLeadingMean_le hdp).trans (ENNReal.ofReal_le_ofReal hd)
  have hpair : generationPairIntensity d (E ×ˢ E) ≤ ENNReal.ofReal B := by
    apply (criticalLeadingPair_le hdp hM.le hmean).trans
    exact ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)
  have hfinite : generationPairIntensity d (E ×ˢ E) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpair
  have hi := integrable_vectorEventCount_toReal_sq d hE hfinite
  have hv := integral_vectorEventCount_toReal_sq d hE hfinite
  have hbound : (∫ ω, (vectorEventCount d E ω).toReal ^ 2 ∂law) ≤ B := by
    rw [hv]
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpair
    simpa only [ENNReal.toReal_ofReal hB.le] using hh
  dsimp [E, criticalLeadingVectorEvent] at hi hbound
  simp_rw [vectorEventCount_endpointLeading] at hi hbound
  exact ⟨hi, hbound⟩

/-- The actual PWIT has a positive uniform chance to reach the critical
generation time, with no unproved probabilistic premise. -/
theorem clockLowerSeed : ClockLowerSeed :=
  clockLowerSeed_of_exactLeadingSecondMoment uniform_exactLeadingWindow_secondMoment

end FreezingGrowth.PWIT
