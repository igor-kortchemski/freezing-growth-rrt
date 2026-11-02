module

public import FreezingGrowth.PWIT.CriticalFirstCrossing
public import FreezingGrowth.PWIT.LogBarrierIntensityActual

/-! The actual PWIT first-crossing union bound. Negative endpoints are empty,
so the endpoint exponential retains its full dependence on the deviation. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal

noncomputable def crossingIntensityBound (d j : ℕ) (a c : ℝ) : ℝ :=
  logGenerationConstant * (1 + (crossingAllowance d j a c + c) ^ 14) /
    ((j : ℝ) * Real.sqrt j) *
      Real.exp (Real.exp 1 * criticalCrossingBarrier d j a c - j)

theorem crossingIntensityBound_nonneg (d j : ℕ) (a c : ℝ) :
    0 ≤ crossingIntensityBound d j a c := by
  unfold crossingIntensityBound
  have hC := logGenerationConstant_pos
  positivity

theorem probability_crossingGenerationEvent_le {d j : ℕ} (hj : 30 ≤ j)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    law (crossingGenerationEvent d j a c) ≤ ENNReal.ofReal (crossingIntensityBound d j a c) := by
  have hjpos : 0 < j := by omega
  let : NeZero j := ⟨hjpos.ne'⟩
  rw [crossingGenerationEvent, dite_eq_left hjpos]
  by_cases hb : 0 ≤ criticalCrossingBarrier d j a c
  · have hA : 0 ≤ crossingAllowance d j a c := by
      have hl : 0 ≤ Real.log ((min j (d - j) : ℕ) + 1 : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ min j (d - j) + 1 by omega))
      exact add_nonneg ha (mul_nonneg hc hl)
    simpa only [hb, true_and, crossingIntensityBound] using
      (probability_exists_logBarrier_bound hj hA hc hb)
  · simp only [hb, false_and, ofPred_false, measure_empty, zero_le]

theorem probability_reaches_le_crossing_sum {d : ℕ} (hd : 30 ≤ d) {a c : ℝ}
    (ha : criticalCrossingOffset ≤ a) (hc : 0 ≤ c) :
    law (reaches d (timeCenter d - a)) ≤
      ∑ j ∈ Finset.Icc 30 d, ENNReal.ofReal (crossingIntensityBound d j a c) := by
  have hsub : reaches d (timeCenter d - a) ≤ᵐ[law]
      ⋃ j ∈ Finset.Icc 30 d, crossingGenerationEvent d j a c := by
    filter_upwards [ae_all_clocks_pos] with ω hω
    intro hr
    obtain ⟨j, hj, hcross⟩ := reaches_first_crossing hd ha hc
      (fun z => (hω z).le) hr
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hcross⟩⟩
  calc
    _ ≤ law (⋃ j ∈ Finset.Icc 30 d, crossingGenerationEvent d j a c) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ Finset.Icc 30 d, law (crossingGenerationEvent d j a c) :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact probability_crossingGenerationEvent_le (Finset.mem_Icc.mp hj).1
        (criticalCrossingOffset_pos.le.trans ha) hc

end FreezingGrowth.PWIT
