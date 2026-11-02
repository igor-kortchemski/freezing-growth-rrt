module

public import FreezingGrowth.PWIT.CriticalCrossingWeights
public import FreezingGrowth.RRTCriticalUpperTransfer

/-! The unconditional critical upper clock bound for the actual PWIT law. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped ENNReal

theorem criticalClockUpperBound_actual :
    CriticalClockUpperBound 14 (criticalClockUpperConstant criticalCrossingOffset)
      criticalCrossingOffset 30 := by
  intro d hd x hx
  have ha : criticalCrossingOffset ≤ x / Real.exp 1 + criticalCrossingOffset := by
    have hh := div_nonneg hx (Real.exp_pos 1).le
    linarith
  have hprob := probability_reaches_le_crossing_sum hd ha
    (by positivity : (0 : ℝ) ≤ 2 / Real.exp 1)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    crossingIntensityBound_nonneg d j (x / Real.exp 1 + criticalCrossingOffset) (2 / Real.exp 1))] at hprob
  have hsum := ENNReal.ofReal_le_ofReal
    (sum_crossingIntensityBound_critical_le d criticalCrossingOffset_pos.le hx)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hprob.trans hsum)
  have hnonneg : 0 ≤ criticalClockUpperConstant criticalCrossingOffset * (1 + x) ^ 14 * Real.exp (-x) := by
    have := criticalClockUpperConstant_pos criticalCrossingOffset_pos.le
    positivity
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg, sub_add_eq_sub_sub] using hreal

theorem exists_criticalClockUpperBound :
    ∃ C : ℝ, 0 < C ∧ CriticalClockUpperBound 14 C criticalCrossingOffset 30 :=
  ⟨criticalClockUpperConstant criticalCrossingOffset,
    criticalClockUpperConstant_pos criticalCrossingOffset_pos.le, criticalClockUpperBound_actual⟩

end FreezingGrowth.PWIT
