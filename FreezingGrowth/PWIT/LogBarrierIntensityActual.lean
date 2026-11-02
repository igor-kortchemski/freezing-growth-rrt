module

public import FreezingGrowth.PWIT.LogBarrierIntensity
public import FreezingGrowth.PWIT.SoftBallotSummation

/-! Unconditional logarithmic-barrier bounds for actual all-rank PWIT paths.
The analytic simplex estimate is discharged by its proved cyclic-occupancy
bound, before the generation first moment is used. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal

theorem logSimplexBound_actual : LogSimplexBound logSoftBallotConstant := by
  intro d hd A c hA hc
  exact @simplex_log_ballot_bound d hd A c hA hc

noncomputable def logGenerationConstant : ℝ :=
  logBarrierIntensityConstant logSoftBallotConstant / Real.exp 1

theorem logGenerationConstant_pos : 0 < logGenerationConstant := by
  have hC : 0 < logSoftBallotConstant := by
    have := logSoftBallotConstant_ge_forty_two
    linarith
  have hK := degreeBallotDensityConstant_pos 14
  unfold logGenerationConstant logBarrierIntensityConstant
  positivity

/-- Actual all-rank prefix intensity below a nonnegative endpoint. -/
theorem generation_logBarrier_bound {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    generationIncrementIntensity d (logBarrierVectorEvent d A c (Icc 0 b)) ≤
      ENNReal.ofReal (logGenerationConstant * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)) := by
  exact generation_logBarrier_Icc_le
    (by have := logSoftBallotConstant_ge_forty_two; linarith)
    logSimplexBound_actual hd hA hc hb

theorem lintegral_logBarrier_count_le {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    (∫⁻ ω, vectorEventCount d (logBarrierVectorEvent d A c (Icc 0 b)) ω ∂law) ≤
      ENNReal.ofReal (logGenerationConstant * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)) := by
  rw [lintegral_vectorEventCount d (measurableSet_logBarrierVectorEvent d A c measurableSet_Icc)]
  exact generation_logBarrier_bound hd hA hc hb

theorem probability_exists_logBarrier_bound {d : ℕ} [NeZero d] (hd : 30 ≤ d)
    {A c b : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    law {ω | ∃ r : Fin d → ℕ, tupleIncrement r ω ∈ logBarrierVectorEvent d A c (Icc 0 b)} ≤
      ENNReal.ofReal (logGenerationConstant * (1 + (A + c) ^ 14) /
        ((d : ℝ) * Real.sqrt d) * Real.exp (Real.exp 1 * b - d)) :=
  (probability_exists_vectorEvent_le_generation d
    (measurableSet_logBarrierVectorEvent d A c measurableSet_Icc)).trans
      (generation_logBarrier_bound hd hA hc hb)

end FreezingGrowth.PWIT
