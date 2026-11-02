module

public import FreezingGrowth.PWIT.CriticalClockUpper
public import FreezingGrowth.RRTSharpHeightConditional

/-! The sharp recursive-tree height estimates under the actual tree law.
The critical clock upper estimate is proved, so no estimate premise remains. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory

theorem uniformCriticalAbsoluteDeviation :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, criticalAbsoluteDeviation n ≤ B :=
  uniformCriticalAbsoluteDeviation_of_clock PWIT.criticalClockUpperBound_actual

theorem uniformCriticalMeanDeviation :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |meanHeight n - lowerCenter (3 / 2) n| ≤ B :=
  uniformCriticalMeanDeviation_of_clock PWIT.criticalClockUpperBound_actual

/-- E1: the source mean has a uniformly bounded error at its exact center. -/
theorem sourceMeanHeightExpansion :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 2 ≤ n → |meanHeight n - sourceHeightCenter n| ≤ B :=
  sourceMeanHeightExpansion_of_clock PWIT.criticalClockUpperBound_actual

/-- E1: uniform tightness at the exact source center. -/
theorem sourceHeight_tight :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      (Forward.heightLaw allAttach n).real
        {h | K ≤ |(h : ℝ) - sourceHeightCenter n|} ≤ ε :=
  sourceHeight_tight_of_clock PWIT.criticalClockUpperBound_actual

/-- E2: exact source rate, for every size and nonnegative real threshold. -/
theorem meanCenteredHeightConcentration :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ k : ℝ, 0 ≤ k →
      (Forward.heightLaw allAttach n).real {h | k ≤ |(h : ℝ) - meanHeight n|} ≤
        K * Real.exp (-k / (3 * Real.exp 1)) :=
  meanCenteredHeightConcentration_of_clock PWIT.criticalClockUpperBound_actual

end FreezingGrowth.RRT
