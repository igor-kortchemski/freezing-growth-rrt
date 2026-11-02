module

public import FreezingGrowth.RRTUpperTail
public import FreezingGrowth.PWIT.GlobalSecondMoment

/-!
# A coarse absolute-deviation estimate for actual recursive-tree heights

The uniform upper excess and the proved lower deficit at coefficient two give
an explicit logarithmic-logarithmic error about the first-order center. This
auxiliary estimate is weaker than the sharp source claims E1 and E2.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open MeasureTheory

noncomputable def roughAbsoluteDeviation (n : ℕ) : ℝ :=
  ∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|
    ∂Forward.heightLaw allAttach n

theorem roughAbsoluteDeviation_integrable (n : ℕ) :
    Integrable (fun h : ℕ => |(h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|)
      (Forward.heightLaw allAttach n) :=
  Forward.heightLaw_integrable allAttach n _

theorem roughAbsoluteDeviation_nonneg (n : ℕ) : 0 ≤ roughAbsoluteDeviation n :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem roughAbsoluteDeviation_le_excess_add_deficit (n : ℕ) :
    roughAbsoluteDeviation n ≤ upperExcess n + lowerDeficit 2 n +
      2 * Real.log (1 + Real.log ((n : ℝ) + 1)) := by
  let b := Real.exp 1 * Real.log ((n : ℝ) + 1)
  let c := 2 * Real.log (1 + Real.log ((n : ℝ) + 1))
  have hc : 0 ≤ c := by
    have hn : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hcenter : lowerCenter 2 n = b - c := rfl
  have hpoint (h : ℕ) : |(h : ℝ) - b| ≤
      max ((h : ℝ) - b) 0 + max (lowerCenter 2 n - (h : ℝ)) 0 + c := by
    have hu := le_max_left ((h : ℝ) - b) 0
    have hu0 := le_max_right ((h : ℝ) - b) 0
    have hl := le_max_left (lowerCenter 2 n - (h : ℝ)) 0
    have hl0 := le_max_right (lowerCenter 2 n - (h : ℝ)) 0
    apply abs_le.mpr
    constructor <;> linarith
  have hu := upperExcessAt_integrable n b
  have hl := lowerDeficit_integrable 2 n
  calc
    roughAbsoluteDeviation n ≤ ∫ h : ℕ,
        (max ((h : ℝ) - b) 0 + max (lowerCenter 2 n - (h : ℝ)) 0 + c)
          ∂Forward.heightLaw allAttach n :=
      integral_mono (roughAbsoluteDeviation_integrable n)
        ((hu.add hl).add (integrable_const c)) hpoint
    _ = upperExcess n + lowerDeficit 2 n + c := by
      have houter := integral_add (hu.add hl) (integrable_const c)
      have hinner := integral_add hu hl
      simp only [Pi.add_apply] at houter hinner
      rw [houter, hinner, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    _ = _ := rfl

/-- A single constant works for every number of edges, including zero. -/
theorem uniformRoughAbsoluteDeviation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, roughAbsoluteDeviation n ≤
      C + 2 * Real.log (1 + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨D, hD, hdeficit⟩ := uniformLowerDeficit_of_seed (by norm_num : (0 : ℝ) ≤ 2)
    (constantSuccessSeed_of_clockLowerSeed PWIT.clockLowerSeed)
  refine ⟨upperExcessConstant + D, add_nonneg upperExcessConstant_pos.le hD, fun n => ?_⟩
  exact (roughAbsoluteDeviation_le_excess_add_deficit n).trans
    (add_le_add (add_le_add (upperExcess_le n) (hdeficit n)) (le_refl _))

end FreezingGrowth.RRT
