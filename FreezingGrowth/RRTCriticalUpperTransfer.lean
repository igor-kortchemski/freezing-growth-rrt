module

public import FreezingGrowth.RRTUpperTail
public import FreezingGrowth.RRTCriticalLowerSeed
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A conditional transfer of a critical PWIT upper estimate to actual
recursive-tree heights. The clock estimate remains an explicit premise;
this module by itself does not complete either sharp height obligation. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped NNReal

namespace PWIT

/-- The first-crossing estimate needed for the critical upper transfer. -/
def CriticalClockUpperBound (P : ℕ) (C A₀ : ℝ) (d₀ : ℕ) : Prop :=
  ∀ d : ℕ, d₀ ≤ d → ∀ x : ℝ, 0 ≤ x →
    law.real (reaches d (timeCenter d - x / Real.exp 1 - A₀)) ≤
      C * (1 + x) ^ P * Real.exp (-x)

end PWIT

namespace RRT

theorem lowerCenter_critical_ge_log (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ lowerCenter (3 / 2) n := by
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hll := Real.log_le_sub_one_of_pos
    (show 0 < 1 + Real.log ((n : ℝ) + 1) by linarith)
  have he : 0 ≤ Real.exp 1 - 5 / 2 := by have := Real.exp_one_gt_d9; linarith
  unfold lowerCenter
  nlinarith [mul_nonneg he hl]

/-- The critical log correction also cancels in the upper inversion. -/
theorem critical_height_index_time_lower (n d : ℕ) {A x : ℝ} (hA : 1 ≤ A) (hx : 0 ≤ x)
    (hd : lowerCenter (3 / 2) n + A + x ≤ (d : ℝ)) :
    Real.log ((n : ℝ) + 1) + (A + x) / Real.exp 1 ≤ PWIT.timeCenter d := by
  let l : ℝ := Real.log ((n : ℝ) + 1)
  let g : ℝ := Real.log (1 + l)
  have hl : 0 ≤ l := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hb : l ≤ lowerCenter (3 / 2) n := lowerCenter_critical_ge_log n
  have hdl : 1 + l ≤ (d : ℝ) := by linarith
  have hlogd : g ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by linarith : 0 < 1 + l) hdl
  have hcenter : lowerCenter (3 / 2) n = Real.exp 1 * l - (3 / 2) * g := rfl
  have hleft : l + (A + x) / Real.exp 1 =
      (2 * Real.exp 1 * l + 2 * A + 2 * x) / (2 * Real.exp 1) := by
    field_simp
    ring
  have hright : PWIT.timeCenter d =
      (2 * (d : ℝ) + 3 * Real.log d) / (2 * Real.exp 1) := by
    unfold PWIT.timeCenter
    field_simp
  change l + (A + x) / Real.exp 1 ≤ _
  rw [hleft, hright]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.exp 1)).mpr
  rw [hcenter] at hd
  linarith

/-- Any proved clock bound of the displayed form yields a uniform actual RRT
upper tail, including the zero-edge tree. The clock premise is retained. -/
theorem heightLaw_critical_upper_tail_of_clock {P : ℕ} {C A₀ : ℝ} {d₀ : ℕ}
    (hclock : PWIT.CriticalClockUpperBound P C A₀ d₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (Forward.heightLaw allAttach n).real
        {h | lowerCenter (3 / 2) n + A + x ≤ (h : ℝ)} ≤
        2 * C * (1 + x) ^ P * Real.exp (-x) := by
  let A : ℝ := max (max 1 (d₀ : ℝ)) (1 + Real.exp 1 * (Real.log 2 + A₀))
  have hA : 1 ≤ A := (le_max_left 1 (d₀ : ℝ)).trans (le_max_left _ _)
  have hAd : (d₀ : ℝ) ≤ A := (le_max_right 1 (d₀ : ℝ)).trans (le_max_left _ _)
  have hAdiv : Real.log 2 + A₀ ≤ A / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).mpr
    have hh : 1 + Real.exp 1 * (Real.log 2 + A₀) ≤ A := le_max_right _ _
    nlinarith
  refine ⟨A, by linarith, ?_⟩
  intro n x hx
  let d : ℕ := Nat.ceil (lowerCenter (3 / 2) n + A + x)
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hb : 0 ≤ lowerCenter (3 / 2) n := hl.trans (lowerCenter_critical_ge_log n)
  have hd : lowerCenter (3 / 2) n + A + x ≤ (d : ℝ) := Nat.le_ceil _
  have hdpos : 0 < d := Nat.ceil_pos.mpr (by linarith)
  have hd₀ : d₀ ≤ d := by
    exact_mod_cast (show (d₀ : ℝ) ≤ (d : ℝ) by linarith)
  have htime := critical_height_index_time_lower n d hA hx hd
  rw [add_div] at htime
  have ht : (upperComparisonTime n : ℝ) ≤ PWIT.timeCenter d - x / Real.exp 1 - A₀ := by
    have heq : (upperComparisonTime n : ℝ) = Real.log ((n : ℝ) + 1) + Real.log 2 := by
      change Real.log (2 * ((n : ℝ) + 1)) = _
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)]
      ring
    rw [heq]
    linarith
  have hu : PWIT.law.real (PWIT.reaches d (upperComparisonTime n : ℝ)) ≤
      C * (1 + x) ^ P * Real.exp (-x) :=
    (measureReal_mono (PWIT.reaches_mono_time ht)).trans (hclock d hd₀ x hx)
  rw [PWIT.reaches_probability_eq_geometric_tail (upperComparisonTime n) d hdpos] at hu
  have hi := upperComparisonTime_index_tail n
  have hm := geometricHeightLaw_tail_ge (upperComparisonTime n) n d
  have hh := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ (Forward.heightLaw allAttach n).real {h | d ≤ h} from measureReal_nonneg)
  have hevent : {h : ℕ | lowerCenter (3 / 2) n + A + x ≤ (h : ℝ)} = {h | d ≤ h} := by
    ext h
    simp only [Set.mem_ofPred_eq, d, Nat.ceil_le]
  rw [hevent]
  nlinarith

end RRT
end FreezingGrowth
