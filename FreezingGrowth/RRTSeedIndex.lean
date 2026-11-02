module

public import FreezingGrowth.RRTLowerCenter
public import FreezingGrowth.PWIT.GoodPaths
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Deterministic inversion of the one-sided generation-time estimate. -/

@[expose] public section
namespace FreezingGrowth.RRT

open Filter
open scoped Topology

noncomputable def seedIndex (n : ℕ) : ℕ := Nat.ceil (lowerCenter 2 n - 1)

theorem lowerCenter_two_lower (n : ℕ) :
    (Real.exp 1 - 2) * Real.log ((n : ℝ) + 1) ≤ lowerCenter 2 n := by
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log ((n : ℝ) + 1) by linarith)
  unfold lowerCenter
  nlinarith

theorem tendsto_lowerCenter_two : Tendsto (lowerCenter 2) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hm := hl.const_mul_atTop (by have := Real.exp_one_gt_two; linarith : 0 < Real.exp 1 - 2)
  exact tendsto_atTop_mono lowerCenter_two_lower hm

theorem tendsto_seedIndex : Tendsto seedIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_lowerCenter_two.eventually_ge_atTop ((b : ℝ) + 1)] with n hn
  have hh := Nat.le_ceil (lowerCenter 2 n - 1)
  have hr : (b : ℝ) ≤ (seedIndex n : ℝ) := by dsimp [seedIndex]; linarith
  exact_mod_cast hr

/-- The log-log slack permits any fixed time shift in the seed transfer. -/
theorem seedIndex_time_upper {n : ℕ} (hb : 2 ≤ lowerCenter 2 n) :
    PWIT.timeCenter (seedIndex n) ≤ Real.log ((n : ℝ) + 1) -
      (1 / (2 * Real.exp 1)) * Real.log (1 + Real.log ((n : ℝ) + 1)) +
      3 / (2 * Real.exp 1) := by
  let l : ℝ := Real.log ((n : ℝ) + 1)
  let d : ℕ := seedIndex n
  have hl : 0 ≤ l := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hll : 0 ≤ Real.log (1 + l) := Real.log_nonneg (by linarith)
  have hd : (d : ℝ) < lowerCenter 2 n := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ lowerCenter 2 n - 1)
    dsimp [d, seedIndex]
    linarith
  have hcenter : lowerCenter 2 n ≤ Real.exp 1 * l := by unfold lowerCenter; dsimp [l] at *; linarith
  have hdpos : 0 < d := by
    have hh := Nat.le_ceil (lowerCenter 2 n - 1)
    have hr : (1 : ℝ) ≤ d := by dsimp [d, seedIndex]; linarith
    have hn : 1 ≤ d := by exact_mod_cast hr
    omega
  have hlogd : Real.log (d : ℝ) ≤ 1 + Real.log (1 + l) := by
    have hh := Real.log_le_log (show (0 : ℝ) < d by exact_mod_cast hdpos)
      (show (d : ℝ) ≤ Real.exp 1 * (1 + l) by have := Real.exp_pos (1 : ℝ); nlinarith)
    rw [Real.log_mul (Real.exp_ne_zero _) (by linarith : 1 + l ≠ 0), Real.log_exp] at hh
    exact hh
  have hepos := Real.exp_pos (1 : ℝ)
  have hde : (d : ℝ) ≤ Real.exp 1 * l - 2 * Real.log (1 + l) := by
    change (d : ℝ) ≤ lowerCenter 2 n
    exact hd.le
  unfold PWIT.timeCenter
  change (d : ℝ) / Real.exp 1 + 3 * Real.log d / (2 * Real.exp 1) ≤ _
  change _ ≤ l - (1 / (2 * Real.exp 1)) * Real.log (1 + l) + 3 / (2 * Real.exp 1)
  have hleft : (d : ℝ) / Real.exp 1 + 3 * Real.log d / (2 * Real.exp 1) =
      (2 * (d : ℝ) + 3 * Real.log d) / (2 * Real.exp 1) := by
    field_simp
  have hright : l - (1 / (2 * Real.exp 1)) * Real.log (1 + l) + 3 / (2 * Real.exp 1) =
      (2 * Real.exp 1 * l - Real.log (1 + l) + 3) / (2 * Real.exp 1) := by
    field_simp
  rw [hleft, hright]
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2 * Real.exp 1)).mpr
  nlinarith

theorem tendsto_seedIndex_time_gap :
    Tendsto (fun n : ℕ => PWIT.timeCenter (seedIndex n) - Real.log ((n : ℝ) + 1))
      atTop atBot := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hn
  have hl1 : Tendsto (fun n : ℕ => 1 + Real.log ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [Function.comp_def]; linarith) hl
  have hll := Real.tendsto_log_atTop.comp hl1
  have hm := hll.const_mul_atTop
    (by positivity : (0 : ℝ) < 1 / (2 * Real.exp 1))
  have hu : Tendsto (fun n : ℕ =>
      -(1 / (2 * Real.exp 1) * Real.log (1 + Real.log ((n : ℝ) + 1))) +
        3 / (2 * Real.exp 1)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [hm.eventually_ge_atTop (3 / (2 * Real.exp 1) - b)] with n hh
    simp only [Function.comp_def] at hh
    linarith
  apply tendsto_atBot_mono' atTop _ hu
  filter_upwards [tendsto_lowerCenter_two.eventually_ge_atTop 2] with n hn
  have hh := seedIndex_time_upper hn
  linarith

end FreezingGrowth.RRT
