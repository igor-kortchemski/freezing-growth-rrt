module

public import FreezingGrowth.PWIT.TimeCenterEstimates
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! Deterministic geometry of the logarithmic first-crossing barrier.
These comparisons do not assert the probabilistic ballot or crossing bounds. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem log_chord_lower {J r : ℝ} (hJ : 0 < J) (hr : 0 ≤ r) (hrJ : r ≤ J) :
    r / J * Real.log (J + 1) ≤ Real.log (r + 1) := by
  have ha : 0 ≤ r / J := div_nonneg hr hJ.le
  have hb : 0 ≤ 1 - r / J := by
    have hh := (div_le_one hJ).mpr hrJ
    linarith
  have hconc := StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  have hh := hconc.2
    (show J + 1 ∈ Set.Ioi (0 : ℝ) by simp; linarith)
    (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) ha hb
    (show r / J + (1 - r / J) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hh
  have he : r / J * (J + 1) + (1 - r / J) * 1 = r + 1 := by field_simp; ring
  rwa [he] at hh

/-- Subtracting the endpoint chord leaves a symmetric logarithmic barrier. -/
theorem log_bridge_barrier_compare {i j : ℕ} (hj : 0 < j) (hij : i ≤ j) :
    Real.log ((i : ℝ) + 1) - (i : ℝ) / j * Real.log ((j : ℝ) + 1) ≤
      Real.log ((min i (j - i) : ℕ) + 1 : ℝ) := by
  have hjR : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hl : 0 ≤ Real.log ((j : ℝ) + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) j; linarith)
  by_cases hi : i ≤ j - i
  · rw [Nat.min_eq_left hi]
    have hh := mul_nonneg (div_nonneg (Nat.cast_nonneg (α := ℝ) i) hjR.le) hl
    linarith
  · rw [Nat.min_eq_right (by omega : j - i ≤ i)]
    have hs := log_chord_lower hjR (Nat.cast_nonneg (α := ℝ) (j - i))
      (show ((j - i : ℕ) : ℝ) ≤ j by exact_mod_cast (Nat.sub_le j i))
    have hm := Real.log_le_log (by positivity : (0 : ℝ) < (i : ℝ) + 1)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := Nat.cast_sub hij
    rw [hcast] at hs
    rw [hcast]
    have he : ((j : ℝ) - i) / j * Real.log ((j : ℝ) + 1) =
        Real.log ((j : ℝ) + 1) - (i : ℝ) / j * Real.log ((j : ℝ) + 1) := by
      field_simp
    rw [he] at hs
    linarith

theorem min_window_mul_bound {d j i : ℕ} (hjd : j ≤ d) (hij : i ≤ j) :
    min i (d - i) + 1 ≤ (d - j + 1) * (min i (j - i) + 1) := by
  by_cases hi : i ≤ j - i
  · rw [Nat.min_eq_left hi]
    have hm := Nat.min_le_left i (d - i)
    nlinarith [Nat.zero_le (d - j), Nat.zero_le i]
  · rw [Nat.min_eq_right (by omega : j - i ≤ i)]
    have hm := Nat.min_le_right i (d - i)
    have he : d - i = d - j + (j - i) := by omega
    rw [he] at hm ⊢
    nlinarith [Nat.zero_le (d - j), Nat.zero_le (j - i)]

/-- Near the far endpoint, the global window loses at most `log(q+1)`. -/
theorem log_min_window_bound {d j i : ℕ} (hjd : j ≤ d) (hij : i ≤ j) :
    Real.log ((min i (d - i) : ℕ) + 1 : ℝ) ≤
      Real.log ((d - j : ℕ) + 1 : ℝ) + Real.log ((min i (j - i) : ℕ) + 1 : ℝ) := by
  have hh := Real.log_le_log
    (show (0 : ℝ) < ((min i (d - i) + 1 : ℕ) : ℝ) by positivity)
    (show ((min i (d - i) + 1 : ℕ) : ℝ) ≤
      (((d - j + 1) * (min i (j - i) + 1) : ℕ) : ℝ) by
        exact_mod_cast min_window_mul_bound hjd hij)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hh ⊢
  rwa [Real.log_mul (by positivity : ((d - j : ℕ) : ℝ) + 1 ≠ 0)
    (by positivity : ((min i (j - i) : ℕ) : ℝ) + 1 ≠ 0)] at hh

theorem timeCenter_le_linear (d : ℕ) :
    timeCenter d ≤ (5 / (2 * Real.exp 1)) * (d : ℝ) := by
  have hl : Real.log (d : ℝ) ≤ (d : ℝ) := Real.log_le_self (Nat.cast_nonneg d)
  have he : timeCenter d = (2 * (d : ℝ) + 3 * Real.log d) / (2 * Real.exp 1) := by
    unfold timeCenter
    field_simp
  rw [he, show 5 / (2 * Real.exp 1) * (d : ℝ) = (5 * d) / (2 * Real.exp 1) by ring]
  apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * Real.exp 1)).mpr
  linarith

end FreezingGrowth.PWIT
