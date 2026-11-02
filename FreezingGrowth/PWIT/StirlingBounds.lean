module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic

/-!
# Uniform factorial bounds for generation intensities

The constants are explicit and independent of the generation. These bounds
are ingredients for the critical endpoint and rank windows; they do not by
themselves assert either window estimate.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

theorem factorial_le_stirling_upper {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have hs : Stirling.stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, zero_add,
      Stirling.stirlingSeq_one] using Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hden : 0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  change (n.factorial : ℝ) / (Real.sqrt (2 * n) * ((n : ℝ) / Real.exp 1) ^ n) ≤
    Real.exp 1 / Real.sqrt 2 at hs
  have hf := (div_le_iff₀ hden).mp hs
  calc
    _ ≤ (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := hf
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp

theorem factorial_stirling_bounds {n : ℕ} (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n :=
  ⟨Stirling.le_factorial_stirling n, factorial_le_stirling_upper hn⟩

end FreezingGrowth.PWIT
