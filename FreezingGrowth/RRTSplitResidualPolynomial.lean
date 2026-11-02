module

public import FreezingGrowth.RRTSplitResidual

/-!
# Residual bounds throughout the ninth-power suffix range

The full floor-root scale requires all suffix lengths at least `m^9`, not
only the exact ninth powers. The proof compares logarithms directly and does
not assume monotonicity of the regularized lower center.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

theorem lowerCenter_half_ge_of_pow_nine_le {m n : ℕ} (hm : 2 ≤ m) (hmn : m ^ 9 ≤ n) :
    Real.exp 1 * Real.log ((m : ℝ) + 1) ≤ RRT.lowerCenter 2 (n / 2) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hln : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hpow : m ^ 8 ≤ n / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    calc
      m ^ 8 * 2 ≤ m ^ 8 * m := Nat.mul_le_mul_left _ hm
      _ = m ^ 9 := (pow_succ m 8).symm
      _ ≤ n := hmn
  have hsmall : (m : ℝ) + 1 ≤ (m : ℝ) ^ 2 := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlogsmall : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log (m : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ) + 1) hsmall
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hloglarge : 8 * Real.log (m : ℝ) ≤ Real.log ((n / 2 : ℕ) + (1 : ℝ)) := by
    have hcast : (m : ℝ) ^ 8 ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
      have hh : (m : ℝ) ^ 8 ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hpow
      linarith
    have hh := Real.log_le_log (pow_pos hmpos 8) hcast
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have he : 0 ≤ Real.exp 1 - 2 := by have := Real.exp_one_gt_two; linarith
  have hcoef : 2 * Real.exp 1 ≤ 8 * (Real.exp 1 - 2) := by
    have := Real.exp_one_gt_d9
    linarith
  calc
    Real.exp 1 * Real.log ((m : ℝ) + 1) ≤
        Real.exp 1 * (2 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogsmall (Real.exp_pos _).le
    _ ≤ (Real.exp 1 - 2) * (8 * Real.log (m : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcoef hln]
    _ ≤ (Real.exp 1 - 2) * Real.log ((n / 2 : ℕ) + (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglarge he
    _ ≤ RRT.lowerCenter 2 (n / 2) := RRT.lowerCenter_two_lower _

/-- One residual constant works simultaneously for all `m ≥ 2` and all
suffix lengths `n ≥ m^9`. -/
theorem uniformResidualBound_of_pow_nine_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m n : ℕ, 2 ≤ m → m ^ 9 ≤ n → residual m n ≤ C := by
  obtain ⟨C, hC, hres⟩ := uniformResidualBound
  exact ⟨C, hC, fun m n hm hmn => hres m n (lowerCenter_half_ge_of_pow_nine_le hm hmn)⟩

end FreezingGrowth.RRTSplit
