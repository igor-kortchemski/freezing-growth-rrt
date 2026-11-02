module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Finite grid bounds for a positive deficit. -/

@[expose] public section
namespace FreezingGrowth

open scoped Classical

/-- A finite indicator grid covers a positive real value, including grid endpoints. -/
theorem positivePart_le_grid {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (x : ℝ)
    (hx : x ≤ (N : ℝ) * L) :
    max x 0 ≤ L * ∑ j ∈ Finset.range N, (if (j : ℝ) * L < x then 1 else 0) := by
  induction N with
  | zero => simp only [Nat.cast_zero, zero_mul] at hx; simp [max_eq_right hx]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ (N : ℝ) * L
    · have hh := ih h
      split_ifs <;> nlinarith
    · have hsum : (∑ j ∈ Finset.range N, (if (j : ℝ) * L < x then (1 : ℝ) else 0)) = N := by
        have hf : ∀ j ∈ Finset.range N, (j : ℝ) * L < x := by
          intro j hj
          have hj' : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hj).le
          have hh := mul_le_mul_of_nonneg_right hj' hL
          linarith
        simp only [Finset.sum_ite_of_true hf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hsum, ite_eq_left (by linarith : (N : ℝ) * L < x)]
      apply max_le
      · push_cast at hx
        nlinarith
      · positivity

/-- A uniform upper bound on every finite geometric sum. -/
theorem geom_sum_le_inv_one_sub {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, ρ ^ j ≤ 1 / (1 - ρ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - ρ)).mpr
  have he := geom_sum_mul ρ N
  nlinarith [pow_nonneg hρ N]

end FreezingGrowth
