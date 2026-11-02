module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-! A telescoping criterion for arbitrarily late small increments. -/

@[expose] public section
namespace FreezingGrowth

theorem exists_small_increment_of_affine_upper (a : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hupper : ∃ C : ℝ, ∀ n : ℕ, a n ≤ ε / 2 * n + C)
    (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ a (n + 1) - a n < ε := by
  by_contra hnone
  have hlarge : ∀ n : ℕ, N ≤ n → ε ≤ a (n + 1) - a n := by
    intro n hn
    exact le_of_not_gt (fun h => hnone ⟨n, hn, h⟩)
  obtain ⟨C, hC⟩ := hupper
  have hlower (k : ℕ) : a N + (k : ℝ) * ε ≤ a (N + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := hlarge (N + k) (Nat.le_add_right _ _)
      push_cast
      rw [Nat.add_succ]
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((C + ε / 2 * N - a N) / (ε / 2))
  have hmul := (div_lt_iff₀ (half_pos hε)).mp hk
  have hlo := hlower k
  have hhi := hC (N + k)
  push_cast at hhi
  nlinarith

end FreezingGrowth
