module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Group the two orientations of a uniform split by the larger component. -/

@[expose] public section
namespace FreezingGrowth

theorem sum_larger_component_le (n : ℕ) (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k)
    (q : ℝ) (hq : 0 ≤ q) :
    (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then u k else q * u (n - 1 - k)) ≤
      (1 + q) * ∑ k ∈ Finset.Ico (n / 2) n, u k := by
  let f : ℕ → ℝ := fun k => if n / 2 ≤ k then u k else 0
  have hsum : (∑ k ∈ Finset.range n, f k) = ∑ k ∈ Finset.Ico (n / 2) n, u k := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  have hfirst : (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then u k else 0) =
      ∑ k ∈ Finset.range n, f k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : n - 1 - k ≤ k ↔ n / 2 ≤ k := by omega
    simp only [he, f]
  have hsecond : (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then 0 else u (n - 1 - k)) ≤
      ∑ k ∈ Finset.range n, f k := by
    rw [← Finset.sum_range_reflect
      (fun k => if n - 1 - k ≤ k then 0 else u (n - 1 - k)) n]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : n - 1 - (n - 1 - k) = k := by omega
    rw [he]
    by_cases hc : k ≤ n - 1 - k
    · simp only [hc, ↓reduceIte]
      dsimp [f]
      split_ifs
      · exact hu k
      · exact le_rfl
    · have hh : n / 2 ≤ k := by omega
      simp only [hc, ↓reduceIte, f, hh]
      exact le_rfl
  have hsplit : (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then u k else q * u (n - 1 - k)) =
      (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then u k else 0) +
        q * (∑ k ∈ Finset.range n, if n - 1 - k ≤ k then 0 else u (n - 1 - k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  rw [hsplit, hfirst, ← hsum]
  nlinarith [mul_le_mul_of_nonneg_left hsecond hq]

end FreezingGrowth
