module

public import FreezingGrowth.RRTCentralSplits
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Averaging a uniform bound that improves on at least half the split indices. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open scoped Classical

/-- Central terms improve by a factor `1-p`. -/
theorem split_average_contraction {N : ℕ} (hN : 0 < N) {a p : ℝ}
    (ha : 0 ≤ a) (hp : 0 ≤ p) (f : ℕ → ℝ)
    (hall : ∀ k ∈ Finset.range N, f k ≤ a)
    (hcentral : ∀ k ∈ centralSplits N, f k ≤ a * (1 - p)) :
    (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f k ≤ a * (1 - p / 2) := by
  have hfilter : (Finset.range N).filter (fun k => k ∈ centralSplits N) =
      centralSplits N := Finset.filter_mem_eq_inter.trans
        (Finset.inter_eq_right.mpr (centralSplits_subset_range N))
  have hs : (∑ k ∈ Finset.range N, f k) ≤
      (N : ℝ) * a - ((centralSplits N).card : ℝ) * (a * p) := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, (a - if k ∈ centralSplits N then a * p else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hc : k ∈ centralSplits N
        · simp only [hc, ite_true]
          nlinarith [hcentral k hc]
        · simp only [hc, ite_false, sub_zero]
          exact hall k hk
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.sum_filter, hfilter]
        simp
  have hh : (N : ℝ) ≤ 2 * ((centralSplits N).card : ℝ) := by
    exact_mod_cast half_le_card_centralSplits N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1 / (N : ℝ))).trans
  rw [one_div, mul_comm (N : ℝ)⁻¹, ← div_eq_mul_inv]
  apply (div_le_iff₀ hNr).mpr
  nlinarith [mul_nonneg ha hp, mul_le_mul_of_nonneg_right hh (mul_nonneg ha hp)]

end FreezingGrowth.RRTSplit
