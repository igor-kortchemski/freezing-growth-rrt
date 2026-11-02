module

public import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

/-! Counting split indices with both components retaining a quarter of the vertices. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

/-- `n` is the total edge count, so the component vertex counts are
`k+1` and `n-k`. The empty case is retained. -/
def centralSplits (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun k => n + 1 ≤ 4 * (k + 1) ∧ n + 1 ≤ 4 * (n - k)

theorem centralSplits_eq_Ico (n : ℕ) :
    centralSplits n = Finset.Ico (n / 4) (n - n / 4) := by
  ext k
  simp only [centralSplits, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem card_centralSplits (n : ℕ) :
    (centralSplits n).card = n - 2 * (n / 4) := by
  rw [centralSplits_eq_Ico, Nat.card_Ico]
  omega

/-- At least half of the uniformly sampled indices are central. -/
theorem half_le_card_centralSplits (n : ℕ) :
    n ≤ 2 * (centralSplits n).card := by
  rw [card_centralSplits]
  omega

theorem centralSplits_subset_range (n : ℕ) : centralSplits n ⊆ Finset.range n :=
  Finset.filter_subset _ _

/-- Every split has a component with at least half the vertices. -/
theorem larger_component_vertices {n k : ℕ} (hk : k < n) :
    n + 1 ≤ 2 * max (k + 1) (n - k) := by
  have := le_max_left (k + 1) (n - k)
  have := le_max_right (k + 1) (n - k)
  omega

end FreezingGrowth.RRTSplit
