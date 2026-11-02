module

public import FreezingGrowth.ForwardPairMaximum
public import FreezingGrowth.RRTDepthGap

/-! Integration and linearity for the actual ordered-distinct vertex average,
including its dependence on the tree's retained maximum. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

theorem uniformRootPair_integrable (s : Finset ℕ) (hs : 2 ≤ s.card)
    (f : ℕ × ℕ → ℝ) : Integrable f (uniformRootPair s) := by
  unfold uniformRootPair Measure.uniformOfFinset
  apply integrable_finsetSum_measure.mpr
  intro p _
  apply Integrable.smul_measure (integrable_dirac (by simp))
  exact ENNReal.inv_ne_top.mpr (by
    exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')

namespace Forward

theorem activePairHeightMean_eq_integral (s : State) (hs : 2 ≤ s.active.card)
    (F : ℕ → ℕ → ℕ → ℝ) :
    activePairHeightMean s F =
      ∫ p, F (s.height p.1) (s.height p.2) (treeHeight s) ∂uniformRootPair s.active := by
  have he : s.active.offDiag =
      (s.active ×ˢ s.active).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum : (∑ p ∈ s.active.offDiag, F (s.height p.1) (s.height p.2) (treeHeight s)) =
      FiniteAveraging.pairSum s.active
        (fun u v => if u = v then 0 else F (s.height u) (s.height v) (treeHeight s)) := by
    rw [he, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v <;> simp [huv]
  unfold activePairHeightMean FiniteAveraging.distinctPairMean
  rw [← hsum, ← card_offDiag_real s.active (by omega)]
  unfold uniformRootPair Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro p _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    exact ENNReal.inv_ne_top.mpr (by
      exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')

theorem activePairHeightMean_const (s : State) (hs : 2 ≤ s.active.card) (f : ℕ → ℝ) :
    activePairHeightMean s (fun _ _ M => f M) = f (treeHeight s) := by
  let := uniformRootPair_isProbabilityMeasure s.active hs
  rw [activePairHeightMean_eq_integral s hs]
  simp

theorem activePairHeightMean_sub (s : State) (hs : 2 ≤ s.active.card)
    (F G : ℕ → ℕ → ℕ → ℝ) :
    activePairHeightMean s (fun a b M => F a b M - G a b M) =
      activePairHeightMean s F - activePairHeightMean s G := by
  rw [activePairHeightMean_eq_integral s hs, activePairHeightMean_eq_integral s hs F,
    activePairHeightMean_eq_integral s hs G]
  simpa only [Pi.sub_apply] using integral_sub
    (uniformRootPair_integrable s.active hs (fun p => F (s.height p.1) (s.height p.2) (treeHeight s)))
    (uniformRootPair_integrable s.active hs (fun p => G (s.height p.1) (s.height p.2) (treeHeight s)))

theorem activePairHeightMean_const_mul (s : State) (hs : 2 ≤ s.active.card)
    (c : ℝ) (F : ℕ → ℕ → ℕ → ℝ) :
    activePairHeightMean s (fun a b M => c * F a b M) = c * activePairHeightMean s F := by
  rw [activePairHeightMean_eq_integral s hs, activePairHeightMean_eq_integral s hs F,
    integral_const_mul]

theorem activePairHeightMean_depth_gap (s : State) (hs : 2 ≤ s.active.card) :
    activePairHeightMean s (fun a b _ => |(a : ℝ) - b|) = RRT.treeDistinctDepthGap s := by
  rw [activePairHeightMean_eq_integral s hs, RRT.treeDistinctDepthGap_eq_integral s hs]

theorem activePairHeightMean_mono (s : State) (hs : 2 ≤ s.active.card)
    (F G : ℕ → ℕ → ℕ → ℝ)
    (hFG : ∀ u ∈ s.active, ∀ v ∈ s.active, u ≠ v →
      F (s.height u) (s.height v) (treeHeight s) ≤
        G (s.height u) (s.height v) (treeHeight s)) :
    activePairHeightMean s F ≤ activePairHeightMean s G := by
  have hN : (2 : ℝ) ≤ s.active.card := by exact_mod_cast hs
  unfold activePairHeightMean FiniteAveraging.distinctPairMean FiniteAveraging.pairSum
  apply div_le_div_of_nonneg_right _ (by nlinarith)
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  by_cases huv : u = v
  · simp [huv]
  · simpa only [ite_eq_right huv] using hFG u hu v hv huv

end Forward
end FreezingGrowth
