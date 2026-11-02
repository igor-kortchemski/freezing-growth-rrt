module

public import FreezingGrowth.FinitePairAveraging
public import FreezingGrowth.ForwardHeight
public import FreezingGrowth.ForwardFiniteSupport

/-! Uniform freezing preserves an ordered-distinct active-pair statistic.
The zero diagonal is a condition on the statistic, not a deletion of pairs of
different vertices that happen to have the same depth. -/

@[expose] public section
namespace FreezingGrowth.Forward

open MeasureTheory
open scoped Classical

noncomputable def activeDistinctPairMean (s : State) (f : ℕ → ℕ → ℝ) : ℝ :=
  FiniteAveraging.distinctPairMean s.active (fun u v => f (s.height u) (s.height v))

theorem average_activeDistinctPairMean_freeze {s : State} (hs : 3 ≤ s.active.card)
    (t : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ k, f k k = 0) :
    (∑ v ∈ s.active, activeDistinctPairMean (freeze s t v) f) / s.active.card =
      activeDistinctPairMean s f := by
  simpa only [activeDistinctPairMean, freeze] using
    FiniteAveraging.average_distinctPairMean_erase s.active
      (fun u v => f (s.height u) (s.height v)) hs (fun v _ => hf (s.height v))

theorem transitionLaw_activeDistinctPairMean_freeze {s : State}
    (hs : 3 ≤ s.active.card) (t : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ k, f k k = 0) :
    (∫ s', activeDistinctPairMean s' f ∂transitionLaw s t false) =
      activeDistinctPairMean s f := by
  rw [transitionLaw_integral s t false (Finset.card_pos.mp (by omega))]
  convert average_activeDistinctPairMean_freeze hs t f hf using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [step, hv]

theorem treeLaw_activeDistinctPairMean_freeze (x : SignSequence) (n : ℕ)
    (hx : x (n + 1) = false)
    (hc : ∀ᵐ s ∂treeLaw x n, 3 ≤ s.active.card)
    (f : ℕ → ℕ → ℝ) (hf : ∀ k, f k k = 0) :
    (∫ s, activeDistinctPairMean s f ∂treeLaw x (n + 1)) =
      ∫ s, activeDistinctPairMean s f ∂treeLaw x n := by
  rw [treeLaw_integral_succ_state, hx]
  apply integral_congr_ae
  filter_upwards [hc] with s hs
  exact transitionLaw_activeDistinctPairMean_freeze hs _ f hf

end FreezingGrowth.Forward
