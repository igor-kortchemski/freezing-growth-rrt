module

public import FreezingGrowth.ForwardPairAveraging
public import FreezingGrowth.HeightProfile

/-! Ordered-distinct depth-pair observables retaining the full old maximum.
Only the vertex-identity diagonal is removed. -/

@[expose] public section
namespace FreezingGrowth.Forward

open MeasureTheory
open scoped Classical

noncomputable def activePairHeightMean (s : State) (F : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  FiniteAveraging.distinctPairMean s.active
    (fun u v => if u = v then 0 else F (s.height u) (s.height v) (treeHeight s))

theorem average_activePairHeightMean_freeze {s : State} (hs : 3 ≤ s.active.card)
    (t : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ v ∈ s.active, activePairHeightMean (freeze s t v) F) / s.active.card =
      activePairHeightMean s F := by
  simpa only [activePairHeightMean, freeze, treeHeight] using
    FiniteAveraging.average_distinctPairMean_erase s.active
      (fun u v => if u = v then 0 else F (s.height u) (s.height v) (treeHeight s))
      hs (by intros; simp)

theorem transitionLaw_activePairHeightMean_freeze {s : State}
    (hs : 3 ≤ s.active.card) (t : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∫ s', activePairHeightMean s' F ∂transitionLaw s t false) =
      activePairHeightMean s F := by
  rw [transitionLaw_integral s t false (Finset.card_pos.mp (by omega))]
  convert average_activePairHeightMean_freeze hs t F using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [step, hv]

theorem treeLaw_activePairHeightMean_freeze (x : SignSequence) (n : ℕ)
    (hx : x (n + 1) = false) (hc : ∀ᵐ s ∂treeLaw x n, 3 ≤ s.active.card)
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∫ s, activePairHeightMean s F ∂treeLaw x (n + 1)) =
      ∫ s, activePairHeightMean s F ∂treeLaw x n := by
  rw [treeLaw_integral_succ_state, hx]
  apply integral_congr_ae
  filter_upwards [hc] with s hs
  exact transitionLaw_activePairHeightMean_freeze hs _ F

/-- With two active vertices, a symmetric observable of their depths and old
maximum is exactly its ordered-pair average. Multiset multiplicities survive. -/
theorem activePairHeightMean_profile_of_card_two {s : State}
    (hs : s.active.card = 2) (G : HeightProfile → ℝ) :
    activePairHeightMean s (fun a b M => G ⟨{a, b}, M⟩) = G (HeightProfile.ofState s) := by
  obtain ⟨u, v, huv, hS⟩ := Finset.card_eq_two.mp hs
  have hvu : v ≠ u := Ne.symm huv
  have hcomm : (⟨{s.height v, s.height u}, treeHeight s⟩ : HeightProfile) =
      ⟨{s.height u, s.height v}, treeHeight s⟩ := by
    congr 1
    exact Multiset.pair_comm _ _
  simp only [Multiset.insert_eq_cons] at hcomm
  simp [activePairHeightMean, FiniteAveraging.distinctPairMean,
    FiniteAveraging.pairSum, HeightProfile.ofState, hS, huv, hvu, hcomm]
  ring

end FreezingGrowth.Forward
