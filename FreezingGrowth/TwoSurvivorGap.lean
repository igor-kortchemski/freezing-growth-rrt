module

public import FreezingGrowth.ForwardPairAveraging
public import FreezingGrowth.ForwardPairMaximum
public import FreezingGrowth.RRTDepthGap
public import FreezingGrowth.MainStatements

/-! The two active vertices in the paper's prefix have the original RRT's
ordered-distinct absolute depth-gap expectation. This identifies the observable
needed by the main comparison, without assuming a joint depth limit theorem. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory Filter
open scoped Classical Topology

private def attachThenFreeze (m : ℕ) : SignSequence := fun i => decide (i ≤ m)

private theorem attachThenFreeze_early (m j : ℕ) (hj : j ≤ m) :
    activeCount (attachThenFreeze m) j = (j : ℤ) + 1 := by
  rw [show activeCount (attachThenFreeze m) j = activeCount RRT.allAttach j from
    Word.activeCount_congr (by
      intro i hi
      simp [attachThenFreeze, RRT.allAttach, show i + 1 ≤ m by omega])]
  exact RRT.activeCount_allAttach j

private theorem attachThenFreeze_late (m k : ℕ) :
    activeCount (attachThenFreeze m) (m + k) = (m : ℤ) + 1 - k := by
  induction k with
  | zero => simpa using attachThenFreeze_early m m le_rfl
  | succ k ih =>
    rw [Nat.add_succ, activeCount_succ, ih]
    have he : attachThenFreeze m (m + k + 1) = false := by
      simp [attachThenFreeze, show ¬m + k + 1 ≤ m by omega]
    rw [he]
    push_cast
    ring

private theorem attachThenFreeze_positive (m k : ℕ) (hk : k ≤ m) :
    PositiveThrough (attachThenFreeze m) (m + k) := by
  intro j hj
  by_cases hje : j ≤ m
  · rw [attachThenFreeze_early m j hje]
    omega
  · have he : m + (j - m) = j := by omega
    rw [← he, attachThenFreeze_late]
    have hr : j - m ≤ m := by omega
    omega

private theorem attachThenFreeze_card (m k : ℕ) (hk : k ≤ m) :
    ∀ᵐ s ∂Forward.treeLaw (attachThenFreeze m) (m + k),
      (s.active.card : ℤ) = (m : ℤ) + 1 - k := by
  have ht := (lt_extinctionTime_iff (attachThenFreeze m) (m + k)).mpr
    (attachThenFreeze_positive m k hk)
  filter_upwards [Forward.treeLaw_counts (attachThenFreeze m) (m + k) ht.le] with s hs
  simpa only [attachThenFreeze_late] using hs.1

private theorem attachThenFreeze_pair_mean (m k : ℕ) (hk : k ≤ m - 1)
    (f : ℕ → ℕ → ℝ) (hf : ∀ a, f a a = 0) :
    (∫ s, Forward.activeDistinctPairMean s f ∂Forward.treeLaw (attachThenFreeze m) (m + k)) =
      ∫ s, Forward.activeDistinctPairMean s f ∂Forward.treeLaw (attachThenFreeze m) m := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∫ s, Forward.activeDistinctPairMean s f
          ∂Forward.treeLaw (attachThenFreeze m) (m + k) := by
        rw [Nat.add_succ]
        apply Forward.treeLaw_activeDistinctPairMean_freeze
          (attachThenFreeze m) (m + k)
        · simp [attachThenFreeze, show ¬m + k + 1 ≤ m by omega]
        · filter_upwards [attachThenFreeze_card m k (by omega)] with s hs
          omega
        · exact hf
      _ = _ := ih (by omega)

private theorem prefix_sign (m k i : ℕ) :
    Word.toSigns (List.replicate m true ++ List.replicate k false) (i + 1) =
      attachThenFreeze m (i + 1) := by
  rw [Word.toSigns_succ]
  by_cases hi : i < m
  · rw [List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_replicate_of_lt hi, attachThenFreeze, show i + 1 ≤ m by omega]
  · simp [List.getElem?_append, List.length_replicate, hi,
      List.getElem?_replicate, attachThenFreeze, show ¬i + 1 ≤ m by omega]
    split_ifs <;> rfl

theorem twoActivePrefix_active_card (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ s ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length,
      s.active.card = 2 := by
  have hl : (twoActivePrefix m).length = m + (m - 1) := by
    simp [twoActivePrefix]
  rw [hl, Forward.treeLaw_congr (x := (twoActivePrefix m).toSigns)
    (y := attachThenFreeze m) (fun i _ => prefix_sign m (m - 1) i)]
  filter_upwards [attachThenFreeze_card m (m - 1) (by omega)] with s hs
  omega

/-- Uniform successive freezing preserves every zero-diagonal pair observable.
In particular it preserves the absolute depth gap, including equal-depth pairs. -/
theorem twoActivePrefix_pair_mean (m : ℕ) (_hm : 1 ≤ m)
    (f : ℕ → ℕ → ℝ) (hf : ∀ a, f a a = 0) :
    (∫ s, Forward.activeDistinctPairMean s f
      ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length) =
      ∫ s, Forward.activeDistinctPairMean s f ∂Forward.treeLaw RRT.allAttach m := by
  have hl : (twoActivePrefix m).length = m + (m - 1) := by simp [twoActivePrefix]
  rw [hl, Forward.treeLaw_congr (x := (twoActivePrefix m).toSigns)
    (y := attachThenFreeze m) (fun i _ => prefix_sign m (m - 1) i),
    attachThenFreeze_pair_mean m (m - 1) le_rfl f hf]
  rw [Forward.treeLaw_congr (x := attachThenFreeze m) (y := RRT.allAttach)
    (fun i hi => by simp [attachThenFreeze, RRT.allAttach, show i + 1 ≤ m by omega])]

private theorem attachThenFreeze_pair_height_mean (m k : ℕ) (hk : k ≤ m - 1)
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∫ s, Forward.activePairHeightMean s F ∂Forward.treeLaw (attachThenFreeze m) (m + k)) =
      ∫ s, Forward.activePairHeightMean s F ∂Forward.treeLaw (attachThenFreeze m) m := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∫ s, Forward.activePairHeightMean s F
          ∂Forward.treeLaw (attachThenFreeze m) (m + k) := by
        rw [Nat.add_succ]
        apply Forward.treeLaw_activePairHeightMean_freeze
          (attachThenFreeze m) (m + k)
        · simp [attachThenFreeze, show ¬m + k + 1 ≤ m by omega]
        · filter_upwards [attachThenFreeze_card m k (by omega)] with s hs
          omega
      _ = _ := ih (by omega)

/-- All depth-pair and full-maximum observables retain the dependence on the
original random recursive tree. The vertex-label diagonal is removed. -/
theorem twoActivePrefix_pair_height_mean (m : ℕ) (_hm : 1 ≤ m)
    (F : ℕ → ℕ → ℕ → ℝ) :
    (∫ s, Forward.activePairHeightMean s F
      ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length) =
      ∫ s, Forward.activePairHeightMean s F ∂Forward.treeLaw RRT.allAttach m := by
  have hl : (twoActivePrefix m).length = m + (m - 1) := by simp [twoActivePrefix]
  rw [hl, Forward.treeLaw_congr (x := (twoActivePrefix m).toSigns)
    (y := attachThenFreeze m) (fun i _ => prefix_sign m (m - 1) i),
    attachThenFreeze_pair_height_mean m (m - 1) le_rfl F]
  rw [Forward.treeLaw_congr (x := attachThenFreeze m) (y := RRT.allAttach)
    (fun i hi => by simp [attachThenFreeze, RRT.allAttach, show i + 1 ≤ m by omega])]

theorem twoActivePrefix_profile_integral (m : ℕ) (hm : 1 ≤ m)
    (G : HeightProfile → ℝ) :
    (∫ p, G p ∂HeightProfile.law (twoActivePrefix m).toSigns (twoActivePrefix m).length) =
      ∫ s, Forward.activePairHeightMean s (fun a b M => G ⟨{a, b}, M⟩)
        ∂Forward.treeLaw RRT.allAttach m := by
  rw [← HeightProfile.map_treeLaw,
    integral_map measurable_from_top.aemeasurable measurable_from_top.aestronglyMeasurable,
    ← twoActivePrefix_pair_height_mean m hm]
  apply integral_congr_ae
  filter_upwards [twoActivePrefix_active_card m hm] with s hs
  exact (Forward.activePairHeightMean_profile_of_card_two hs G).symm

noncomputable def expectedTwoSurvivorGap (m : ℕ) : ℝ :=
  ∫ s, RRT.treeDistinctDepthGap s
    ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length

theorem expectedTwoSurvivorGap_eq (m : ℕ) (hm : 1 ≤ m) :
    expectedTwoSurvivorGap m = RRT.expectedDistinctDepthGap m := by
  exact twoActivePrefix_pair_mean m hm (fun a b => |(a : ℝ) - b|) (by simp)

theorem tendsto_expectedTwoSurvivorGap_atTop :
    Tendsto expectedTwoSurvivorGap atTop atTop := by
  apply RRT.tendsto_expectedDistinctDepthGap_atTop.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (expectedTwoSurvivorGap_eq m hm).symm

end FreezingGrowth
