module

public import FreezingGrowth.ForwardPairSkeleton
public import FreezingGrowth.SeedDepthMaximum

/-! The source's original RRT and its two uniform surviving vertex IDs have
their full joint law, retaining the labelled graph, parents, and heights. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical

private def skeletonPrefixSigns (m : ℕ) : SignSequence := fun i => decide (i ≤ m)

private theorem skeletonPrefix_early (m j : ℕ) (hj : j ≤ m) :
    activeCount (skeletonPrefixSigns m) j = (j : ℤ) + 1 := by
  rw [show activeCount (skeletonPrefixSigns m) j = activeCount RRT.allAttach j from
    Word.activeCount_congr (by
      intro i hi
      simp [skeletonPrefixSigns, RRT.allAttach, show i + 1 ≤ m by omega])]
  exact RRT.activeCount_allAttach j

private theorem skeletonPrefix_late (m k : ℕ) :
    activeCount (skeletonPrefixSigns m) (m + k) = (m : ℤ) + 1 - k := by
  induction k with
  | zero => simpa using skeletonPrefix_early m m le_rfl
  | succ k ih =>
    rw [Nat.add_succ, activeCount_succ, ih]
    have he : skeletonPrefixSigns m (m + k + 1) = false := by
      simp [skeletonPrefixSigns, show ¬m + k + 1 ≤ m by omega]
    rw [he]
    push_cast
    ring

private theorem skeletonPrefix_positive (m k : ℕ) (hk : k ≤ m) :
    PositiveThrough (skeletonPrefixSigns m) (m + k) := by
  intro j hj
  by_cases hje : j ≤ m
  · rw [skeletonPrefix_early m j hje]
    omega
  · have he : m + (j - m) = j := by omega
    rw [← he, skeletonPrefix_late]
    have hr : j - m ≤ m := by omega
    omega

private theorem skeletonPrefix_card (m k : ℕ) (hk : k ≤ m) :
    ∀ᵐ s ∂Forward.treeLaw (skeletonPrefixSigns m) (m + k),
      (s.active.card : ℤ) = (m : ℤ) + 1 - k := by
  have ht := (lt_extinctionTime_iff (skeletonPrefixSigns m) (m + k)).mpr
    (skeletonPrefix_positive m k hk)
  filter_upwards [Forward.treeLaw_counts (skeletonPrefixSigns m) (m + k) ht.le] with s hs
  simpa only [skeletonPrefix_late] using hs.1

private theorem skeletonPrefix_pair_mean (m k : ℕ) (hk : k ≤ m - 1)
    (F : Forward.TreePairSample → ℝ) :
    (∫ s, Forward.activePairSkeletonMean s F
      ∂Forward.treeLaw (skeletonPrefixSigns m) (m + k)) =
      ∫ s, Forward.activePairSkeletonMean s F
        ∂Forward.treeLaw (skeletonPrefixSigns m) m := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = ∫ s, Forward.activePairSkeletonMean s F
          ∂Forward.treeLaw (skeletonPrefixSigns m) (m + k) := by
        rw [Nat.add_succ]
        apply Forward.treeLaw_activePairSkeletonMean_freeze (skeletonPrefixSigns m) (m + k)
        · simp [skeletonPrefixSigns, show ¬m + k + 1 ≤ m by omega]
        · filter_upwards [skeletonPrefix_card m k (by omega)] with s hs
          omega
      _ = _ := ih (by omega)

private theorem skeletonPrefix_sign (m k i : ℕ) :
    Word.toSigns (List.replicate m true ++ List.replicate k false) (i + 1) =
      skeletonPrefixSigns m (i + 1) := by
  rw [Word.toSigns_succ]
  by_cases hi : i < m
  · rw [List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_replicate_of_lt hi, skeletonPrefixSigns, show i + 1 ≤ m by omega]
  · simp [List.getElem?_append, List.length_replicate, hi,
      List.getElem?_replicate, skeletonPrefixSigns, show ¬i + 1 ≤ m by omega]
    split_ifs <;> rfl

theorem twoActivePrefix_pair_skeleton_mean (m : ℕ) (_hm : 1 ≤ m)
    (F : Forward.TreePairSample → ℝ) :
    (∫ s, Forward.activePairSkeletonMean s F
      ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length) =
      ∫ s, Forward.activePairSkeletonMean s F ∂Forward.treeLaw RRT.allAttach m := by
  have hl : (twoActivePrefix m).length = m + (m - 1) := by simp [twoActivePrefix]
  rw [hl, Forward.treeLaw_congr (x := (twoActivePrefix m).toSigns)
    (y := skeletonPrefixSigns m) (fun i _ => skeletonPrefix_sign m (m - 1) i),
    skeletonPrefix_pair_mean m (m - 1) le_rfl F]
  rw [Forward.treeLaw_congr (x := skeletonPrefixSigns m) (y := RRT.allAttach)
    (fun i hi => by simp [skeletonPrefixSigns, RRT.allAttach, show i + 1 ≤ m by omega])]

theorem RRT.treeLaw_two_le_active_card (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ s ∂Forward.treeLaw RRT.allAttach m, 2 ≤ s.active.card := by
  filter_upwards [Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs
  have hc : (s.active.card : ℤ) = (m : ℤ) + 1 := by
    simpa only [RRT.activeCount_allAttach] using hs.1
  omega

/-- Equality of the original labelled tree and its ordered surviving pair,
including their full dependence. No graph or vertex label is projected away. -/
theorem twoActivePrefix_treePairLaw (m : ℕ) (hm : 1 ≤ m) :
    Forward.treePairLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length =
      Forward.treePairLaw RRT.allAttach m := by
  have hp : ∀ᵐ s ∂Forward.treeLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length,
      2 ≤ s.active.card := (twoActivePrefix_active_card m hm).mono (fun _ hs => by omega)
  have hr := RRT.treeLaw_two_le_active_card m hm
  let := Forward.treePairLaw_probability _ _ hp
  let := Forward.treePairLaw_probability _ _ hr
  apply TwoSeedCoupling.measures_eq_of_integrals
  intro F
  rw [Forward.treePairLaw_integral _ _ hp, Forward.treePairLaw_integral _ _ hr]
  exact twoActivePrefix_pair_skeleton_mean m hm F

/-- Conditional on the actual original RRT, sample uniformly among all ordered
distinct vertex pairs. This is the complete tree-and-pair form of source I1. -/
theorem twoActivePrefix_treePairLaw_eq_bind_vertices (m : ℕ) (hm : 1 ≤ m) :
    Forward.treePairLaw (twoActivePrefix m).toSigns (twoActivePrefix m).length =
      (Forward.treeLaw RRT.allAttach m).bind (fun s =>
        (uniformRootPair s.vertices).map (Forward.treePairSample s)) := by
  rw [twoActivePrefix_treePairLaw m hm, Forward.treePairLaw]
  apply Measure.bind_congr_right
  filter_upwards [RRT.active_eq_vertices m] with s hs
  simp only [Forward.activeTreePairLaw, hs]

end FreezingGrowth
