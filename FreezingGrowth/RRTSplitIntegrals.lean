module

public import FreezingGrowth.RRTSplitSymmetry
public import FreezingGrowth.RRTMeanUpper

/-! Integration of the two actual first-edge component heights. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open MeasureTheory
open scoped Classical

def splitHeights (n : ℕ) (s : Forward.State) : ℕ × ℕ :=
  (Forward.treeHeight (split n s).rootSide.tree,
    Forward.treeHeight (split n s).childSide.tree)

theorem heightPairLaw_eq_map (n : ℕ) : heightPairLaw n =
    (Forward.treeLaw RRT.allAttach (n + 1)).map (splitHeights n) := by
  rw [heightPairLaw, pairLaw,
    Measure.map_map measurable_heightPair measurable_from_top]
  rfl

theorem splitHeights_ae_bound (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw RRT.allAttach (n + 1),
      (splitHeights n s).1 ≤ n + 1 ∧ (splitHeights n s).2 ≤ n + 1 := by
  filter_upwards [treeLaw_height_split n, Forward.treeLaw_valid RRT.allAttach (n + 1)]
    with s hs hv
  have hbound := hv.treeHeight_le
  change Forward.treeHeight s = max (splitHeights n s).1 ((splitHeights n s).2 + 1) at hs
  omega

theorem heightPairLaw_integrable (n : ℕ) (f : ℕ × ℕ → ℝ) :
    Integrable f (heightPairLaw n) := by
  rw [heightPairLaw_eq_map]
  apply (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    measurable_from_top.aemeasurable).mpr
  let I := (Finset.range (n + 2)).product (Finset.range (n + 2))
  let C : ℝ := ∑ p ∈ I, |f p|
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [splitHeights_ae_bound n] with s hs
  rw [Real.norm_eq_abs]
  apply Finset.single_le_sum (f := fun p : ℕ × ℕ => |f p|) (fun _ _ => abs_nonneg _)
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega)⟩

theorem integral_max_heightPairLaw (n : ℕ) :
    (∫ p, (max p.1 (p.2 + 1) : ℝ) ∂heightPairLaw n) = RRT.meanHeight (n + 1) := by
  rw [heightPairLaw_eq_map, integral_map measurable_from_top.aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [treeLaw_height_split n] with s hs
  simpa only [Nat.cast_max, Nat.cast_add, Nat.cast_one, splitHeights] using
    congrArg (fun k : ℕ => (k : ℝ)) hs.symm

theorem heightPairLaw_height_one (n : ℕ) :
    (heightPairLaw n).real {p | max p.1 (p.2 + 1) = 1} =
      (1 : ℝ) / ((n + 1).factorial : ℝ) := by
  rw [heightPairLaw_eq_map,
    map_measureReal_apply measurable_from_top (Set.to_countable _).measurableSet]
  have he : (Forward.treeLaw RRT.allAttach (n + 1)).real
      {s | max (splitHeights n s).1 ((splitHeights n s).2 + 1) = 1} =
      (Forward.heightLaw RRT.allAttach (n + 1)).real {1} := by
    rw [Forward.heightLaw, map_measureReal_apply measurable_from_top (by trivial)]
    apply measureReal_congr
    filter_upwards [treeLaw_height_split n] with s hs
    change (max (splitHeights n s).1 ((splitHeights n s).2 + 1) = 1) =
      (Forward.treeHeight s = 1)
    exact congrArg (fun k => k = 1) hs.symm
  exact he.trans (RRT.height_one_real_mass (by omega))

end FreezingGrowth.RRTSplit
