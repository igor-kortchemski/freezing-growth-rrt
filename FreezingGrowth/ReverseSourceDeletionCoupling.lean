module

public import FreezingGrowth.ReverseSourceShorterHistory

/-! The original Algorithm 3 pathwise deletion comparison, with both actual
whole-history marginals supplied by the preceding construction. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

theorem sourceLongerHistoryLaw_current (k : ℕ) (tail : Word) :
    (sourceLongerHistoryLaw k tail).map FiniteMarkov.History.current =
      (sourceDelayedLaw k tail (k - 1)).map longerForest := by
  rw [sourceLongerHistoryLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    sourceDelayedLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  have htail : initializationTailLaw k tail =
      (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
        tail.length).map FiniteMarkov.History.current :=
    (orderedHistoryLaw_current _ _ _).symm
  rw [htail, Measure.bind_map
    (m := orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length tail.length)
    (f := FiniteMarkov.History.current)
    (g := fun F => (delayedLawAfter F k (k - 1)).map longerForest)
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  congr 1
  funext h
  rw [Measure.map_map measurable_from_top measurable_from_top,
    ← delayedHistoryLaw_current h.current k (k - 1),
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

theorem sourceDelayedLaw_longer_treeLaw (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    (sourceDelayedLaw k tail (k - 1)).map longerForest =
      Reverse.treeLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length := by
  rw [← sourceLongerHistoryLaw_current, sourceLongerHistoryLaw_eq k hk tail ha,
    graphHistoryLaw_current]
  rfl

theorem sourceDelayedLaw_longer_heightLaw (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    (sourceDelayedLaw k tail (k - 1)).map (fun z => z.longer.forest.maxDepth) =
      (reversePeakWord k tail).heightLaw := by
  rw [Word.heightLaw_eq_reverseHeightLaw _ ha, Reverse.heightLaw,
    ← sourceDelayedLaw_longer_treeLaw k hk tail ha,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

theorem sourceDelayedLaw_shorter_heightLaw (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    (sourceDelayedLaw k tail (k - 1)).map (fun z => z.shorter.forest.maxDepth) =
      (reverseDeletedWord k tail).heightLaw := by
  have hshort : (reverseDeletedWord k tail).admissible :=
    Word.first_peak_deletion_admissible k hk tail ha
  rw [Word.heightLaw_eq_orderedReverseHeightLaw _ hshort, heightLaw,
    ← sourceDelayedLaw_shorter_treeLaw k hk tail ha,
    Measure.map_map measurable_from_top measurable_from_top]
  congr 1
  funext z
  exact (relabel_maxDepth z.shorter _).symm

/-- Source C8, using the paper's actual delayed-pair construction: both
height laws are identified and terminal domination holds on that same law. -/
theorem sourceCoupling_heightLE (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    Word.HeightLE (reverseDeletedWord k tail) (reversePeakWord k tail) := by
  intro h
  change (reverseDeletedWord k tail).heightLaw {z | h ≤ z} ≤
    (reversePeakWord k tail).heightLaw {z | h ≤ z}
  rw [← sourceDelayedLaw_shorter_heightLaw k hk tail ha,
    ← sourceDelayedLaw_longer_heightLaw k hk tail ha,
    Measure.map_apply measurable_from_top MeasurableSet.of_discrete,
    Measure.map_apply measurable_from_top MeasurableSet.of_discrete]
  apply measure_mono_ae
  filter_upwards [sourceDelayedLaw_terminal_maxDepth_le k hk tail ha] with z hz
  exact fun hh => hh.trans hz

end FreezingGrowth.ReverseOrdered
