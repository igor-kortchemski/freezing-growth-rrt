module

public import FreezingGrowth.ReverseOrderedForest
public import FreezingGrowth.ReverseHeightBridge

/-! The actual maximum-height law of the ordered source Algorithm 2. -/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory

namespace ReverseOrdered

noncomputable def heightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).map (fun F => F.forest.maxDepth)

instance heightLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (heightLaw x n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable).mpr inferInstance

/-- The final component list has exactly one entry. -/
theorem treeLaw_unique_component (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂treeLaw x n, F.rootOrder.length = 1 := by
  simpa [treeLaw] using lawAfter_rootOrder_length x n n hn le_rfl

theorem heightLaw_eq_reverseHeightLaw (x : SignSequence) (n : ℕ) :
    heightLaw x n = Reverse.heightLaw x n := by
  unfold heightLaw Reverse.heightLaw
  rw [← map_treeLaw x n, Measure.map_map measurable_from_top measurable_from_top]
  rfl

/-- Ordered-list Algorithm 2 and the genuine forward Algorithm 1 have the
same maximum-height law, also when the schedule ends at extinction. -/
theorem heightLaw_eq_forwardHeightLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    heightLaw x n = Forward.heightLaw x n :=
  (heightLaw_eq_reverseHeightLaw x n).trans (Forward.heightLaw_eq_reverseHeightLaw x n hn).symm

end ReverseOrdered

namespace Word

/-- The source height-law equivalence for every admissible finite word. -/
theorem heightLaw_eq_orderedReverseHeightLaw (xs : Word) (ha : xs.admissible) :
    xs.heightLaw = ReverseOrdered.heightLaw xs.toSigns xs.length :=
  (ReverseOrdered.heightLaw_eq_forwardHeightLaw xs.toSigns xs.length
    ((admissible_iff_le_extinctionTime xs).mp ha)).symm

end Word
end FreezingGrowth
