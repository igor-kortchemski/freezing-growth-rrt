module

public import FreezingGrowth.SeededWordLaw
public import FreezingGrowth.RRTSplitIntegrals

/-! Expectations of seeded growth, identified with the genuine split law. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical

def seedHeight (a b M : ℕ) (p : ℕ × ℕ) : ℕ := max M (max (a + p.1) (b + p.2))

theorem pairLaw_eq_map_mixture (n : ℕ) : RRTSplit.pairLaw n =
    (RRTSplit.mixtureLaw n).map Prod.snd := by
  rw [← RRTSplit.treeLaw_firstEdgeSplit n,
    Measure.map_map measurable_snd measurable_from_top]
  rfl

theorem join_seed_maximum_law (a b M : ℕ) (hab : max a b ≤ M) (n : ℕ) :
    (grow ⟨{a, b}, M⟩ n).map maximum =
      (RRTSplit.heightPairLaw n).map (seedHeight a b M) := by
  rw [join_seed_growth a b M hab, RRTSplit.heightPairLaw, pairLaw_eq_map_mixture,
    Measure.map_map RRTSplit.measurable_heightPair measurable_snd,
    Measure.map_map (measurable_of_countable _) (RRTSplit.measurable_heightPair.comp measurable_snd),
    Measure.map_map measurable_from_top (measurable_project a b M)]
  rfl

theorem join_seed_integrable (a b M : ℕ) (hab : max a b ≤ M) (n : ℕ) :
    Integrable (fun p => (p.maximum : ℝ)) (grow ⟨{a, b}, M⟩ n) := by
  apply (integrable_map_measure (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable
    measurable_from_top.aemeasurable).mp
  rw [join_seed_maximum_law a b M hab]
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr
      (RRTSplit.heightPairLaw_integrable n (fun p => (seedHeight a b M p : ℝ)))

theorem join_seed_mean (a b M : ℕ) (hab : max a b ≤ M) (n : ℕ) :
    (∫ p, (p.maximum : ℝ) ∂grow ⟨{a, b}, M⟩ n) =
      ∫ p, (seedHeight a b M p : ℝ) ∂RRTSplit.heightPairLaw n := by
  rw [← integral_map measurable_from_top.aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable,
    join_seed_maximum_law a b M hab,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]

theorem single_seed_integrable (a M : ℕ) (ha : a ≤ M) (n : ℕ) :
    Integrable (fun p => (p.maximum : ℝ)) (grow ⟨{a}, M⟩ n) := by
  rw [single_seed_growth a M ha]
  apply (integrable_map_measure measurable_from_top.aestronglyMeasurable
    measurable_from_top.aemeasurable).mpr
  exact Forward.treeLaw_integrable_heightTest RRT.allAttach n
    (fun k => ((max M (a + k) : ℕ) : ℝ))

theorem single_seed_mean (a M : ℕ) (ha : a ≤ M) (n : ℕ) :
    (∫ p, (p.maximum : ℝ) ∂grow ⟨{a}, M⟩ n) =
      ∫ s, ((max M (a + Forward.treeHeight s) : ℕ) : ℝ)
        ∂Forward.treeLaw RRT.allAttach n := by
  rw [single_seed_growth a M ha,
    integral_map measurable_from_top.aemeasurable measurable_from_top.aestronglyMeasurable]
  rfl

theorem expectedHeight_eq_wordLaw (xs : Word) : Word.expectedHeight xs =
    ∫ p, (p.maximum : ℝ) ∂wordLaw xs := by
  rw [Word.expectedHeight, Word.heightLaw, ← map_law_maximum,
    integral_map measurable_from_top.aemeasurable
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).aestronglyMeasurable]
  rfl

end FreezingGrowth.HeightProfile
