module

public import FreezingGrowth.RemoveAttachTreeCoupling

@[expose] public section
namespace FreezingGrowth.RemoveAttachTreeCoupling
open MeasureTheory TwoSeedGraft

theorem long_seed_spec : ∀ᵐ s ∂Forward.treeLaw longPrefix.toSigns longPrefix.length,
    s.active = {birthOrderedFirstSeed s, birthOrderedSecondSeed s} ∧
      birthOrderedFirstSeed s ≠ birthOrderedSecondSeed s := by
  filter_upwards [attachAttachFreeze_active_card] with s hs
  exact ⟨(birthOrderedSeed_spec s hs).1, (birthOrderedSeed_spec s hs).2.ne⟩

theorem short_seed_spec : ∀ᵐ s ∂Forward.treeLaw shortPrefix.toSigns shortPrefix.length,
    s.active = {birthOrderedFirstSeed s, birthOrderedSecondSeed s} ∧
      birthOrderedFirstSeed s ≠ birthOrderedSecondSeed s := by
  filter_upwards [attachFreezeAttach_active_card] with s hs
  exact ⟨(birthOrderedSeed_spec s hs).1, (birthOrderedSeed_spec s hs).2.ne⟩

theorem sampleLaw_long (k : ℕ) :
    (sampleLaw k).map (longState k) =
      Forward.treeLaw (longPrefix ++ List.replicate (k + 1) true).toSigns
        (longPrefix ++ List.replicate (k + 1) true).length := by
  rw [word_two_seed_master_law longPrefix (k + 1)
    birthOrderedFirstSeed birthOrderedSecondSeed long_seed_spec,
    sampleLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have h : ∀ t : Forward.State,
        ((Forward.treeLaw RRT.allAttach (k + 2)).map (fun r => (⟨s,t,r⟩ : Sample))).map
          (longState k) = (Forward.treeLaw RRT.allAttach (k + 2)).map
            (fun r => replay s 3 (birthOrderedFirstSeed s) (birthOrderedSecondSeed s)
              r.parent (k + 1)) := fun t => by
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl
    simp_rw [h]
    rw [Measure.bind_const, measure_univ, one_smul]
    rfl)

theorem sampleLaw_short_prefix (k : ℕ) :
    (sampleLaw k).map (shortState k) =
      Forward.treeLaw (shortPrefix ++ List.replicate k true).toSigns
        (shortPrefix ++ List.replicate k true).length := by
  rw [word_two_seed_master_law_of_le shortPrefix k (k + 2)
    birthOrderedFirstSeed birthOrderedSecondSeed short_seed_spec (by omega),
    sampleLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  have h : ∀ s : Forward.State,
      ((Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
        (Forward.treeLaw RRT.allAttach (k + 2)).map (fun r => (⟨s,t,r⟩ : Sample)))).map
          (shortState k) =
      (Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
        (Forward.treeLaw RRT.allAttach (k + 2)).map (fun r =>
          replay t 3 (birthOrderedFirstSeed t) (birthOrderedSecondSeed t) r.parent k)) := by
    intro s
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl)
  simp_rw [h]
  rw [Measure.bind_const, measure_univ, one_smul]
  rfl

theorem short_word_eq (k : ℕ) :
    shortPrefix ++ List.replicate k true = [true,false] ++ List.replicate (k + 1) true := by
  simp [shortPrefix, List.replicate_succ]

theorem sampleLaw_short (k : ℕ) :
    (sampleLaw k).map (shortState k) =
      Forward.treeLaw (Word.toSigns ([true,false] ++ List.replicate (k+1) true))
        ([true,false] ++ List.replicate (k+1) true).length := by
  rw [sampleLaw_short_prefix, short_word_eq]

theorem sampleLaw_master (k : ℕ) :
    (sampleLaw k).map Sample.master = Forward.treeLaw RRT.allAttach (k + 2) := by
  rw [sampleLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  have h : ∀ s : Forward.State,
      ((Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
        (Forward.treeLaw RRT.allAttach (k + 2)).map (fun r => (⟨s,t,r⟩ : Sample)))).map
          Sample.master = Forward.treeLaw RRT.allAttach (k + 2) := by
    intro s
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have hm : ∀ t : Forward.State,
        ((Forward.treeLaw RRT.allAttach (k + 2)).map (fun r => (⟨s,t,r⟩ : Sample))).map
          Sample.master = Forward.treeLaw RRT.allAttach (k + 2) := by
      intro t
      rw [Measure.map_map measurable_from_top measurable_from_top]
      exact Measure.map_id
    simp_rw [hm]
    rw [Measure.bind_const, measure_univ, one_smul]
  simp_rw [h]
  rw [Measure.bind_const, measure_univ, one_smul]

end FreezingGrowth.RemoveAttachTreeCoupling
