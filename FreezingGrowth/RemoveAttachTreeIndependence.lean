module
public import FreezingGrowth.RemoveAttachTreeMarginals

@[expose] public section
namespace FreezingGrowth.RemoveAttachTreeCoupling
open MeasureTheory TwoSeedGraft

theorem sampleLaw_longInitial_master (k : ℕ) :
    (sampleLaw k).map (fun z => (z.longInitial,z.master)) =
      (Forward.treeLaw longPrefix.toSigns longPrefix.length).prod
        (Forward.treeLaw RRT.allAttach (k+2)) := by
  rw [sampleLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, Measure.prod_eq_of_sfinite]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun s => by
    dsimp only
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    have h : ∀ t : Forward.State,
        ((Forward.treeLaw RRT.allAttach (k+2)).map (fun r => (⟨s,t,r⟩ : Sample))).map
          (fun z => (z.longInitial,z.master)) =
          (Forward.treeLaw RRT.allAttach (k+2)).map (fun r => (s,r)) := by
      intro t
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl
    simp_rw [h]
    rw [Measure.bind_const, measure_univ, one_smul])

theorem sampleLaw_shortInitial_master (k : ℕ) :
    (sampleLaw k).map (fun z => (z.shortInitial,z.master)) =
      (Forward.treeLaw shortPrefix.toSigns shortPrefix.length).prod
        (Forward.treeLaw RRT.allAttach (k+2)) := by
  rw [sampleLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, Measure.prod_eq_of_sfinite]
  have h : ∀ s : Forward.State,
      ((Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
        (Forward.treeLaw RRT.allAttach (k+2)).map (fun r => (⟨s,t,r⟩ : Sample)))).map
          (fun z => (z.shortInitial,z.master)) =
      (Forward.treeLaw shortPrefix.toSigns shortPrefix.length).bind (fun t =>
        (Forward.treeLaw RRT.allAttach (k+2)).map (fun r => (t,r))) := by
    intro s
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl)
  simp_rw [h]
  rw [Measure.bind_const, measure_univ, one_smul]

theorem sampleLaw_longInitial (k : ℕ) :
    (sampleLaw k).map Sample.longInitial = Forward.treeLaw longPrefix.toSigns longPrefix.length := by
  have h := congrArg (fun μ => μ.map Prod.fst) (sampleLaw_longInitial_master k)
  rw [Measure.map_map measurable_fst measurable_from_top, Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

theorem sampleLaw_shortInitial (k : ℕ) :
    (sampleLaw k).map Sample.shortInitial = Forward.treeLaw shortPrefix.toSigns shortPrefix.length := by
  have h := congrArg (fun μ => μ.map Prod.fst) (sampleLaw_shortInitial_master k)
  rw [Measure.map_map measurable_fst measurable_from_top, Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

theorem sampleLaw_orderedSeeds (k : ℕ) : ∀ᵐ z ∂sampleLaw k,
    (z.longInitial.active = {birthOrderedFirstSeed z.longInitial,birthOrderedSecondSeed z.longInitial} ∧
      birthOrderedFirstSeed z.longInitial < birthOrderedSecondSeed z.longInitial) ∧
    (z.shortInitial.active = {birthOrderedFirstSeed z.shortInitial,birthOrderedSecondSeed z.shortInitial} ∧
      birthOrderedFirstSeed z.shortInitial < birthOrderedSecondSeed z.shortInitial) := by
  have hl : ∀ᵐ s ∂Forward.treeLaw longPrefix.toSigns longPrefix.length, s.active.card = 2 :=
    attachAttachFreeze_active_card
  have hs : ∀ᵐ s ∂Forward.treeLaw shortPrefix.toSigns shortPrefix.length, s.active.card = 2 :=
    attachFreezeAttach_active_card
  rw [← sampleLaw_longInitial k] at hl
  rw [← sampleLaw_shortInitial k] at hs
  have hl' := (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hl
  have hs' := (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hs
  filter_upwards [hl',hs'] with z hz hz'
  exact ⟨birthOrderedSeed_spec _ hz,birthOrderedSeed_spec _ hz'⟩

end FreezingGrowth.RemoveAttachTreeCoupling
