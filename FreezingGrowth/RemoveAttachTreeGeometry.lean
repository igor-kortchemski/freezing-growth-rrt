module

public import FreezingGrowth.RemoveAttachTreeMarginals
public import FreezingGrowth.TwoSeedGraftMasterTree

@[expose] public section
namespace FreezingGrowth.RemoveAttachTreeCoupling
open MeasureTheory TwoSeedGraft

theorem sampleLaw_probability (k : ℕ) : IsProbabilityMeasure (sampleLaw k) := by
  have : IsProbabilityMeasure ((sampleLaw k).map Sample.master) := by
    rw [sampleLaw_master]
    infer_instance
  exact (Measure.isProbabilityMeasure_map_iff (μ := sampleLaw k) (f := Sample.master)
    measurable_from_top.aemeasurable).mp inferInstance

theorem sampleLaw_masterPrefix (k : ℕ) :
    (sampleLaw k).map (fun z => masterPrefix k z.master) =
      Forward.treeLaw RRT.allAttach (k + 1) := by
  calc
    _ = ((sampleLaw k).map Sample.master).map (masterPrefix k) :=
      (Measure.map_map measurable_from_top measurable_from_top).symm
    _ = _ := by rw [sampleLaw_master, masterPrefix_law k (k+2) (by omega)]

theorem sampleLaw_ae_master (k : ℕ) : ∀ᵐ z ∂sampleLaw k,
    Forward.ValidAt (k+2) z.master ∧
      RRTSplit.Describes (k+1) z.master (RRTSplit.split (k+1) z.master) := by
  have h : ∀ᵐ r ∂Forward.treeLaw RRT.allAttach (k+2),
      Forward.ValidAt (k+2) r ∧ RRTSplit.Describes (k+1) r (RRTSplit.split (k+1) r) := by
    filter_upwards [Forward.treeLaw_valid RRT.allAttach (k+2),
      RRTSplit.treeLaw_split_describes (k+1)] with r hr hd
    exact ⟨hr, hd⟩
  rw [← sampleLaw_master k] at h
  exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp h

theorem sampleLaw_graphs (k : ℕ) : ∀ᵐ z ∂sampleLaw k,
    (longState k z).graph = z.longInitial.graph ⊔
      ((RRTSplit.split (k+1) z.master).rootSide.mappedGraph.map
        (embedding 3 (birthOrderedFirstSeed z.longInitial) (birthOrderedSecondSeed z.longInitial)) ⊔
      (RRTSplit.split (k+1) z.master).childSide.mappedGraph.map
        (embedding 3 (birthOrderedFirstSeed z.longInitial) (birthOrderedSecondSeed z.longInitial))) ∧
    (shortState k z).graph = z.shortInitial.graph ⊔
      ((RRTSplit.split k (masterPrefix k z.master)).rootSide.mappedGraph.map
        (embedding 3 (birthOrderedFirstSeed z.shortInitial) (birthOrderedSecondSeed z.shortInitial)) ⊔
      (RRTSplit.split k (masterPrefix k z.master)).childSide.mappedGraph.map
        (embedding 3 (birthOrderedFirstSeed z.shortInitial) (birthOrderedSecondSeed z.shortInitial))) := by
  filter_upwards [sampleLaw_ae_master k] with z hz
  constructor
  · exact replay_graph_split _ _ _ _ _ _ hz.1 hz.2
  · rw [masterPrefix_split_eq]
    have hp : ∀ j, 2 ≤ j → j ≤ k+1 → z.master.parent j < j := by
      intro j hj hj'
      apply hz.1.parent_lt j _ (by omega)
      rw [hz.2.vertices]
      exact Finset.mem_range.mpr (by omega)
    rw [shortState, replay_graph, graftEdges_eq_components _ _ _ _ k hp]
    rfl

/-- Old parents, depths, and freezing times are retained in both whole trees. -/
theorem old_data_preserved (k : ℕ) (z : Sample) (a : ℕ) (ha : a ≤ 3) :
    (longState k z).parent a = z.longInitial.parent a ∧
    (longState k z).height a = z.longInitial.height a ∧
    (longState k z).frozenAt a = z.longInitial.frozenAt a ∧
    (shortState k z).parent a = z.shortInitial.parent a ∧
    (shortState k z).height a = z.shortInitial.height a ∧
    (shortState k z).frozenAt a = z.shortInitial.frozenAt a :=
  ⟨replay_parent_old _ _ _ _ _ _ _ ha, replay_height_old _ _ _ _ _ _ _ ha,
    replay_frozenAt_old _ _ _ _ _ _ _ ha, replay_parent_old _ _ _ _ _ _ _ ha,
    replay_height_old _ _ _ _ _ _ _ ha, replay_frozenAt_old _ _ _ _ _ _ _ ha⟩

end FreezingGrowth.RemoveAttachTreeCoupling
