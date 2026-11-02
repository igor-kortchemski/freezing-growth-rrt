module

public import FreezingGrowth.RemoveAttachTreeGeometry
public import FreezingGrowth.RemoveAttachTreeIndependence

/-! Source III1, with `n = k + 1`. Independent prefix trees are a permissible
choice of their otherwise unspecified joint law. Both grafts use one master
parent array; `masterPrefix` is the smaller actual recursive tree on that array.
The full graph identities are `sampleLaw_graphs`; old frozen data are retained
by `old_data_preserved`, and every new parent is identified below. -/

@[expose] public section
namespace FreezingGrowth.RemoveAttachTreeCoupling
open MeasureTheory TwoSeedGraft

theorem sampleLaw_ae_prefix_components (k : ℕ) : ∀ᵐ z ∂sampleLaw k,
    RRTSplit.Describes k (masterPrefix k z.master) (RRTSplit.split k z.master) := by
  have h := RRTSplit.treeLaw_split_describes k
  rw [← sampleLaw_masterPrefix k] at h
  have h' := (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp h
  filter_upwards [h'] with z hz
  rwa [masterPrefix_split_eq] at hz

theorem new_data_preserved_long (k : ℕ) (z : Sample) (j : ℕ) (hj : j < k+1) :
    (longState k z).parent (3+j+1) =
      embedding 3 (birthOrderedFirstSeed z.longInitial) (birthOrderedSecondSeed z.longInitial)
        (z.master.parent (j+2)) ∧
    (longState k z).frozenAt (3+j+1) = none :=
  ⟨replay_parent_new _ _ _ _ _ _ _ hj, replay_frozenAt_new _ _ _ _ _ _ _ hj⟩

theorem new_data_preserved_short (k : ℕ) (z : Sample) (j : ℕ) (hj : j < k) :
    (shortState k z).parent (3+j+1) =
      embedding 3 (birthOrderedFirstSeed z.shortInitial) (birthOrderedSecondSeed z.shortInitial)
        (z.master.parent (j+2)) ∧
    (shortState k z).frozenAt (3+j+1) = none :=
  ⟨replay_parent_new _ _ _ _ _ _ _ hj, replay_frozenAt_new _ _ _ _ _ _ _ hj⟩

/-- One probability space realizes both exact word laws and the nested master
sizes. Component assignment, seed order and complete graph identities are
proved on this very same space in the imported geometry/independence modules. -/
theorem source_full_tree_coupling (k : ℕ) :
    IsProbabilityMeasure (sampleLaw k) ∧
    (sampleLaw k).map (longState k) =
      Forward.treeLaw (longPrefix ++ List.replicate (k+1) true).toSigns
        (longPrefix ++ List.replicate (k+1) true).length ∧
    (sampleLaw k).map (shortState k) =
      Forward.treeLaw (Word.toSigns ([true,false] ++ List.replicate (k+1) true))
        ([true,false] ++ List.replicate (k+1) true).length ∧
    (sampleLaw k).map Sample.master = Forward.treeLaw RRT.allAttach (k+2) ∧
    (sampleLaw k).map (fun z => masterPrefix k z.master) =
      Forward.treeLaw RRT.allAttach (k+1) :=
  ⟨sampleLaw_probability k, sampleLaw_long k, sampleLaw_short k,
    sampleLaw_master k, sampleLaw_masterPrefix k⟩

end FreezingGrowth.RemoveAttachTreeCoupling
