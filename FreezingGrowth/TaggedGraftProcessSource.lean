module

public import FreezingGrowth.TaggedGraftLongHistory
public import FreezingGrowth.TwoSeedGraftSource

/-! Source II1 with complete common-prefix histories and every inserted State. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

theorem taggedHistory_entire_common_prefix (T n : ℕ) (z : TaggedHistorySample) :
    dropRecent n (z.base.baselineHistory T n) = z.base.old.history ∧
      dropRecent 2 (dropRecent n (z.longHistory T n)) = z.base.old.history := by
  constructor
  · exact (historySample_entire_common_prefix T n z.base).1
  · have h := replayHistory_commonPrefix (z.longPrefixHistory T) (T + 2)
      (caseSeeds T z.base.old.first z.base.old.second z.tag).1
      (caseSeeds T z.base.old.first z.base.old.second z.tag).2 z.base.master.parent n
    change dropRecent 2 (dropRecent n
      (FiniteMarkov.History.merge (z.longPrefixHistory T)
        (replayHistory (z.longPrefixHistory T).current (T + 2)
          (caseSeeds T z.base.old.first z.base.old.second z.tag).1
          (caseSeeds T z.base.old.first z.base.old.second z.tag).2 z.base.master.parent n))) = _
    rw [h]
    rfl

theorem taggedHistoryLaw_probability (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    IsProbabilityMeasure (taggedHistoryLaw xs n) := by
  have : IsProbabilityMeasure ((taggedHistoryLaw xs n).map TaggedHistorySample.toTaggedSample) := by
    rw [taggedHistoryLaw_toTaggedSample]
    exact (tagged_full_state_coupling xs n hc).1
  exact (Measure.isProbabilityMeasure_map_iff (f := TaggedHistorySample.toTaggedSample)
    measurable_from_top.aemeasurable).mp this

/-- Both complete Algorithm 1 histories have their exact word laws on this
single space. The original prefix is literally the same on every sample. -/
theorem source_attachFreeze_history_coupling (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IsProbabilityMeasure (taggedHistoryLaw (twoActivePrefix m) n) ∧
      (taggedHistoryLaw (twoActivePrefix m) n).map
          (fun z => z.base.baselineHistory (twoActivePrefix m).length n) =
        prefixHistoryLaw (twoActivePrefix m ++ List.replicate n true) ∧
      (taggedHistoryLaw (twoActivePrefix m) n).map
          (TaggedHistorySample.longHistory (twoActivePrefix m).length n) =
        prefixHistoryLaw ((twoActivePrefix m ++ [true,false]) ++ List.replicate n true) := by
  have hc := twoActivePrefix_active_card m hm
  exact ⟨taggedHistoryLaw_probability _ n hc, taggedHistoryLaw_baselineHistory _ n hc,
    taggedHistoryLaw_longHistory _ n hc⟩

/-- Independence holds against the entire original trajectory, ordered pair,
and actual shared master jointly. -/
theorem source_attachFreeze_history_tag_independence (m n : ℕ) :
    (taggedHistoryLaw (twoActivePrefix m) n).map (fun z => (z.base,z.tag)) =
      (historySampleLaw (twoActivePrefix m) n).prod TwoSeedCoupling.threeCaseLaw :=
  taggedHistoryLaw_joint _ _

theorem source_attachFreeze_history_treePair_split (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (taggedHistoryLaw (twoActivePrefix m) n).map
        (fun z => (z.base.old.treePair, RRTSplit.firstEdgeSplit n z.base.master)) =
      ((Forward.treeLaw RRT.allAttach m).bind (fun s =>
        (uniformRootPair s.vertices).map (Forward.treePairSample s))).prod
        ((Measure.uniformOfFinset (Finset.range (n + 1))).bind (fun k =>
          ((Forward.treeLaw RRT.allAttach k).prod
            (Forward.treeLaw RRT.allAttach (n - k))).map (fun p => (k,p.1,p.2)))) := by
  rw [← source_history_treePair_split m hm n, ← taggedHistoryLaw_base,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

/-- All three source cases use the same original complete graph and the same
actual master split, including the child that is frozen in case zero. -/
theorem source_attachFreeze_history_all_case_graphs (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∀ᵐ z ∂taggedHistoryLaw (twoActivePrefix m) n, ∀ c : Fin 3,
      let T := (twoActivePrefix m).length
      let b := z.base.base
      (caseState T n c b).graph =
        (b.initial.graph ⊔ SimpleGraph.edge b.first (T + 1)) ⊔
          ((RRTSplit.split n b.master).rootSide.mappedGraph.map
              (embedding (T + 2) (caseSeeds T b.first b.second c).1 (caseSeeds T b.first b.second c).2) ⊔
            (RRTSplit.split n b.master).childSide.mappedGraph.map
              (embedding (T + 2) (caseSeeds T b.first b.second c).1 (caseSeeds T b.first b.second c).2)) := by
  have hp := taggedSampleLaw_all_case_graphs (twoActivePrefix m) n
    (twoActivePrefix_active_card m hm)
  rw [← taggedHistoryLaw_toTaggedSample] at hp
  exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hp

end FreezingGrowth.TwoSeedGraft
