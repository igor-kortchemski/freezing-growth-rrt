module

public import FreezingGrowth.TwoSeedGraftLongHistory

/-! Source I2: both complete original-word processes on one shared original
history, with joint old-data/master independence and complete graft geometry. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

/-- Remove the most recent transitions while retaining all earlier States. -/
def dropRecent : ℕ → FiniteMarkov.History Forward.State → FiniteMarkov.History Forward.State
  | 0, h => h
  | n + 1, ⟨_, a :: past⟩ => dropRecent n ⟨a,past⟩
  | _ + 1, ⟨a, []⟩ => ⟨a,[]⟩

theorem dropRecent_push (n : ℕ) (h : FiniteMarkov.History Forward.State) (a : Forward.State) :
    dropRecent (n + 1) (h.push a) = dropRecent n h := by
  cases h
  rfl

/-- Removing exactly the replayed suffix returns the literal shared prefix. -/
theorem replayHistory_commonPrefix (h : FiniteMarkov.History Forward.State)
    (T u v : ℕ) (p : ℕ → ℕ) (n : ℕ) :
    dropRecent n (FiniteMarkov.History.merge h (replayHistory h.current T u v p n)) = h := by
  induction n with
  | zero => cases h; rfl
  | succ n ih =>
    change dropRecent (n + 1)
      ((FiniteMarkov.History.merge h (replayHistory h.current T u v p n)).push
        (replay h.current T u v p (n + 1))) = h
    rw [dropRecent_push, ih]

theorem historySample_entire_common_prefix (T n : ℕ) (z : HistorySample) :
    dropRecent n (z.baselineHistory T n) = z.old.history ∧
      dropRecent 2 (dropRecent n (z.longHistory T n)) = z.old.history := by
  constructor
  · exact replayHistory_commonPrefix z.old.history T z.old.first z.old.second z.master.parent n
  · have h := replayHistory_commonPrefix (z.longPrefixHistory T)
      (T + 2) (T + 2) z.old.first z.master.parent n
    change dropRecent 2 (dropRecent n
      (FiniteMarkov.History.merge (z.longPrefixHistory T)
        (replayHistory (z.longPrefixHistory T).current (T + 2) (T + 2)
          z.old.first z.master.parent n))) = _
    rw [h]
    rfl

theorem historySampleLaw_probability (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    IsProbabilityMeasure (historySampleLaw xs n) := by
  have : IsProbabilityMeasure ((historySampleLaw xs n).map HistorySample.base) := by
    rw [historySampleLaw_base]
    exact sampleLaw_probability xs n (hc.mono (fun _ h => by omega))
  exact (Measure.isProbabilityMeasure_map_iff (f := HistorySample.base)
    measurable_from_top.aemeasurable).mp this

theorem historySampleLaw_ae_parameters (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ z ∂historySampleLaw xs n, Parameters xs.length n z.base := by
  have hp := sampleLaw_ae_parameters xs n hc
  rw [← historySampleLaw_base xs n] at hp
  exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hp

/-- Both entire source-word processes, including all frozen data and the
literal original common prefix, are realized on this one probability space. -/
theorem source_freezeAttach_history_coupling (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IsProbabilityMeasure (historySampleLaw (twoActivePrefix m) n) ∧
      (historySampleLaw (twoActivePrefix m) n).map
          (HistorySample.baselineHistory (twoActivePrefix m).length n) =
        prefixHistoryLaw (twoActivePrefix m ++ List.replicate n true) ∧
      (historySampleLaw (twoActivePrefix m) n).map
          (HistorySample.longHistory (twoActivePrefix m).length n) =
        prefixHistoryLaw ((twoActivePrefix m ++ [false,true]) ++ List.replicate n true) := by
  have hc := twoActivePrefix_active_card m hm
  exact ⟨historySampleLaw_probability _ n hc, historySampleLaw_baselineHistory _ n hc,
    historySampleLaw_longHistory _ n hc⟩

/-- Full source old-tree/pair law times the uniform-size conditional product
of genuine complete recursive-tree components. -/
theorem source_history_treePair_split (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (historySampleLaw (twoActivePrefix m) n).map
        (fun z => (z.old.treePair, RRTSplit.firstEdgeSplit n z.master)) =
      ((Forward.treeLaw RRT.allAttach m).bind (fun s =>
        (uniformRootPair s.vertices).map (Forward.treePairSample s))).prod
        ((Measure.uniformOfFinset (Finset.range (n + 1))).bind (fun k =>
          ((Forward.treeLaw RRT.allAttach k).prod
            (Forward.treeLaw RRT.allAttach (n - k))).map (fun p => (k,p.1,p.2)))) := by
  rw [historySampleLaw_treePair_split, twoActivePrefix_treePairLaw_eq_bind_vertices m hm]
  rfl

/-- Both complete graft graphs use the same original tree and actual master
split. The first master component is on the new child in the longer word. -/
theorem source_history_both_graft_graphs (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ∀ᵐ z ∂historySampleLaw (twoActivePrefix m) n,
      let T := (twoActivePrefix m).length
      let P := RRTSplit.split n z.master
      (baselineState T n z.base).graph = z.old.history.current.graph ⊔
        (P.rootSide.mappedGraph.map (embedding T z.old.first z.old.second) ⊔
          P.childSide.mappedGraph.map (embedding T z.old.first z.old.second)) ∧
      (longState T n z.base).graph = z.old.history.current.graph ⊔
        (SimpleGraph.edge z.old.first (T + 2) ⊔
          (P.rootSide.mappedGraph.map (embedding (T + 2) (T + 2) z.old.first) ⊔
            P.childSide.mappedGraph.map (embedding (T + 2) (T + 2) z.old.first))) := by
  filter_upwards [historySampleLaw_ae_parameters _ n (twoActivePrefix_active_card m hm)] with z hz
  dsimp only
  constructor
  · exact replay_graph_split _ _ _ _ _ _ hz.2.2.2.1 hz.2.2.2.2
  · have h := replay_graph_split (longPrefixState (twoActivePrefix m).length z.base)
      z.master ((twoActivePrefix m).length + 2) ((twoActivePrefix m).length + 2)
        z.old.first n hz.2.2.2.1 hz.2.2.2.2
    simpa only [longState, longPrefixState, Forward.attach, Forward.freeze,
      HistorySample.base, sup_assoc] using h

end FreezingGrowth.TwoSeedGraft
