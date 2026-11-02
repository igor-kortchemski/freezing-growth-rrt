module

public import FreezingGrowth.TwoSeedGraftIndependence

/-! The shared master realizes both entire original-word trajectories,
including the literal common past and the two inserted intermediate states. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

/-- Concatenation of genuine forward histories, retaining every old State. -/
theorem prefixHistoryLaw_append (xs ys : Word) :
    prefixHistoryLaw (xs ++ ys) = (prefixHistoryLaw xs).bind (fun h =>
      (FiniteMarkov.historyLaw (Measure.dirac h.current)
        (fun j s => Forward.transitionLaw s (xs.length + j + 1) (ys.toSigns (j + 1)))
          ys.length).map (FiniteMarkov.History.merge h)) := by
  unfold prefixHistoryLaw
  rw [List.length_append, FiniteMarkov.historyLaw_add]
  have hp : FiniteMarkov.historyLaw (Measure.dirac Forward.initial)
      (fun j s => Forward.transitionLaw s (j + 1) ((xs ++ ys).toSigns (j + 1))) xs.length =
      FiniteMarkov.historyLaw (Measure.dirac Forward.initial)
        (fun j s => Forward.transitionLaw s (j + 1) (xs.toSigns (j + 1))) xs.length := by
    apply FiniteMarkov.historyLaw_congr
    intro j hj s
    rw [Word.toSigns_append_left xs ys hj]
  rw [hp]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => by
    dsimp only
    congr 1
    apply FiniteMarkov.historyLaw_congr
    intro j hj s
    rw [Word.toSigns_append_right])

theorem prefixHistoryLaw_attachSuffix (xs : Word) (n : ℕ) :
    prefixHistoryLaw (xs ++ List.replicate n true) =
      (prefixHistoryLaw xs).bind (fun h =>
        (FiniteMarkov.historyLaw (Measure.dirac h.current)
          (fun j s => Forward.transitionLaw s (xs.length + j + 1) true) n).map
            (FiniteMarkov.History.merge h)) := by
  rw [prefixHistoryLaw_append, List.length_replicate]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => by
    dsimp only
    congr 1
    apply FiniteMarkov.historyLaw_congr
    intro j hj s
    simp only [Word.toSigns_succ, List.getElem?_replicate_of_lt hj, Option.getD_some])

/-- The exact conditional suffix history for a random ordered active pair. -/
theorem orderedPair_master_history (s : Forward.State) {T : ℕ}
    (hs : Forward.ValidAt T s) (hc : s.active.card = 2) (n : ℕ) :
    (uniformRootPair s.active).bind (fun p =>
      (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => replayHistory s T p.1 p.2 r.parent n)) =
      FiniteMarkov.historyLaw (Measure.dirac s)
        (fun j q => Forward.transitionLaw q (T + j + 1) true) n := by
  let := uniformRootPair_isProbabilityMeasure s.active (by omega)
  calc
    _ = (uniformRootPair s.active).bind (fun _ =>
        FiniteMarkov.historyLaw (Measure.dirac s)
          (fun j q => Forward.transitionLaw q (T + j + 1) true) n) := by
      apply Measure.bind_congr_right
      filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      exact masterTree_replayHistory_law s (hs.vertices_le _ (hs.active_subset ha))
        (hs.vertices_le _ (hs.active_subset hb)) hab (active_eq_pair_of_card_two hc hp) n
    _ = _ := by rw [Measure.bind_const, measure_univ, one_smul]

theorem historySampleLaw_baselineHistory (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (historySampleLaw xs n).map (HistorySample.baselineHistory xs.length n) =
      prefixHistoryLaw (xs ++ List.replicate n true) := by
  have hh : ∀ᵐ h ∂prefixHistoryLaw xs,
      Forward.ValidAt xs.length h.current ∧ h.current.active.card = 2 := by
    have hv := (Forward.treeLaw_valid xs.toSigns xs.length).and hc
    rw [← prefixHistoryLaw_current xs] at hv
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hv
  rw [historySampleLaw, oldHistoryPairLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    prefixHistoryLaw_attachSuffix]
  apply Measure.bind_congr_right
  filter_upwards [hh] with h hh
  rw [Measure.bind_map (measurable_of_countable _).aemeasurable
      measurable_from_top.aemeasurable,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    ← orderedPair_master_history h.current hh.1 hh.2 n,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    simp only [Measure.map_map measurable_from_top measurable_from_top]
    rfl)

end FreezingGrowth.TwoSeedGraft
