module

public import FreezingGrowth.TwoSeedGraftInsertedHistory

/-! Exact merged full-word histories for the freeze/attach coupling. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

theorem prefixHistoryLaw_append_two (xs : Word) (b c : Bool) :
    prefixHistoryLaw (xs ++ [b,c]) = (prefixHistoryLaw xs).bind (fun h =>
      (Forward.transitionLaw h.current (xs.length + 1) b).bind (fun q =>
        (Forward.transitionLaw q (xs.length + 2) c).map (fun r => (h.push q).push r))) := by
  rw [prefixHistoryLaw_append]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => by
    dsimp only
    simp only [List.length_cons, List.length_nil, FiniteMarkov.historyLaw,
      Measure.map_dirac' measurable_from_top, Measure.dirac_bind measurable_from_top]
    rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl))

theorem oldHistoryPairLaw_freezeAttachHistory (xs : Word)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (oldHistoryPairLaw xs).map
        (fun o => freezeAttachHistory o.history xs.length o.first o.second) =
      prefixHistoryLaw (xs ++ [false,true]) := by
  have hh : ∀ᵐ h ∂prefixHistoryLaw xs, h.current.active.card = 2 := by
    rw [← prefixHistoryLaw_current xs] at hc
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hc
  rw [oldHistoryPairLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, prefixHistoryLaw_append_two]
  apply Measure.bind_congr_right
  filter_upwards [hh] with h hh
  rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
  exact orderedPair_freezeAttachHistory h xs.length hh

/-- The complete longer path, including its two inserted transitions, has
exactly Algorithm 1's full original-word history law. -/
theorem historySampleLaw_longHistory (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (historySampleLaw xs n).map (HistorySample.longHistory xs.length n) =
      prefixHistoryLaw ((xs ++ [false,true]) ++ List.replicate n true) := by
  have hh := oldHistoryPairLaw_ae_parameters xs hc
  rw [historySampleLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, prefixHistoryLaw_attachSuffix,
    ← oldHistoryPairLaw_freezeAttachHistory xs hc,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hh] with o ho
  have hu : o.first ≤ xs.length := ho.1.vertices_le _ (ho.1.active_subset (by rw [ho.2.1]; simp))
  have hq : (Forward.attach (Forward.freeze o.history.current (xs.length + 1) o.second)
      (xs.length + 2) o.first).active = {xs.length + 2,o.first} := by
    change insert (xs.length + 2) (o.history.current.active.erase o.second) = _
    rw [ho.2.1]
    ext a
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    aesop
  have hsuffix := masterTree_replayHistory_law
    (Forward.attach (Forward.freeze o.history.current (xs.length + 1) o.second)
      (xs.length + 2) o.first) le_rfl (by omega) (by omega) hq n
  have hm := congrArg (fun μ => μ.map
    (FiniteMarkov.History.merge (freezeAttachHistory o.history xs.length o.first o.second))) hsuffix
  rw [Measure.map_map measurable_from_top measurable_from_top] at hm
  rw [Measure.map_map measurable_from_top measurable_from_top]
  simpa [HistorySample.longHistory, HistorySample.longPrefixHistory,
    HistorySample.base, longPrefixState, freezeAttachHistory, Function.comp_def,
    FiniteMarkov.History.push,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hm

end FreezingGrowth.TwoSeedGraft
