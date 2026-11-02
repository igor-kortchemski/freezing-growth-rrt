module

public import FreezingGrowth.ReverseDelayedTags

/-! An exact projection of the coupled history that retains the entire
shorter history and only the metadata relevant to its future. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

structure ShorterView where
  history : FiniteMarkov.History Forest
  tag : PendingTag

instance : MeasurableSpace ShorterView := ⊤
instance : DiscreteMeasurableSpace ShorterView := ⟨fun _ => trivial⟩

def shorterView (h : FiniteMarkov.History InitializationSample) : ShorterView :=
  ⟨FiniteMarkov.History.map InitializationSample.shorter h, pendingTag h.current⟩

def shorterViewUpdate (h : FiniteMarkov.History Forest) (p : Forest × PendingTag) : ShorterView :=
  ⟨h.push p.1, p.2⟩

theorem measurable_shorterViewUpdate (h : FiniteMarkov.History Forest) :
    Measurable (shorterViewUpdate h) :=
  measurable_from_prod_countable_left (fun _ => measurable_from_top)

noncomputable def shorterHistoryStep (h : FiniteMarkov.History Forest) :
    Measure (FiniteMarkov.History Forest) := (joinLaw h.current).map (fun F => h.push F)

noncomputable def shorterViewStep (N : ℕ) (v : ShorterView) : Measure ShorterView :=
  match v.tag with
  | none => (uniformRootPair (Finset.range N)).map (fun p =>
      ⟨v.history.push (joinPositions v.history.current p), none⟩)
  | some p => (freshPendingLaw N).map (fun q =>
      ⟨v.history.push (joinPositions v.history.current (lowerPair p)), q⟩)

theorem joinPositions_orderedLaw (F : Forest) (hF : 2 ≤ F.forest.roots.card) :
    (uniformRootPair (Finset.range F.forest.roots.card)).map (joinPositions F) = joinLaw F := by
  rw [← ReverseHeightList.map_uniformRootPair_finPairValues F.forest.roots.card,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    joinLaw_eq_list_indices F hF]
  apply Measure.map_congr
  filter_upwards [ReverseHeightList.uniformFinPair_ae_distinct F.forest.roots.card] with p hp
  exact joinPositions_fin F p hp

theorem positivePairLaw_shorterHistoryStep (N : ℕ) (hN : 2 ≤ N)
    (h : FiniteMarkov.History Forest) (hc : h.current.forest.roots.card = N) :
    (positivePairLaw N).map (fun p => h.push (joinPositions h.current (lowerPair p))) =
      shorterHistoryStep h := by
  calc
    _ = ((positivePairLaw N).map lowerPair).map
        (fun p => h.push (joinPositions h.current p)) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = ((uniformRootPair (Finset.range N)).map (joinPositions h.current)).map
        (fun F => h.push F) := by
      rw [positivePairLaw_lowerPair N,
        Measure.map_map measurable_from_top (measurable_of_countable _)]
      rfl
    _ = _ := by
      rw [← hc, joinPositions_orderedLaw h.current (by omega)]
      rfl

theorem initializationLaw_shorterView (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    (initializationLaw F i).map (fun z => shorterView (FiniteMarkov.History.start z)) =
      (freshPendingLaw (F.forest.roots.card + 1)).map
        (fun q => (⟨FiniteMarkov.History.start F, q⟩ : ShorterView)) := by
  rw [← initializationLaw_pendingTag F hi,
    Measure.map_map (measurable_of_countable _) measurable_from_top]
  apply Measure.map_congr
  unfold initializationLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Conditional on the full coupled current history, its projected update
depends only on the entire shorter history and the None/Some pending tag. -/
theorem delayedTransition_shorterView {i N : ℕ}
    (h : FiniteMarkov.History InitializationSample)
    (hz : DelayedValid i N h.current) (hN : 2 ≤ N) :
    (delayedTransition i h.current).map (fun z => shorterView (h.push z)) =
      shorterViewStep N (shorterView h) := by
  cases hu : h.current.used with
  | true =>
    rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN), hu]
    simp only [↓reduceIte, synchronizedLaw,
      Measure.map_map measurable_from_top (measurable_of_countable _)]
    simp only [shorterViewStep, shorterView, pendingTag, hu, ↓reduceIte]
    rw [hz.shorter_card]
    congr 1
  | false =>
    rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN), hu]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have he : (fun z => shorterView (h.push z)) =
        shorterViewUpdate (FiniteMarkov.History.map InitializationSample.shorter h) ∘
          (fun z : InitializationSample => (z.shorter, pendingTag z)) := rfl
    rw [he, ← Measure.map_map (measurable_shorterViewUpdate _) measurable_from_top,
      initializationLaw_shorter_pendingTag (consumeDelayed h.current) hz.consume_fresh,
      Measure.map_map (measurable_shorterViewUpdate _) (measurable_of_countable _)]
    rw [hz.consume_card hu]
    simp only [shorterViewStep, shorterView, pendingTag, hu, Bool.false_eq_true, ↓reduceIte]
    rfl

noncomputable def projectedShorterHistoryLaw (F : Forest) (i t : ℕ) : Measure ShorterView :=
  (delayedHistoryLaw F i t).map shorterView

theorem projectedShorterHistoryLaw_zero (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    projectedShorterHistoryLaw F i 0 =
      (freshPendingLaw (F.forest.roots.card + 1)).map
        (fun q => (⟨FiniteMarkov.History.start F, q⟩ : ShorterView)) := by
  rw [projectedShorterHistoryLaw, delayedHistoryLaw, FiniteMarkov.historyLaw,
    Measure.map_map measurable_from_top measurable_from_top]
  exact initializationLaw_shorterView F hi

theorem projectedShorterHistoryLaw_succ (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (t : ℕ) (ht : t + 1 ≤ F.forest.roots.card - 1) :
    projectedShorterHistoryLaw F i (t + 1) =
      (projectedShorterHistoryLaw F i t).bind (shorterViewStep (F.forest.roots.card - t)) := by
  have hv : ∀ᵐ h ∂delayedHistoryLaw F i t,
      DelayedValid i (F.forest.roots.card - t) h.current := by
    have hh := delayedLawAfter_ae_valid F hi t (by omega)
    rw [← finiteRunLaw_delayed F i t, ← FiniteMarkov.historyLaw_current] at hh
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hh
  unfold projectedShorterHistoryLaw
  rw [delayedHistoryLaw, FiniteMarkov.historyLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.bind_map (m := delayedHistoryLaw F i t) (f := shorterView)
      (g := shorterViewStep (F.forest.roots.card - t))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hv] with h hz
  rw [Measure.map_map measurable_from_top measurable_from_top]
  exact delayedTransition_shorterView h hz (by omega)

end FreezingGrowth.ReverseOrdered
