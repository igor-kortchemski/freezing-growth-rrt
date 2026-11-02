module

public import FreezingGrowth.ReverseSourceShorterHistory

/-! The corrected source-history independence statement includes the entire
common tail, not just the comparison history after initialization. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

noncomputable def sourceShorterHistoryLawAt (k : ℕ) (tail : Word) (t : ℕ) :
    Measure (FiniteMarkov.History Forest) :=
  (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
    tail.length).bind (fun h => (delayedHistoryLaw h.current k t).map
      (extendSourceShorterHistory k tail h))

noncomputable def sourceShorterTaggedHistoryLaw (k : ℕ) (tail : Word) (t : ℕ) :
    Measure (FiniteMarkov.History Forest × PendingTag) :=
  (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
    tail.length).bind (fun h => (delayedHistoryLaw h.current k t).map
      (fun g => (extendSourceShorterHistory k tail h g, pendingTag g.current)))

def extendShorterOnly (k : ℕ) (tail : Word) (h g : FiniteMarkov.History Forest) :
    FiniteMarkov.History Forest :=
  FiniteMarkov.History.map
    (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length))
    (g.appendPast h.past)

private theorem bind_prod_const {α β γ : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (K : α → Measure β) (η : Measure γ) [SFinite η] :
    (μ.bind K).prod η = μ.bind (fun a => (K a).prod η) := by
  rw [Measure.prod_eq_of_sfinite,
    Measure.bind_bind Measurable.of_discrete.aemeasurable
      Measurable.map_prodMk_left.aemeasurable]
  congr 1
  funext a
  rw [Measure.prod_eq_of_sfinite]

theorem sourceShorterTaggedHistoryLaw_product (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) (t : ℕ) (ht : t ≤ k - 1) :
    sourceShorterTaggedHistoryLaw k tail t =
      (sourceShorterHistoryLawAt k tail t).prod (delayedMetadataLaw k t) := by
  let := delayedMetadataLaw_probability k hk t ht
  rw [sourceShorterHistoryLawAt, bind_prod_const]
  unfold sourceShorterTaggedHistoryLaw
  apply Measure.bind_congr_right
  filter_upwards [sourceTailHistory_parameters k tail ha] with h hF
  have hjoint := delayedHistoryLaw_shorter_pendingTag h.current hF.1 (by omega) t
    (by simpa only [hF.2] using ht)
  rw [hF.2] at hjoint
  have hshort := delayedHistoryLaw_shorter h.current hF.1 (by omega) t
    (by simpa only [hF.2] using ht)
  have hm : Measurable (Prod.map (extendShorterOnly k tail h) (id : PendingTag → PendingTag)) :=
    measurable_from_top.prodMap measurable_id
  calc
    _ = ((delayedHistoryLaw h.current k t).map (fun g =>
        (FiniteMarkov.History.map InitializationSample.shorter g, pendingTag g.current))).map
        (Prod.map (extendShorterOnly k tail h) id) := by
      rw [Measure.map_map hm measurable_from_top]
      rfl
    _ = ((shorterCoalescentHistoryLaw h.current t).prod (delayedMetadataLaw k t)).map
        (Prod.map (extendShorterOnly k tail h) id) := by rw [hjoint]
    _ = ((shorterCoalescentHistoryLaw h.current t).map (extendShorterOnly k tail h)).prod
        (delayedMetadataLaw k t) := by
      rw [← Measure.map_prod_map _ _ measurable_from_top measurable_id, Measure.map_id]
    _ = _ := by
      rw [← hshort, Measure.map_map measurable_from_top measurable_from_top]
      rfl

theorem sourceShorterHistoryLawAt_eq (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) (t : ℕ) (ht : t ≤ k - 1) :
    sourceShorterHistoryLawAt k tail t =
      orderedHistoryLaw (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
        (tail.length + t) := by
  let e := deletionLabelEquiv (reverseDeletedWord k tail).length
  let x := (reverseDeletedWord k tail).toSigns
  let n := (reverseDeletedWord k tail).length
  have hsplit : orderedHistoryLaw x n (tail.length + t) =
      (orderedHistoryLaw x n tail.length).bind (fun h =>
        (shorterCoalescentHistoryLaw h.current t).map (FiniteMarkov.History.merge h)) := by
    change FiniteMarkov.historyLaw (Measure.dirac (initial x n)) (orderedStepAfter x n)
      (tail.length + t) = _
    rw [FiniteMarkov.historyLaw_add]
    congr 1
    funext h
    congr 1
    apply FiniteMarkov.historyLaw_congr
    intro j hj F
    exact orderedStepAfter_deleted_join k tail (by omega) F
  rw [hsplit, ← orderedHistoryLaw_deletion_tail k hk tail,
    Measure.bind_map
      (m := orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length tail.length)
      (f := FiniteMarkov.History.map (fun F => relabel F e))
      (g := fun h : FiniteMarkov.History Forest =>
        (shorterCoalescentHistoryLaw h.current t).map (FiniteMarkov.History.merge h))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  unfold sourceShorterHistoryLawAt
  apply Measure.bind_congr_right
  filter_upwards [sourceTailHistory_parameters k tail ha] with h hF
  have hshort := delayedHistoryLaw_shorter h.current hF.1 (by omega) t
    (by simpa only [hF.2] using ht)
  have hrel := shorterCoalescentHistoryLaw_relabel h.current e t
  change (delayedHistoryLaw h.current k t).map (extendSourceShorterHistory k tail h) =
    (shorterCoalescentHistoryLaw (relabel h.current e) t).map
      (FiniteMarkov.History.merge (FiniteMarkov.History.map (fun F => relabel F e) h))
  rw [← hrel, ← hshort,
    Measure.map_map measurable_from_top measurable_from_top,
    Measure.map_map measurable_from_top measurable_from_top]
  congr 1
  funext g
  cases h
  cases g
  simp [extendSourceShorterHistory, FiniteMarkov.History.map, FiniteMarkov.History.merge,
    FiniteMarkov.History.appendPast, Function.comp_def, e, List.map_append]

/-- Source C5's corrected independence from the whole comparison-process
past, including the actual common tail. No independence from the full joint
Algorithm 3 history is asserted. -/
theorem sourceShorterTaggedHistoryLaw_eq (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) (t : ℕ) (ht : t ≤ k - 1) :
    sourceShorterTaggedHistoryLaw k tail t =
      (orderedHistoryLaw (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
        (tail.length + t)).prod (delayedMetadataLaw k t) := by
  rw [sourceShorterTaggedHistoryLaw_product k hk tail ha t ht,
    sourceShorterHistoryLawAt_eq k hk tail ha t ht]

end FreezingGrowth.ReverseOrdered
