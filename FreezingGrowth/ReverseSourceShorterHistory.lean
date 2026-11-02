module

public import FreezingGrowth.ReverseDeletionTail
public import FreezingGrowth.ReverseDelayedDomination

/-! The entire second process of Algorithm 3 has the shortened word's
ordinary ordered-history law after the explicit bookkeeping-label transport. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

theorem reverseDeletedWord_attach (k : ℕ) (tail : Word) {j : ℕ} (hj : j < k - 1) :
    (reverseDeletedWord k tail).toSigns (j + 1) = true := by
  rw [reverseDeletedWord,
    Word.toSigns_append_left (List.replicate (k - 1) true) tail (by simpa using hj)]
  simp [Word.toSigns_succ, List.getElem?_replicate_of_lt hj]

theorem orderedStepAfter_deleted_join (k : ℕ) (tail : Word) {j : ℕ} (hj : j < k - 1)
    (F : Forest) :
    orderedStepAfter (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
      (tail.length + j) F = joinLaw F := by
  have hlt : tail.length + j < (reverseDeletedWord k tail).length := by
    rw [reverseDeletedWord_length]
    omega
  have hi : (reverseDeletedWord k tail).length - (tail.length + j + 1) =
      k - 1 - (j + 1) := by rw [reverseDeletedWord_length]; omega
  rw [orderedStepAfter, ite_eq_left hlt, hi, transitionLaw,
    reverseDeletedWord_attach k tail (by omega : k - 1 - (j + 1) < k - 1)]
  simp

theorem shorterCoalescentHistoryLaw_relabel (F : Forest) (e : Label ≃ Label) (t : ℕ) :
    (shorterCoalescentHistoryLaw F t).map (FiniteMarkov.History.map (fun G => relabel G e)) =
      shorterCoalescentHistoryLaw (relabel F e) t := by
  have hh := FiniteMarkov.map_historyLaw (Measure.dirac F)
    (fun _ => joinLaw) (fun _ => joinLaw) (fun G => relabel G e) t
    (fun _ _ => Filter.Eventually.of_forall (fun G => relabel_joinLaw G e))
  rw [Measure.map_dirac' measurable_from_top] at hh
  exact hh

def extendSourceShorterHistory (k : ℕ) (tail : Word)
    (h : FiniteMarkov.History Forest) (g : FiniteMarkov.History InitializationSample) :
    FiniteMarkov.History Forest :=
  FiniteMarkov.History.map
    (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length))
    ((FiniteMarkov.History.map InitializationSample.shorter g).appendPast h.past)

noncomputable def sourceShorterHistoryLaw (k : ℕ) (tail : Word) :
    Measure (FiniteMarkov.History Forest) :=
  (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
    tail.length).bind (fun h => (delayedHistoryLaw h.current k (k - 1)).map
      (extendSourceShorterHistory k tail h))

theorem sourceShorterHistoryLaw_eq (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    sourceShorterHistoryLaw k tail =
      orderedHistoryLaw (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
        (reverseDeletedWord k tail).length := by
  let e := deletionLabelEquiv (reverseDeletedWord k tail).length
  let x := (reverseDeletedWord k tail).toSigns
  let n := (reverseDeletedWord k tail).length
  have hn : n = tail.length + (k - 1) := by
    dsimp only [n]
    rw [reverseDeletedWord_length]
    omega
  have hsplit : orderedHistoryLaw x n n =
      (orderedHistoryLaw x n tail.length).bind (fun h =>
        (shorterCoalescentHistoryLaw h.current (k - 1)).map (FiniteMarkov.History.merge h)) := by
    change FiniteMarkov.historyLaw (Measure.dirac (initial x n)) (orderedStepAfter x n) n = _
    conv_lhs => arg 3; rw [hn]
    rw [FiniteMarkov.historyLaw_add]
    congr 1
    funext h
    congr 1
    apply FiniteMarkov.historyLaw_congr
    intro j hj F
    exact orderedStepAfter_deleted_join k tail hj F
  rw [hsplit, ← orderedHistoryLaw_deletion_tail k hk tail,
    Measure.bind_map
      (m := orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length tail.length)
      (f := FiniteMarkov.History.map (fun F => relabel F e))
      (g := fun h : FiniteMarkov.History Forest =>
        (shorterCoalescentHistoryLaw h.current (k - 1)).map (FiniteMarkov.History.merge h))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  unfold sourceShorterHistoryLaw
  apply Measure.bind_congr_right
  filter_upwards [sourceTailHistory_parameters k tail ha] with h hF
  have hshort := delayedHistoryLaw_shorter h.current hF.1 (by omega) (k - 1)
    (by simpa only [hF.2] using (le_rfl : k - 1 ≤ k - 1))
  have hrel := shorterCoalescentHistoryLaw_relabel h.current e (k - 1)
  change (delayedHistoryLaw h.current k (k - 1)).map (extendSourceShorterHistory k tail h) =
    (shorterCoalescentHistoryLaw (relabel h.current e) (k - 1)).map
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

theorem delayedHistoryLaw_current (F : Forest) (i t : ℕ) :
    (delayedHistoryLaw F i t).map FiniteMarkov.History.current = delayedLawAfter F i t := by
  rw [delayedHistoryLaw, FiniteMarkov.historyLaw_current, finiteRunLaw_delayed]

theorem sourceShorterHistoryLaw_current (k : ℕ) (tail : Word) :
    (sourceShorterHistoryLaw k tail).map FiniteMarkov.History.current =
      (sourceDelayedLaw k tail (k - 1)).map (fun z =>
        relabel z.shorter (deletionLabelEquiv (reverseDeletedWord k tail).length)) := by
  rw [sourceShorterHistoryLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    sourceDelayedLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  have htail : initializationTailLaw k tail =
      (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
        tail.length).map FiniteMarkov.History.current :=
    (orderedHistoryLaw_current _ _ _).symm
  rw [htail, Measure.bind_map
    (m := orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length tail.length)
    (f := FiniteMarkov.History.current)
    (g := fun F => (delayedLawAfter F k (k - 1)).map
      (fun z => relabel z.shorter (deletionLabelEquiv (reverseDeletedWord k tail).length)))
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  congr 1
  funext h
  rw [Measure.map_map measurable_from_top measurable_from_top,
    ← delayedHistoryLaw_current h.current k (k - 1),
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

/-- The actual terminal shorter forest, with its bookkeeping labels shifted,
has exactly the shortened word's ordered-tree law. -/
theorem sourceDelayedLaw_shorter_treeLaw (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    (sourceDelayedLaw k tail (k - 1)).map (fun z =>
        relabel z.shorter (deletionLabelEquiv (reverseDeletedWord k tail).length)) =
      treeLaw (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length := by
  rw [← sourceShorterHistoryLaw_current, sourceShorterHistoryLaw_eq k hk tail ha,
    orderedHistoryLaw_current]
  rfl

end FreezingGrowth.ReverseOrdered
