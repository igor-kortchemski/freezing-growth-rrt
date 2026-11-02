module

public import FreezingGrowth.ReverseDeletionLabels

/-! The complete common-tail coupling in source C1. One sequence of ordered
forest choices serves both words after the explicit two-index label shift. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

theorem orderedStepAfter_deletion_tail (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    {t : ℕ} (ht : t < tail.length) (F : Forest) :
    (orderedStepAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length t F).map
        (fun G => relabel G (deletionLabelEquiv (reverseDeletedWord k tail).length)) =
      orderedStepAfter (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length t
        (relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length)) := by
  have hlong : t < (reversePeakWord k tail).length := by
    rw [reversePeakWord_length]
    omega
  have hshort : t < (reverseDeletedWord k tail).length := by
    rw [reverseDeletedWord_length]
    omega
  have hli : (reversePeakWord k tail).length - (t + 1) + 1 =
      (reversePeakWord k tail).length - t := by omega
  have hsi : (reverseDeletedWord k tail).length - (t + 1) + 1 =
      (reverseDeletedWord k tail).length - t := by omega
  have hshift : deletionLabelEquiv (reverseDeletedWord k tail).length
      (.inr ((reversePeakWord k tail).length - (t + 1))) =
      .inr ((reverseDeletedWord k tail).length - (t + 1)) := by
    rw [deletionLabelEquiv_tail]
    · congr 1
      rw [reversePeakWord_length_deleted k hk tail]
      omega
    · rw [reversePeakWord_length]
      omega
    · rw [reversePeakWord_length_deleted k hk tail]
      omega
  rw [orderedStepAfter, ite_eq_left hlong, orderedStepAfter, ite_eq_left hshort,
    transitionLaw, transitionLaw, hli, hsi,
    reversePeakWord_tail_sign k tail ht, reverseDeletedWord_tail_sign k tail ht]
  cases hs : tail.toSigns (tail.length - t) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Measure.map_dirac' measurable_from_top]
    congr 1
    exact relabel_insertLabel F _ _ _ hshift
  | true =>
    simp only [↓reduceIte]
    exact relabel_joinLaw F _

/-- Full finite common-tail history equality, preserving the exact choice
dependence across all phases and the actual ordered rooted forests. -/
theorem orderedHistoryLaw_deletion_tail (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
      tail.length).map
        (FiniteMarkov.History.map
          (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length))) =
      orderedHistoryLaw (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
        tail.length := by
  have hh := FiniteMarkov.map_historyLaw
    (Measure.dirac (initial (reversePeakWord k tail).toSigns (reversePeakWord k tail).length))
    (orderedStepAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length)
    (orderedStepAfter (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length)
    (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length)) tail.length
    (fun t ht => Filter.Eventually.of_forall (orderedStepAfter_deletion_tail k hk tail ht))
  rw [Measure.map_dirac' measurable_from_top, relabel_deletion_initial k hk tail] at hh
  exact hh

theorem initializationTailLaw_deletion (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    (initializationTailLaw k tail).map
        (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length)) =
      lawAfter (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length
        tail.length := by
  have hh := congrArg (fun μ : Measure (FiniteMarkov.History Forest) =>
    μ.map FiniteMarkov.History.current) (orderedHistoryLaw_deletion_tail k hk tail)
  rw [orderedHistoryLaw_current,
    Measure.map_map measurable_from_top measurable_from_top] at hh
  change (lawAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length tail.length).map
    (fun F => relabel F (deletionLabelEquiv (reverseDeletedWord k tail).length)) = _
  rw [← orderedHistoryLaw_current (reversePeakWord k tail).toSigns
    (reversePeakWord k tail).length tail.length,
    Measure.map_map measurable_from_top measurable_from_top]
  exact hh

end FreezingGrowth.ReverseOrdered
