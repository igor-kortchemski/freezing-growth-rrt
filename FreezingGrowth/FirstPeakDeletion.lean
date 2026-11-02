module

public import FreezingGrowth.ChoiceSequence

/-!
# Deterministic effect of deleting the first peak

Deleting the last attachment of the initial positive run and the first freeze
preserves admissibility. The two active-count profiles coincide along the
remaining tail, and the number of attachments decreases by one. These are the
deterministic prerequisites in Section 3.2; stochastic height domination still
requires the coupling argument.
-/

@[expose] public section

namespace FreezingGrowth.Word

theorem toSigns_append_right (xs ys : Word) (j : ℕ) :
    toSigns (xs ++ ys) (xs.length + j + 1) = toSigns ys (j + 1) := by
  simp only [toSigns_succ]
  rw [List.getElem?_append_right (by omega)]
  simp

theorem activeCount_append_add (xs ys : Word) (j : ℕ) :
    activeCount (toSigns (xs ++ ys)) (xs.length + j) =
      activeCount (toSigns xs) xs.length + activeCount (toSigns ys) j - 1 := by
  induction j with
  | zero => simp [activeCount_append_left xs ys le_rfl]
  | succ j ih =>
    rw [show xs.length + (j + 1) = xs.length + j + 1 by omega,
      activeCount_succ, toSigns_append_right, ih, activeCount_succ]
    omega

theorem plusCount_append_add (xs ys : Word) (j : ℕ) :
    plusCount (toSigns (xs ++ ys)) (xs.length + j) =
      plusCount (toSigns xs) xs.length + plusCount (toSigns ys) j := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, plusCount_zero]
    apply plusCount_congr
    exact fun i hi => toSigns_append_left xs ys hi
  | succ j ih =>
    rw [show xs.length + (j + 1) = xs.length + j + 1 by omega,
      plusCount_succ, toSigns_append_right, ih, plusCount_succ]
    omega

theorem attachments_append (xs ys : Word) :
    attachments (xs ++ ys) = attachments xs + attachments ys := by
  simp only [attachments, List.length_append, plusCount_append_add]

/-- Replacing a valid prefix by another valid prefix with the same terminal
active count preserves the admissibility of any fixed tail. -/
theorem admissible_append_of_eq_activeCount {xs ys tail : Word}
    (hy : admissible ys)
    (heq : activeCount (toSigns xs) xs.length = activeCount (toSigns ys) ys.length)
    (h : admissible (xs ++ tail)) : admissible (ys ++ tail) := by
  intro j hj
  by_cases hprefix : j < ys.length
  · rw [activeCount_append_left ys tail hprefix.le]
    exact hy j hprefix
  · have hjlen : ys.length ≤ j := by omega
    have htail : j - ys.length < tail.length := by
      simp only [List.length_append] at hj
      omega
    have hp := h (xs.length + (j - ys.length)) (by
      simp only [List.length_append]
      omega)
    rw [activeCount_append_add, heq] at hp
    rw [show j = ys.length + (j - ys.length) from (Nat.add_sub_of_le hjlen).symm,
      activeCount_append_add]
    exact hp

theorem first_peak_prefix_activeCount (k : ℕ) :
    activeCount (toSigns (List.replicate k true ++ [false])) (k + 1) = k := by
  rw [show k + 1 = (List.replicate k true).length + 1 by simp,
    activeCount_append_add]
  simp only [List.length_replicate, activeCount_replicate_true le_rfl]
  have hz : activeCount (toSigns [false]) 1 = 0 := by
    norm_num [activeCount, toSigns]
  rw [hz]
  omega

/-- The source-facing profile matching after deletion of the first peak.
The identity also holds beyond the tail, for the shared default extension. -/
theorem first_peak_deletion_activeCount (k : ℕ) (hk : 1 ≤ k) (tail : Word) (j : ℕ) :
    activeCount (toSigns (List.replicate k true ++ [false] ++ tail)) (k + 1 + j) =
      activeCount (toSigns (List.replicate (k - 1) true ++ tail)) (k - 1 + j) := by
  rw [show k + 1 + j = (List.replicate k true ++ [false]).length + j by simp,
    show k - 1 + j = (List.replicate (k - 1) true).length + j by simp,
    activeCount_append_add, activeCount_append_add]
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    first_peak_prefix_activeCount, activeCount_replicate_true le_rfl]
  omega

/-- The shorter schedule in Theorem 1.3 is admissible, also when it ends at
extinction. This theorem asserts no stochastic comparison. -/
theorem first_peak_deletion_admissible (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (h : admissible (List.replicate k true ++ [false] ++ tail)) :
    admissible (List.replicate (k - 1) true ++ tail) := by
  apply admissible_append_of_eq_activeCount (replicate_true_inFamily (k - 1)).1 _ h
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    first_peak_prefix_activeCount, activeCount_replicate_true le_rfl]
  omega

/-- The deletion removes exactly one attachment. -/
theorem first_peak_deletion_attachments (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    attachments (List.replicate k true ++ [false] ++ tail) =
      attachments (List.replicate (k - 1) true ++ tail) + 1 := by
  rw [attachments_append, attachments_append, attachments_append,
    (replicate_true_inFamily k).2, (replicate_true_inFamily (k - 1)).2]
  have hz : attachments [false] = 0 := by norm_num [attachments, plusCount, toSigns]
  rw [hz]
  omega

end FreezingGrowth.Word
