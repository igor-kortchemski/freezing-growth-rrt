module

public import FreezingGrowth.ReverseOrderedRelabel
public import FreezingGrowth.ReverseSourceLongerHistory

/-! Explicit label transport after deleting the first attachment/freezing
pair. The finite permutation shifts each common-tail freezing index by two. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

/-- Rotate the finite interval of length `n+2` by two positions. -/
def deleteTwoPermutation (n : ℕ) : Equiv.Perm ℕ where
  toFun j := if j < 2 then n + j else if j < n + 2 then j - 2 else j
  invFun j := if j < n then j + 2 else if j < n + 2 then j - n else j
  left_inv j := by dsimp; split_ifs <;> omega
  right_inv j := by dsimp; split_ifs <;> omega

theorem deleteTwoPermutation_tail (n j : ℕ) (hj : 2 ≤ j) (hjn : j < n + 2) :
    deleteTwoPermutation n j = j - 2 := by
  simp only [deleteTwoPermutation, Equiv.coe_fn_mk, ite_eq_right (by omega : ¬j < 2),
    ite_eq_left hjn]

def deletionLabelEquiv (n : ℕ) : Label ≃ Label :=
  Equiv.sumCongr (Equiv.refl ℕ) (deleteTwoPermutation n)

@[simp] theorem deletionLabelEquiv_inl (n j : ℕ) :
    deletionLabelEquiv n (.inl j) = .inl j := rfl

theorem deletionLabelEquiv_tail (n j : ℕ) (hj : 2 ≤ j) (hjn : j < n + 2) :
    deletionLabelEquiv n (.inr j) = .inr (j - 2) := by
  change Sum.inr (deleteTwoPermutation n j) = _
  rw [deleteTwoPermutation_tail n j hj hjn]

def reverseDeletedWord (k : ℕ) (tail : Word) : Word := List.replicate (k - 1) true ++ tail

theorem reverseDeletedWord_length (k : ℕ) (tail : Word) :
    (reverseDeletedWord k tail).length = k - 1 + tail.length := by
  simp only [reverseDeletedWord, List.length_append, List.length_replicate]

theorem reversePeakWord_length_deleted (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    (reversePeakWord k tail).length = (reverseDeletedWord k tail).length + 2 := by
  rw [reversePeakWord_length, reverseDeletedWord_length]
  omega

theorem reversePeakWord_tail_sign (k : ℕ) (tail : Word) {t : ℕ} (ht : t < tail.length) :
    (reversePeakWord k tail).toSigns ((reversePeakWord k tail).length - t) =
      tail.toSigns (tail.length - t) := by
  have hindex : (reversePeakWord k tail).length - t =
      (List.replicate k true ++ [false]).length + (tail.length - t - 1) + 1 := by
    simp only [reversePeakWord_length, List.length_append, List.length_replicate,
      List.length_singleton]
    omega
  change Word.toSigns ((List.replicate k true ++ [false]) ++ tail) _ = _
  rw [hindex, Word.toSigns_append_right]
  congr 1
  omega

theorem reverseDeletedWord_tail_sign (k : ℕ) (tail : Word) {t : ℕ} (ht : t < tail.length) :
    (reverseDeletedWord k tail).toSigns ((reverseDeletedWord k tail).length - t) =
      tail.toSigns (tail.length - t) := by
  have hindex : (reverseDeletedWord k tail).length - t =
      (List.replicate (k - 1) true).length + (tail.length - t - 1) + 1 := by
    rw [reverseDeletedWord_length, List.length_replicate]
    omega
  change Word.toSigns (List.replicate (k - 1) true ++ tail) _ = _
  rw [hindex, Word.toSigns_append_right]
  congr 1
  omega

theorem reversePeakWord_terminal_activeCount (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    activeCount (reversePeakWord k tail).toSigns (reversePeakWord k tail).length =
      activeCount (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length := by
  simpa only [reversePeakWord, reverseDeletedWord, List.length_append,
    List.length_replicate, List.length_singleton] using
      Word.first_peak_deletion_activeCount k hk tail tail.length

theorem relabel_initial_fixed_active (x y : SignSequence) (n m : ℕ)
    (he : activeCount x n = activeCount y m) (e : Label ≃ Label)
    (hi : ∀ j, e (.inl j) = .inl j) :
    relabel (initial x n) e = initial y m := by
  have hs : ((Finset.range (activeCount x n).toNat).disjSum (∅ : Finset ℕ)).map
      e.toEmbedding = (Finset.range (activeCount y m).toNat).disjSum (∅ : Finset ℕ) := by
    rw [he]
    rw [Finset.map_eq_image]
    conv_rhs => rw [← Finset.image_id (s :=
      (Finset.range (activeCount y m).toNat).disjSum (∅ : Finset ℕ))]
    apply Finset.image_congr
    intro v hv
    cases v with
    | inl j => exact hi j
    | inr j => simp at hv
  have hforest : (Reverse.initial x n).relabel e = Reverse.initial y m := by
    rw [Reverse.initial, Reverse.initial, RootedForest.relabel_isolated, hs]
  have hord : (initial x n).rootOrder.map e = (initial x n).rootOrder := by
    conv_rhs => rw [← List.map_id (l := (initial x n).rootOrder)]
    apply List.map_congr_left
    intro v hv
    have hv' := (RootedForest.mem_roots.mp ((mem_rootOrder (initial x n) v).mp hv)).1
    change v ∈ (Finset.range (activeCount x n).toNat).disjSum (∅ : Finset ℕ) at hv'
    cases v with
    | inl j => exact hi j
    | inr j => simp at hv'
  apply Forest.ext_data
  · exact hforest
  · change (initial x n).rootOrder.map e = _
    rw [hord]
    simp only [initial, Reverse.initial, he]

theorem relabel_deletion_initial (k : ℕ) (hk : 1 ≤ k) (tail : Word) :
    relabel (initial (reversePeakWord k tail).toSigns (reversePeakWord k tail).length)
        (deletionLabelEquiv (reverseDeletedWord k tail).length) =
      initial (reverseDeletedWord k tail).toSigns (reverseDeletedWord k tail).length :=
  relabel_initial_fixed_active _ _ _ _ (reversePeakWord_terminal_activeCount k hk tail) _
    (deletionLabelEquiv_inl _)

end FreezingGrowth.ReverseOrdered
