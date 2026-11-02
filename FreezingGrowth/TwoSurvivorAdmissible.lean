module

public import FreezingGrowth.FirstPeakDeletion
public import FreezingGrowth.MainStatements

/-! Deterministic admissibility of all three two-survivor schedules used in
Proposition 1.1(i) and (ii), including arbitrary attachment continuations. -/

@[expose] public section
namespace FreezingGrowth

namespace Word

theorem toSigns_replicate_false (n i : ℕ) :
    toSigns (List.replicate n false) i = false := by
  unfold toSigns
  rw [List.getElem?_replicate]
  split_ifs <;> rfl

theorem activeCount_replicate_false (n j : ℕ) :
    activeCount (toSigns (List.replicate n false)) j = 1 - (j : ℤ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [activeCount_succ, ih, toSigns_replicate_false]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    omega

theorem admissible_append_attachments (xs : Word) (hx : xs.admissible)
    (hp : 0 < activeCount xs.toSigns xs.length) (n : ℕ) :
    (xs ++ List.replicate n true).admissible := by
  intro j hj
  by_cases hpre : j < xs.length
  · rw [activeCount_append_left xs _ hpre.le]
    exact hx j hpre
  · have hjn : j - xs.length ≤ n := by
      simp only [List.length_append, List.length_replicate] at hj
      omega
    rw [show j = xs.length + (j - xs.length) by omega,
      activeCount_append_add, activeCount_replicate_true hjn]
    omega

end Word

theorem twoActivePrefix_activeCount_early (m j : ℕ) (hj : j ≤ m) :
    activeCount (twoActivePrefix m).toSigns j = (j : ℤ) + 1 := by
  unfold twoActivePrefix
  rw [Word.activeCount_append_left _ _ (by simpa using hj)]
  exact Word.activeCount_replicate_true hj

/-- The chosen `Word.toSigns` extension also freezes beyond the finite prefix,
so this count identity holds for every `k`; admissibility uses it only within
the actual word. -/
theorem twoActivePrefix_activeCount_late (m k : ℕ) :
    activeCount (twoActivePrefix m).toSigns (m + k) = (m : ℤ) + 1 - k := by
  unfold twoActivePrefix
  rw [show m + k = (List.replicate m true).length + k by simp,
    Word.activeCount_append_add, Word.activeCount_replicate_false]
  simp only [List.length_replicate, Word.activeCount_replicate_true le_rfl]
  ring

theorem twoActivePrefix_terminal_count (m : ℕ) (hm : 1 ≤ m) :
    activeCount (twoActivePrefix m).toSigns (twoActivePrefix m).length = 2 := by
  rw [show (twoActivePrefix m).length = m + (m - 1) by simp [twoActivePrefix],
    twoActivePrefix_activeCount_late]
  omega

theorem twoActivePrefix_positive (m : ℕ) (hm : 1 ≤ m) :
    PositiveThrough (twoActivePrefix m).toSigns (twoActivePrefix m).length := by
  intro j hj
  have hlen : (twoActivePrefix m).length = m + (m - 1) := by simp [twoActivePrefix]
  rw [hlen] at hj
  by_cases hpre : j ≤ m
  · rw [twoActivePrefix_activeCount_early m j hpre]
    omega
  · rw [show j = m + (j - m) by omega, twoActivePrefix_activeCount_late]
    omega

theorem twoActivePrefix_admissible (m : ℕ) (hm : 1 ≤ m) :
    (twoActivePrefix m).admissible :=
  fun j hj => twoActivePrefix_positive m hm j hj.le

theorem twoActivePrefix_append_balanced_pair_positive (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    PositiveThrough (twoActivePrefix m ++ [b, !b]).toSigns
      (twoActivePrefix m ++ [b, !b]).length := by
  intro j hj
  by_cases hpre : j ≤ (twoActivePrefix m).length
  · rw [Word.activeCount_append_left _ _ hpre]
    exact twoActivePrefix_positive m hm j hpre
  · have hjlen : j ≤ (twoActivePrefix m).length + 2 := by simpa using hj
    rw [show j = (twoActivePrefix m).length + (j - (twoActivePrefix m).length) by omega,
      Word.activeCount_append_add, twoActivePrefix_terminal_count m hm]
    have hk : j - (twoActivePrefix m).length = 1 ∨
        j - (twoActivePrefix m).length = 2 := by omega
    rcases hk with hk | hk <;> rw [hk] <;> cases b <;>
      norm_num [activeCount, Word.toSigns, Finset.sum_range_succ]

theorem twoActivePrefix_grow_admissible (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (twoActivePrefix m ++ List.replicate n true).admissible := by
  apply Word.admissible_append_attachments _ (twoActivePrefix_admissible m hm)
  rw [twoActivePrefix_terminal_count m hm]
  norm_num

theorem twoActivePrefix_freeze_attach_admissible (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true).admissible := by
  have hp : PositiveThrough (twoActivePrefix m ++ [false, true]).toSigns
      (twoActivePrefix m ++ [false, true]).length := by
    simpa using twoActivePrefix_append_balanced_pair_positive m hm false
  exact Word.admissible_append_attachments _ (fun j hj => hp j hj.le) (hp _ le_rfl) n

theorem twoActivePrefix_attach_freeze_admissible (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true).admissible := by
  have hp : PositiveThrough (twoActivePrefix m ++ [true, false]).toSigns
      (twoActivePrefix m ++ [true, false]).length := by
    simpa using twoActivePrefix_append_balanced_pair_positive m hm true
  exact Word.admissible_append_attachments _ (fun j hj => hp j hj.le) (hp _ le_rfl) n

end FreezingGrowth
