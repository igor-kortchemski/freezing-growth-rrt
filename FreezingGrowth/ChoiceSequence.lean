module

public import FreezingGrowth.Extinction
public import Mathlib.Data.Set.Finite.List

/-!
# Finite choice sequences

A finite word uses `true` for attachment and `false` for freezing. Its extension
to positive-index schedules is used only through the word's length. Admissibility
requires positivity before each step and therefore permits extinction at the
last step, exactly as in the Introduction's definition of `𝕏ₙ`.
-/

@[expose] public section

namespace FreezingGrowth

abbrev Word := List Bool

namespace Word

/-- Extend a finite word to the positive-index convention of `SignSequence`.
The value at zero is unused; indices beyond the word are set to freezing. -/
def toSigns (xs : Word) (i : ℕ) : Bool := xs[i - 1]?.getD false

/-- Every operation has at least one active vertex to choose from. -/
def admissible (xs : Word) : Prop :=
  ∀ j < xs.length, 0 < activeCount (toSigns xs) j

/-- The number of attachment operations, hence the number of tree edges. -/
def attachments (xs : Word) : ℕ := plusCount (toSigns xs) xs.length

/-- The Introduction's family `𝕏ₙ`, including terminal extinction. -/
def InFamily (n : ℕ) (xs : Word) : Prop := admissible xs ∧ attachments xs = n

@[simp] theorem toSigns_succ (xs : Word) (i : ℕ) :
    toSigns xs (i + 1) = xs[i]?.getD false := by
  simp [toSigns]

@[simp] theorem admissible_nil : admissible [] := by
  simp [admissible]

@[simp] theorem attachments_nil : attachments [] = 0 := by
  simp [attachments]

theorem toSigns_append_left (xs ys : Word) {i : ℕ} (hi : i < xs.length) :
    toSigns (xs ++ ys) (i + 1) = toSigns xs (i + 1) := by
  simp only [toSigns_succ]
  rw [List.getElem?_append_left hi]

theorem toSigns_take (xs : Word) {i k : ℕ} (hi : i < k) :
    toSigns (xs.take k) (i + 1) = toSigns xs (i + 1) := by
  simp only [toSigns_succ]
  rw [List.getElem?_take_of_lt hi]

/-- Counts depend only on the operations actually read. -/
theorem plusCount_congr {x y : SignSequence} {n : ℕ}
    (h : ∀ i < n, x (i + 1) = y (i + 1)) : plusCount x n = plusCount y n := by
  unfold plusCount
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem activeCount_congr {x y : SignSequence} {n : ℕ}
    (h : ∀ i < n, x (i + 1) = y (i + 1)) : activeCount x n = activeCount y n := by
  unfold activeCount
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem plusCount_take (xs : Word) {j k : ℕ} (hj : j ≤ k) :
    plusCount (toSigns (xs.take k)) j = plusCount (toSigns xs) j := by
  apply plusCount_congr
  intro i hi
  exact toSigns_take xs (hi.trans_le hj)

theorem activeCount_take (xs : Word) {j k : ℕ} (hj : j ≤ k) :
    activeCount (toSigns (xs.take k)) j = activeCount (toSigns xs) j := by
  apply activeCount_congr
  intro i hi
  exact toSigns_take xs (hi.trans_le hj)

theorem activeCount_append_left (xs ys : Word) {j : ℕ} (hj : j ≤ xs.length) :
    activeCount (toSigns (xs ++ ys)) j = activeCount (toSigns xs) j := by
  apply activeCount_congr
  intro i hi
  exact toSigns_append_left xs ys (hi.trans_le hj)

theorem plusCount_replicate_true {n j : ℕ} (hj : j ≤ n) :
    plusCount (toSigns (List.replicate n true)) j = j := by
  unfold plusCount
  calc
    _ = ∑ _i ∈ Finset.range j, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := (Finset.mem_range.mp hi).trans_le hj
      simp [toSigns_succ, List.getElem?_replicate_of_lt hin]
    _ = j := by simp

theorem activeCount_replicate_true {n j : ℕ} (hj : j ≤ n) :
    activeCount (toSigns (List.replicate n true)) j = (j : ℤ) + 1 := by
  rw [activeCount_eq, plusCount_replicate_true hj]
  omega

theorem replicate_true_inFamily (n : ℕ) : InFamily n (List.replicate n true) := by
  constructor
  · intro j hj
    simp only [List.length_replicate] at hj
    rw [activeCount_replicate_true hj.le]
    omega
  · simp only [attachments, List.length_replicate, plusCount_replicate_true le_rfl]

theorem family_nonempty (n : ℕ) : {xs : Word | InFamily n xs}.Nonempty :=
  ⟨List.replicate n true, replicate_true_inFamily n⟩

theorem admissible_take {xs : Word} (ha : admissible xs) (k : ℕ) :
    admissible (xs.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  rw [activeCount_take xs (by omega)]
  exact ha j (by omega)

theorem positiveThrough_take {xs : Word} (ha : admissible xs) {k : ℕ}
    (hk : k < xs.length) : PositiveThrough (toSigns (xs.take k)) k := by
  intro j hj
  rw [activeCount_take xs hj]
  exact ha j (hj.trans_lt hk)

/-- Admissibility is exactly survival through the endpoint; equality is allowed. -/
theorem admissible_iff_le_extinctionTime (xs : Word) :
    admissible xs ↔ (xs.length : ℕ∞) ≤ extinctionTime (toSigns xs) := by
  constructor
  · intro ha
    by_contra hn
    have hlt : extinctionTime (toSigns xs) < (xs.length : ℕ∞) := lt_of_not_ge hn
    obtain ⟨k, hk, _⟩ := ENat.le_natCast_iff.mp hlt.le
    have hklt : k < xs.length := by simpa only [hk, ENat.natCast_lt_natCast] using hlt
    have hτk : extinctionTime (toSigns xs) ≤ (k : ℕ∞) := hk.le
    obtain ⟨j, hjk, hz⟩ := (extinctionTime_le_iff (toSigns xs) k).mp hτk
    exact (ha j (hjk.trans_lt hklt)).ne' hz
  · intro hτ j hj
    have hjτ : (j : ℕ∞) < extinctionTime (toSigns xs) :=
      lt_of_lt_of_le (by exact_mod_cast hj) hτ
    exact ((lt_extinctionTime_iff (toSigns xs) j).mp hjτ) j le_rfl

theorem terminal_activeCount_nonneg {xs : Word} (ha : admissible xs) :
    0 ≤ activeCount (toSigns xs) xs.length :=
  activeCount_nonneg_of_le_extinctionTime ((admissible_iff_le_extinctionTime xs).mp ha)

/-- There are at most `n + 1` freezing steps in a word with `n` attachments. -/
theorem length_le_two_mul_attachments_add_one {xs : Word} (ha : admissible xs) :
    xs.length ≤ 2 * attachments xs + 1 := by
  have hn := terminal_activeCount_nonneg ha
  rw [activeCount_eq] at hn
  change 0 ≤ 1 + 2 * (attachments xs : ℤ) - (xs.length : ℤ) at hn
  omega

theorem InFamily.length_le {n : ℕ} {xs : Word} (h : InFamily n xs) :
    xs.length ≤ 2 * n + 1 := by
  simpa only [h.2] using length_le_two_mul_attachments_add_one h.1

/-- Although defined by a union over lengths, the paper's family is finite. -/
theorem family_finite (n : ℕ) : {xs : Word | InFamily n xs}.Finite :=
  (List.finite_length_le Bool (2 * n + 1)).subset (fun _ h => h.length_le)

/-- Terminal extinction is a final freezing step from exactly one active vertex. -/
theorem terminal_zero_last_freeze {xs : Word} (ha : admissible xs)
    (hz : activeCount (toSigns xs) xs.length = 0) :
    0 < xs.length ∧ toSigns xs xs.length = false ∧
      activeCount (toSigns xs) (xs.length - 1) = 1 ∧
      PositiveThrough (toSigns (xs.take (xs.length - 1))) (xs.length - 1) := by
  have hlen : 0 < xs.length := by
    by_contra hn
    have he : xs.length = 0 := by omega
    simp [he] at hz
  have hprev := ha (xs.length - 1) (by omega)
  have hsucc : xs.length - 1 + 1 = xs.length := by omega
  have hstep := activeCount_succ (toSigns xs) (xs.length - 1)
  rw [hsucc, hz] at hstep
  have hfreeze : toSigns xs xs.length = false := by
    cases hs : toSigns xs xs.length with
    | false => rfl
    | true => simp only [hs, ↓reduceIte] at hstep; omega
  have hone : activeCount (toSigns xs) (xs.length - 1) = 1 := by
    simp only [hfreeze, Bool.false_eq_true, ↓reduceIte] at hstep
    omega
  exact ⟨hlen, hfreeze, hone, positiveThrough_take ha (by omega)⟩

/-- Dropping the terminal freezing operation preserves the number of edges. -/
theorem attachments_take_pred_of_terminal_zero {xs : Word} (ha : admissible xs)
    (hz : activeCount (toSigns xs) xs.length = 0) :
    attachments (xs.take (xs.length - 1)) = attachments xs := by
  obtain ⟨hlen, hfreeze, _, _⟩ := terminal_zero_last_freeze ha hz
  have hsucc : xs.length - 1 + 1 = xs.length := by omega
  have hstep := plusCount_succ (toSigns xs) (xs.length - 1)
  rw [hsucc, hfreeze] at hstep
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hstep
  unfold attachments
  rw [List.length_take, Nat.min_eq_left (Nat.sub_le _ _), plusCount_take xs le_rfl]
  exact hstep.symm

end Word
end FreezingGrowth
