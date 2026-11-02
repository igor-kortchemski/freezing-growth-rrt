module

public import FreezingGrowth.ChoiceSequence
public import FreezingGrowth.Height

/-!
# Height laws for finite choice sequences

The law depends only on the finite prefix read by Algorithm 1. In particular,
removing a terminal freezing operation preserves the entire height distribution,
including when that operation freezes the last active vertex.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory

namespace Forward

/-- Algorithm 1 uses only the signs at the steps already read. -/
theorem treeLaw_congr {x y : SignSequence} {n : ℕ}
    (h : ∀ i < n, x (i + 1) = y (i + 1)) : treeLaw x n = treeLaw y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [treeLaw]
    rw [ih (fun i hi => h i (by omega)), h n (Nat.lt_succ_self n)]

theorem heightLaw_congr {x y : SignSequence} {n : ℕ}
    (h : ∀ i < n, x (i + 1) = y (i + 1)) : heightLaw x n = heightLaw y n := by
  unfold heightLaw
  rw [treeLaw_congr h]

end Forward

namespace Word

/-- The height law for the entire finite choice word. -/
noncomputable def heightLaw (xs : Word) : Measure ℕ :=
  Forward.heightLaw xs.toSigns xs.length

/-- Expected height for the actual forward random tree. -/
noncomputable def expectedHeight (xs : Word) : ℝ :=
  ∫ h : ℕ, (h : ℝ) ∂xs.heightLaw

/-- Natural-height stochastic domination, expressed by all upper tails. -/
def HeightLE (xs ys : Word) : Prop :=
  ∀ h : ℕ, xs.heightLaw {k | h ≤ k} ≤ ys.heightLaw {k | h ≤ k}

instance heightLaw_probability (xs : Word) : IsProbabilityMeasure xs.heightLaw :=
  Forward.heightLaw_probability xs.toSigns xs.length

/-- A finite prefix has the same law as stopping the original schedule there. -/
theorem heightLaw_take (xs : Word) {k : ℕ} (hk : k ≤ xs.length) :
    heightLaw (xs.take k) = Forward.heightLaw xs.toSigns k := by
  unfold heightLaw
  rw [List.length_take, Nat.min_eq_left hk]
  apply Forward.heightLaw_congr
  intro i hi
  exact toSigns_take xs hi

theorem heightLaw_append_left (xs ys : Word) :
    Forward.heightLaw (toSigns (xs ++ ys)) xs.length = xs.heightLaw := by
  apply Forward.heightLaw_congr
  intro i hi
  exact toSigns_append_left xs ys hi

/-- A final freezing step never changes the height distribution. -/
theorem heightLaw_take_pred_of_last_freeze {xs : Word} (hlen : 0 < xs.length)
    (hx : xs.toSigns xs.length = false) :
    heightLaw (xs.take (xs.length - 1)) = xs.heightLaw := by
  rw [heightLaw_take xs (Nat.sub_le _ _)]
  change Forward.heightLaw xs.toSigns (xs.length - 1) =
    Forward.heightLaw xs.toSigns xs.length
  have hsucc : xs.length - 1 + 1 = xs.length := by omega
  have hfreeze : xs.toSigns (xs.length - 1 + 1) = false := by
    simpa only [hsucc] using hx
  simpa only [hsucc] using
    (Forward.heightLaw_succ_freeze xs.toSigns (xs.length - 1) hfreeze).symm

/-- The endpoint reduction missing from the printed low-values argument:
terminal extinction may be removed before sampling an active vertex. -/
theorem heightLaw_take_pred_of_terminal_zero {xs : Word} (ha : admissible xs)
    (hz : activeCount xs.toSigns xs.length = 0) :
    heightLaw (xs.take (xs.length - 1)) = xs.heightLaw := by
  obtain ⟨hlen, hfreeze, _, _⟩ := terminal_zero_last_freeze ha hz
  exact heightLaw_take_pred_of_last_freeze hlen hfreeze

theorem expectedHeight_take_pred_of_terminal_zero {xs : Word} (ha : admissible xs)
    (hz : activeCount xs.toSigns xs.length = 0) :
    expectedHeight (xs.take (xs.length - 1)) = xs.expectedHeight := by
  unfold expectedHeight
  rw [heightLaw_take_pred_of_terminal_zero ha hz]

/-- Removing terminal extinction retains family membership as well as height. -/
theorem take_pred_inFamily_of_terminal_zero {n : ℕ} {xs : Word} (h : InFamily n xs)
    (hz : activeCount xs.toSigns xs.length = 0) :
    InFamily n (xs.take (xs.length - 1)) :=
  ⟨admissible_take h.1 _, (attachments_take_pred_of_terminal_zero h.1 hz).trans h.2⟩

end Word
end FreezingGrowth
