module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Tactic

/-!
# Deterministic height-list operations for Algorithm 3

The list graft updates the receiving component by `max (H a) (H b + 1)`
and deletes the donor position. These lemmas give synchronized monotonicity,
the pending distinguished-singleton identity, and both resolution cases.
The projection from actual component heights and the joint probability-law
invariant remain separate; these deterministic helpers do not assume either.
-/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

def LE (xs ys : List ℕ) : Prop := List.Forall₂ (· ≤ ·) xs ys

theorem le_refl (xs : List ℕ) : LE xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons le_rfl ih

theorem le_getD {xs ys : List ℕ} (h : LE xs ys) (i : ℕ) :
    xs[i]?.getD 0 ≤ ys[i]?.getD 0 := by
  induction h generalizing i with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
    cases i with
    | zero => simpa using hxy
    | succ i => simpa using ih i

theorem le_set {xs ys : List ℕ} (h : LE xs ys) {a b : ℕ} (hab : a ≤ b) (i : ℕ) :
    LE (xs.set i a) (ys.set i b) := by
  induction h generalizing i with
  | nil => simp [LE]
  | @cons x y xs ys hxy htail ih =>
    cases i with
    | zero => exact .cons hab htail
    | succ i => exact .cons hxy (ih i)

theorem le_eraseIdx {xs ys : List ℕ} (h : LE xs ys) (i : ℕ) :
    LE (xs.eraseIdx i) (ys.eraseIdx i) := by
  induction h generalizing i with
  | nil => exact .nil
  | @cons x y xs ys hxy htail ih =>
    cases i with
    | zero => exact htail
    | succ i => exact .cons hxy (ih i)

/-- Componentwise domination implies domination of the actual maximum
component height. -/
theorem le_maximum {xs ys : List ℕ} (h : LE xs ys) :
    xs.toFinset.sup id ≤ ys.toFinset.sup id := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy htail ih =>
    simpa using max_le_max hxy ih

/-- The source ordered graft's component-height operation, totalized at
out-of-range indices by the standard list operations. -/
def graft (xs : List ℕ) (a b : ℕ) : List ℕ :=
  (xs.set a (max (xs[a]?.getD 0) (xs[b]?.getD 0 + 1))).eraseIdx b

theorem graft_length (xs : List ℕ) (a b : ℕ) (hb : b < xs.length) :
    (graft xs a b).length = xs.length - 1 := by
  simp [graft, List.length_eraseIdx, hb]

/-- A pending pair represents two forests with the same component count. -/
theorem pending_length (xs : List ℕ) (a b : ℕ) (hb : b < xs.length) :
    (0 :: graft xs a b).length = xs.length := by
  rw [List.length_cons, graft_length xs a b hb]
  omega

/-- Once the distinguished vertex has been used, synchronized grafting
preserves componentwise height domination (source step A). -/
theorem graft_mono {xs ys : List ℕ} (h : LE xs ys) (a b : ℕ) :
    LE (graft xs a b) (graft ys a b) := by
  apply le_eraseIdx
  exact le_set h (max_le_max (le_getD h a) (Nat.add_le_add_right (le_getD h b) 1)) a

/-- A graft avoiding index zero leaves the distinguished singleton untouched,
and performs exactly the delayed graft on the shorter component list. -/
theorem graft_prepend_zero (xs : List ℕ) (a b : ℕ) :
    graft (0 :: xs) (a + 1) (b + 1) = 0 :: graft xs a b := by
  simp [graft]

theorem le_set_of_getD_le (xs : List ℕ) (i b : ℕ) (hb : xs[i]?.getD 0 ≤ b) :
    LE xs (xs.set i b) := by
  induction xs generalizing i with
  | nil => exact .nil
  | cons x xs ih =>
    cases i with
    | zero => exact .cons (by simpa using hb) (le_refl xs)
    | succ i => exact .cons le_rfl (ih i (by simpa using hb))

/-- If the distinguished singleton receives a component, the latter's height
increases by one at its retained position. -/
def resolveReceiver (xs : List ℕ) (i : ℕ) : List ℕ :=
  xs.set i (xs[i]?.getD 0 + 1)

/-- If the distinguished singleton is grafted below a component root, the
receiver's height becomes the maximum of its old height and one. -/
def resolveDonor (xs : List ℕ) (i : ℕ) : List ℕ :=
  xs.set i (max (xs[i]?.getD 0) 1)

theorem le_resolveReceiver (xs : List ℕ) (i : ℕ) : LE xs (resolveReceiver xs i) :=
  le_set_of_getD_le xs i _ (Nat.le_succ _)

theorem le_resolveDonor (xs : List ℕ) (i : ℕ) : LE xs (resolveDonor xs i) :=
  le_set_of_getD_le xs i _ (le_max_left _ _)

/-- An ordinary graft with the distinguished singleton as receiver keeps
that receiver at the front. Algorithm 3 subsequently changes this order. -/
theorem graft_distinguished_receiver (xs : List ℕ) (i : ℕ) :
    graft (0 :: xs) 0 (i + 1) = (xs[i]?.getD 0 + 1) :: xs.eraseIdx i := by
  simp [graft]

/-- With the distinguished singleton as donor, deleting index zero already
has exactly the order used by Algorithm 3. -/
theorem graft_distinguished_donor (xs : List ℕ) (i : ℕ) :
    graft (0 :: xs) (i + 1) 0 = resolveDonor xs i := by
  simp [graft, resolveDonor]

/-- The modified receiver case preserves precisely the multiset of actual
component heights. Its order differs from the ordinary list graft. -/
theorem graft_receiver_perm_resolution (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    (graft (0 :: xs) 0 (i + 1)).Perm (resolveReceiver xs i) := by
  rw [graft_distinguished_receiver]
  exact (List.set_perm_cons_eraseIdx hi _).symm

end FreezingGrowth.ReverseHeightList
