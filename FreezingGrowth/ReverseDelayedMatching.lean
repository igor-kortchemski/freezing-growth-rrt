module

public import FreezingGrowth.ReverseDistinguishedInitialization
public import FreezingGrowth.ReverseRootedForestExtensionality

/-! Local full-forest matching while the distinguished singleton is unused.
Adjoining its fresh vertex commutes with a join of two old roots; positive
original positions are related explicitly to zero-based shortened-list positions. -/

@[expose] public section
namespace FreezingGrowth

open scoped Classical

namespace RootedForest

variable {V : Type*} [DecidableEq V]

/-- Adjoining a fresh isolated vertex commutes with a graft between old roots,
in all forest fields, including the actual parent map and vertex labels. -/
theorem adjoin_join_commute (F : RootedForest V) {d a b : V}
    (hd : d ∉ F.vertices) (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.adjoin d hd).join a b
        (by rw [adjoin_roots]; exact Finset.mem_insert_of_mem ha)
        (by rw [adjoin_roots]; exact Finset.mem_insert_of_mem hb) hab =
      (F.join a b ha hb hab).adjoin d hd := by
  have hdb : d ≠ b := fun he => hd (he.symm ▸ (mem_roots.mp hb).1)
  apply ext_data
  · rfl
  · funext v
    by_cases hvd : v = d
    · subst v
      simp [adjoin, join, hdb]
    · simp [adjoin, join, hvd]
  · funext v
    by_cases hvd : v = d
    · subst v
      simp [adjoin, join, hdb]
    · simp [adjoin, join, hvd]
  · funext v
    by_cases hvd : v = d
    · subst v
      simp [adjoin, join, hdb]
    · simp [adjoin, join, hvd]

end RootedForest

namespace ReverseOrdered

theorem Forest.ext_data {F G : Forest} (hf : F.forest = G.forest)
    (ho : F.rootOrder = G.rootOrder) : F = G := by
  cases F
  cases G
  cases hf
  cases ho
  rfl

theorem prependLabel_pair_valid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    p ∈ (prependLabel F i).forest.roots.offDiag := by
  simp only [prependLabel, dite_eq_right hi, RootedForest.adjoin_roots]
  exact Finset.mem_offDiag.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_offDiag.mp hp).1,
    Finset.mem_insert_of_mem (Finset.mem_offDiag.mp hp).2.1, (Finset.mem_offDiag.mp hp).2.2⟩

theorem joinChoice_fresh (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    Sum.inr i ∉ (joinChoice F p).forest.vertices := by
  rw [joinChoice_forest, RootedForest.joinChoice, dite_eq_left hp]
  exact hi

/-- Exact delayed list matching: the current ordinary graft can be carried
out before or after the fresh distinguished singleton is prepended. -/
theorem prependLabel_joinChoice_commute (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    joinChoice (prependLabel F i) p = prependLabel (joinChoice F p) i := by
  have hp' := prependLabel_pair_valid F hi hp
  have hi' := joinChoice_fresh F hi hp
  have hpA : p ∈ (F.forest.adjoin (.inr i) hi).roots.offDiag := by
    simpa only [prependLabel, dite_eq_right hi] using hp'
  have hbd : Sum.inr i ≠ p.2 := fun he =>
    hi (he.symm ▸ (RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).2.1).1)
  apply Forest.ext_data
  · simp only [joinChoice_forest, prependLabel_forest, Reverse.insertLabel,
      dite_eq_right hi, RootedForest.joinChoice, dite_eq_left hp, dite_eq_left hpA,
      RootedForest.join_vertices]
    exact RootedForest.adjoin_join_commute F.forest hi (Finset.mem_offDiag.mp hp).1
      (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2
  · rw [joinChoice_rootOrder _ hp', prependLabel_rootOrder F hi,
      prependLabel_rootOrder _ hi', joinChoice_rootOrder F hp]
    simp [hbd]

theorem oldPair_avoids_prepend (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) : p ∈ avoidsDistinguished (.inr i) := by
  constructor
  · intro he
    exact hi (he ▸ (RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).1).1)
  · intro he
    exact hi (he ▸ (RootedForest.mem_roots.mp (Finset.mem_offDiag.mp hp).2.1).1)

/-- On an unused distinguished component, the actual order-modified graft
has the same full delayed matching as the standard graft. -/
theorem distinguishedJoinChoice_old_pair (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    distinguishedJoinChoice (prependLabel F i) (.inr i) p =
      prependLabel (joinChoice F p) i := by
  rw [distinguishedJoinChoice, dite_eq_left (prependLabel_pair_valid F hi hp),
    ite_eq_right (oldPair_avoids_prepend F hi hp).1]
  exact prependLabel_joinChoice_commute F hi hp

/-- A shortened-list position is shifted by one in the list with the new
distinguished head. The stored source position is this shifted natural number. -/
def prependIndex (F : Forest) {i : ℕ} (hi : Sum.inr i ∉ F.forest.vertices)
    (a : Fin F.forest.roots.card) : Fin (prependLabel F i).forest.roots.card :=
  ⟨a.val + 1, by rw [prependLabel_roots_card F hi]; omega⟩

theorem rootEnumeration_prepend_index (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (a : Fin F.forest.roots.card) :
    (rootEnumeration (prependLabel F i) (prependIndex F hi a)).val =
      (rootEnumeration F a).val := by
  rw [rootEnumeration_get, rootEnumeration_get]
  simp [prependIndex, prependLabel, hi]

theorem indexedPair_prepend_index (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin F.forest.roots.card × Fin F.forest.roots.card) :
    (prependLabel F i).forest.indexedPair (rootEnumeration (prependLabel F i))
        (prependIndex F hi p.1, prependIndex F hi p.2) =
      F.forest.indexedPair (rootEnumeration F) p := by
  apply Prod.ext <;> exact rootEnumeration_prepend_index F hi _

/-- Every positive original position is the successor of exactly the
shortened-list position obtained by subtracting one. -/
def lowerPositiveIndex (F : Forest) {i : ℕ} (hi : Sum.inr i ∉ F.forest.vertices)
    (a : Fin (prependLabel F i).forest.roots.card) (ha : 0 < a.val) :
    Fin F.forest.roots.card :=
  ⟨a.val - 1, by
    have hlt := a.isLt.trans_le (prependLabel_roots_card F hi).le
    omega⟩

theorem prependIndex_lowerPositiveIndex (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (a : Fin (prependLabel F i).forest.roots.card)
    (ha : 0 < a.val) : prependIndex F hi (lowerPositiveIndex F hi a ha) = a := by
  apply Fin.ext
  dsimp [prependIndex, lowerPositiveIndex]
  omega

/-- Full labelled-forest/list matching in source initialization case (i).
The delayed pair still stores the original positive positions. -/
theorem initializationChoice_pending_matching (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin F.forest.roots.card × Fin F.forest.roots.card) (hp : p.1 ≠ p.2) :
    (initializationChoice F i (prependIndex F hi p.1, prependIndex F hi p.2)).longer =
        prependLabel (joinChoice F (F.forest.indexedPair (rootEnumeration F) p)) i ∧
    (initializationChoice F i (prependIndex F hi p.1, prependIndex F hi p.2)).used = false ∧
    (initializationChoice F i (prependIndex F hi p.1, prependIndex F hi p.2)).delayedPair =
      (p.1.val + 1, p.2.val + 1) := by
  constructor
  · change distinguishedJoinChoice _ _ _ = _
    rw [indexedPair_prepend_index F hi p]
    exact distinguishedJoinChoice_old_pair F hi (indexedPair_valid F p hp)
  · simp [initializationChoice, prependIndex]

end ReverseOrdered
end FreezingGrowth
