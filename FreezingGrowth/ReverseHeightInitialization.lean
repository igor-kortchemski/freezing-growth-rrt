module

public import FreezingGrowth.ReverseHeightProjection

/-!
# Initial and freezing-step component heights

All initial components are isolated, including the empty terminal forest at
extinction. Undoing a freeze appends one fresh zero-height component and
preserves every existing component height and its position.
-/

@[expose] public section

namespace FreezingGrowth.RootedForest

open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem componentHeight_isolated (s : Finset V) (r : V) :
    (isolated s).componentHeight r = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro v _
  exact le_rfl

theorem componentVertices_adjoin_other (F : RootedForest V) {v r : V}
    (hv : v ∉ F.vertices) (hrv : r ≠ v) :
    (F.adjoin v hv).componentVertices r = F.componentVertices r := by
  ext w
  simp only [componentVertices, Finset.mem_filter]
  change (w ∈ insert v F.vertices ∧ (if w = v then v else F.root w) = r) ↔
    (w ∈ F.vertices ∧ F.root w = r)
  constructor
  · rintro ⟨hw, hr⟩
    rcases Finset.mem_insert.mp hw with hw | hw
    · subst w
      exact False.elim (hrv (by simpa using hr.symm))
    · have hwv : w ≠ v := fun h => hv (h ▸ hw)
      exact ⟨hw, by simpa only [ite_eq_right hwv] using hr⟩
  · rintro ⟨hw, hr⟩
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    exact ⟨Finset.mem_insert_of_mem hw, by simpa only [ite_eq_right hwv] using hr⟩

theorem componentHeight_adjoin_other (F : RootedForest V) {v r : V}
    (hv : v ∉ F.vertices) (hrv : r ≠ v) :
    (F.adjoin v hv).componentHeight r = F.componentHeight r := by
  unfold componentHeight
  rw [componentVertices_adjoin_other F hv hrv]
  apply Finset.sup_congr rfl
  intro w hw
  have hwv : w ≠ v := fun h => hv (h ▸ (Finset.mem_filter.mp hw).1)
  change (if w = v then 0 else F.depth w) = F.depth w
  exact ite_eq_right hwv

theorem componentHeight_adjoin_new (F : RootedForest V) {v : V}
    (hv : v ∉ F.vertices) : (F.adjoin v hv).componentHeight v = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro w hw
  obtain ⟨hw, hr⟩ := Finset.mem_filter.mp hw
  change w ∈ insert v F.vertices at hw
  change (if w = v then v else F.root w) = v at hr
  by_cases hwv : w = v
  · subst w
    change (if v = v then 0 else F.depth v) ≤ 0
    simp
  · have hwold : w ∈ F.vertices := (Finset.mem_insert.mp hw).resolve_left hwv
    have hr' : F.root w = v := by simpa only [ite_eq_right hwv] using hr
    exact False.elim (hv (hr' ▸ F.root_mem w hwold))

end FreezingGrowth.RootedForest

namespace FreezingGrowth.ReverseOrdered

open scoped Classical

theorem heightProfile_insertLabel (F : Forest) (i : ℕ)
    (hfresh : Sum.inr i ∉ F.forest.vertices) :
    heightProfile (insertLabel F i) = heightProfile F ++ [0] := by
  have hf : (insertLabel F i).forest = F.forest.adjoin (.inr i) hfresh := by
    simp only [insertLabel, dite_eq_right hfresh]
  unfold heightProfile
  rw [insertLabel_rootOrder F hfresh, List.map_append, hf]
  have hm : F.rootOrder.map (F.forest.adjoin (.inr i) hfresh).componentHeight =
      F.rootOrder.map F.forest.componentHeight := by
    apply List.map_congr_left
    intro r hr
    apply F.forest.componentHeight_adjoin_other hfresh
    intro he
    exact hfresh (he ▸ (RootedForest.mem_roots.mp ((mem_rootOrder F r).mp hr)).1)
  rw [hm]
  simp only [List.map_cons, List.map_nil, RootedForest.componentHeight_adjoin_new]

theorem heightProfile_initial (x : SignSequence) (n : ℕ) :
    heightProfile (initial x n) = List.replicate (activeCount x n).toNat 0 := by
  have hz : ∀ r, (initial x n).forest.componentHeight r = 0 := by
    intro r
    exact RootedForest.componentHeight_isolated _ _
  have hlen : (initial x n).rootOrder.length = (activeCount x n).toNat :=
    (rootOrder_length _).trans (Reverse.initial_valid x n).roots_card
  have hzero : (initial x n).forest.componentHeight = fun _ => 0 := funext hz
  simp only [heightProfile, hzero, List.map_const', hlen]

end FreezingGrowth.ReverseOrdered
