module

public import FreezingGrowth.ReverseHeightKernel
public import FreezingGrowth.ReversePositionPairs
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Grafting and permutations of equal-height components

The counting identities retain repeated component heights. Thus matching the
values at the selected receiver and donor is sufficient for the resulting
height lists to be permutations, even when those heights occur elsewhere.
-/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

open MeasureTheory

/-- A permutation of lists can be realized by a bijection of positions
preserving their values. Equal-valued occurrences remain separate positions. -/
theorem exists_position_equiv {xs ys : List ℕ} (h : xs.Perm ys) :
    ∃ e : Fin xs.length ≃ Fin ys.length, ∀ i, xs.get i = ys.get (e i) := by
  classical
  induction h with
  | nil =>
    exact ⟨Equiv.refl _, fun i => Fin.elim0 i⟩
  | @cons x xs ys h ih =>
    obtain ⟨e, he⟩ := ih
    let e' : Fin (x :: xs).length ≃ Fin (x :: ys).length :=
      ((finSuccEquiv xs.length).trans (Equiv.optionCongr e)).trans
        (finSuccEquiv ys.length).symm
    refine ⟨e', ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e']
    · simpa [e'] using he j
  | swap x y xs =>
    refine ⟨Equiv.swap 0 1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · have h0 : k.succ.succ ≠ (0 : Fin (x :: y :: xs).length) := Fin.succ_ne_zero _
        have h1 : k.succ.succ ≠ (1 : Fin (x :: y :: xs).length) := by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
        rfl
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁
    obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun i => (he₁ i).trans (he₂ (e₁ i))⟩

theorem count_eraseIdx (xs : List ℕ) (i : ℕ) (hi : i < xs.length) (z : ℕ) :
    (xs.eraseIdx i).count z = xs.count z - if xs[i] == z then 1 else 0 := by
  rw [← (List.erase_getElem hi).count_eq z]
  exact List.count_erase

/-- The exact multiplicity update removes one receiver occurrence, inserts
its updated height, then removes the distinct donor occurrence. -/
theorem count_graft (xs : List ℕ) (a b z : ℕ)
    (ha : a < xs.length) (hb : b < xs.length) (hab : a ≠ b) :
    (graft xs a b).count z =
      (xs.count z - (if xs[a] == z then 1 else 0) +
        (if max xs[a] (xs[b] + 1) == z then 1 else 0)) -
          (if xs[b] == z then 1 else 0) := by
  unfold graft
  rw [count_eraseIdx _ b (by simpa using hb), List.count_set ha,
    List.getElem_set_ne hab]
  simp only [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some]

/-- Grafting corresponding positions in two permuted component lists has
the same multiset of resulting heights. -/
theorem graft_perm_of_selected_values {xs ys : List ℕ} (hperm : xs.Perm ys)
    (a b c d : ℕ) (ha : a < xs.length) (hb : b < xs.length)
    (hc : c < ys.length) (hd : d < ys.length) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : xs[a] = ys[c]) (hbd : xs[b] = ys[d]) :
    (graft xs a b).Perm (graft ys c d) := by
  apply List.perm_iff_count.mpr
  intro z
  rw [count_graft xs a b z ha hb hab, count_graft ys c d z hc hd hcd,
    hperm.count_eq z, hac, hbd]

/-- Arbitrary component reordering leaves every eventual maximum-height
law unchanged. The proof transports the actual uniform position-pair law. -/
theorem finishAfter_perm (k : ℕ) {xs ys : List ℕ} (hperm : xs.Perm ys) :
    finishAfter k xs = finishAfter k ys := by
  induction k generalizing xs ys with
  | zero =>
    simp only [finishAfter, List.toFinset_eq_of_perm xs ys hperm]
  | succ k ih =>
    have hlen := hperm.length_eq
    by_cases hx : 2 ≤ xs.length
    · have hy : 2 ≤ ys.length := by omega
      obtain ⟨e, he⟩ := exists_position_equiv hperm
      rw [finishAfter, finishAfter, graftLaw, graftLaw, ite_eq_left hx, ite_eq_left hy,
        Measure.bind_map (measurable_of_countable _).aemeasurable
          measurable_from_top.aemeasurable,
        Measure.bind_map (measurable_of_countable _).aemeasurable
          measurable_from_top.aemeasurable,
        ← map_uniformRootPair_positions e,
        Measure.bind_map (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards [uniformRootPair_ae_offDiag (Finset.range xs.length)] with p hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      have hne : positionMap e p.1 ≠ positionMap e p.2 :=
        fun h => hab (positionMap_injOn e ha hb h)
      have he₁ : xs[p.1] = ys[positionMap e p.1]'(positionMap_lt e ha') := by
        simpa [positionMap, ha'] using he ⟨p.1, ha'⟩
      have he₂ : xs[p.2] = ys[positionMap e p.2]'(positionMap_lt e hb') := by
        simpa [positionMap, hb'] using he ⟨p.2, hb'⟩
      exact ih (graft_perm_of_selected_values hperm p.1 p.2 _ _ ha' hb'
        (positionMap_lt e ha') (positionMap_lt e hb') hab hne he₁ he₂)
    · have hy : ¬2 ≤ ys.length := by omega
      simpa only [finishAfter, graftLaw, ite_eq_right hx, ite_eq_right hy,
        Measure.dirac_bind measurable_from_top] using ih hperm

theorem finishLaw_perm {xs ys : List ℕ} (hperm : xs.Perm ys) :
    finishLaw xs = finishLaw ys := by
  simpa only [finishLaw, hperm.length_eq] using finishAfter_perm (ys.length - 1) hperm

end FreezingGrowth.ReverseHeightList
