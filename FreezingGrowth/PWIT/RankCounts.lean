module

public import FreezingGrowth.PWIT.PathClocks
public import Mathlib.Data.Nat.Choose.Sum

/-! # Exact finite rank-class cardinalities -/

@[expose] public section

namespace FreezingGrowth.PWIT

open scoped BigOperators

theorem rankClass_succ (d k : ℕ) :
    rankClass (d + 1) k = (Finset.range (k + 1)).biUnion
      (fun i => (rankClass d (k - i)).image (List.cons i)) := by
  classical
  ext v
  cases v with
  | nil => simp [mem_rankClass]
  | cons i v =>
    simp only [mem_rankClass, List.length_cons, List.sum_cons, Nat.add_right_cancel_iff,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, List.cons.injEq]
    constructor
    · rintro ⟨hd, hk⟩
      refine ⟨i, by omega, v, ⟨hd, by omega⟩, rfl, rfl⟩
    · rintro ⟨j, hj, w, ⟨hd, hk⟩, hij, hw⟩
      subst j
      subst w
      exact ⟨hd, by omega⟩

theorem card_rankClass_succ (d k : ℕ) :
    (rankClass (d + 1) k).card = ∑ i ∈ Finset.range (k + 1), (rankClass d (k - i)).card := by
  classical
  rw [rankClass_succ, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.card_image_of_injective _ (by intro v w h; simpa using h)
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hw
    exact hij (List.cons.inj hy).1.symm

@[simp] theorem card_rankClass (d k : ℕ) :
    (rankClass d k).card = Nat.multichoose d k := by
  induction d generalizing k with
  | zero =>
    cases k <;> simp [rankClass]
  | succ d ih =>
    rw [card_rankClass_succ]
    simp_rw [ih]
    have he : (∑ i ∈ Finset.range (k + 1), d.multichoose (k - i)) =
        ∑ i ∈ Finset.range (k + 1), d.multichoose i := by
      simpa using Finset.sum_range_reflect (fun i => d.multichoose i) (k + 1)
    rw [he, Nat.sum_range_multichoose, Nat.multichoose_eq]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.choose_symm_add (a := k) (b := d)).symm

/-- The form appearing in AF13, with positive generation explicit. -/
theorem card_rankClass_choose {d : ℕ} (_hd : 0 < d) (k : ℕ) :
    (rankClass d k).card = (d + k - 1).choose k := by
  rw [card_rankClass, Nat.multichoose_eq]

end FreezingGrowth.PWIT
