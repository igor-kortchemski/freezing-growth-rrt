module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar height identities

These deterministic identities support the height comparisons in `main.tex`.
They do not establish the random-tree coupling or any distributional identity.

The formula on source line 617 has the wrong subtree height in its `C` term:
when `a > b + 1`, the weighted maximum equals `a`, not `b`. The corrected
pointwise identity and an explicit counterexample are proved below.
-/

@[expose] public section

namespace FreezingGrowth

/-- The maximum identity used in the decomposition preceding equation
`eq:couplingmadeeasy`. -/
theorem max_eq_left_add_positivePart (a b : ℝ) :
    max a b = a + max 0 (b - a) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
    ring
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (sub_nonpos.mpr h')]
    ring

/-- Adding a perturbation changes the positive part by at most its absolute value. -/
theorem positivePart_add_le (x d : ℝ) :
    max 0 (x + d) ≤ max 0 x + |d| := by
  apply max_le
  · exact add_nonneg (le_max_left 0 x) (abs_nonneg d)
  · exact add_le_add (le_max_right 0 x) (le_abs_self d)

/-- The lower half of the perturbation estimate used after `eq:couplingmadeeasy`. -/
theorem positivePart_sub_abs_le (x d : ℝ) :
    max 0 x - |d| ≤ max 0 (x + d) := by
  have h := positivePart_add_le (x + d) (-d)
  have hx : x + d + -d = x := by ring
  rw [hx, abs_neg] at h
  linarith

/-- Both bounds in the paper's positive-part perturbation estimate. -/
theorem positivePart_perturbation_bounds (x d : ℝ) :
    max 0 x - |d| ≤ max 0 (x + d) ∧
      max 0 (x + d) ≤ max 0 x + |d| :=
  ⟨positivePart_sub_abs_le x d, positivePart_add_le x d⟩

/-- The deterministic identity underlying the later use of exchangeability. -/
theorem positiveParts_sum_eq_abs (x : ℝ) :
    max 0 x + max 0 (-x) = |x| := by
  by_cases h : 0 ≤ x
  · simp [max_eq_right h, max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]
  · have hx : x ≤ 0 := le_of_not_ge h
    simp [max_eq_left hx, max_eq_right (neg_nonneg.mpr hx), abs_of_nonpos hx]

/-- The three weighted maxima in the simplified expression for the original
tree's height in the proof of `prop:increaseheight`(iii), before constant corrections. -/
noncomputable def weightedHeightCore (a b : ℕ) : ℝ :=
  (2 / 3 : ℝ) * (max a (b + 1) : ℕ) +
    (1 / 6 : ℝ) * (max a b : ℕ) +
    (1 / 6 : ℝ) * (max a (b + 2) : ℕ)

theorem weightedHeightCore_of_lt (a b : ℕ) (h : a < b + 1) :
    weightedHeightCore a b = (b : ℝ) + 1 := by
  have hab : a ≤ b := by omega
  have hab1 : a ≤ b + 1 := by omega
  have hab2 : a ≤ b + 2 := by omega
  norm_num [weightedHeightCore, max_eq_right hab, max_eq_right hab1,
    max_eq_right hab2] ; ring

theorem weightedHeightCore_of_eq (a b : ℕ) (h : a = b + 1) :
    weightedHeightCore a b = (b : ℝ) + 1 + 1 / 6 := by
  subst a
  have hb : b ≤ b + 1 := by omega
  have hb2 : b + 1 ≤ b + 2 := by omega
  norm_num [weightedHeightCore, max_eq_left hb, max_eq_right hb2] ; ring

/-- In case `C`, the surviving height is the first subtree height `a`. -/
theorem weightedHeightCore_of_gt (a b : ℕ) (h : b + 1 < a) :
    weightedHeightCore a b = (a : ℝ) := by
  have hb : b ≤ a := by omega
  have hb1 : b + 1 ≤ a := by omega
  have hb2 : b + 2 ≤ a := by omega
  norm_num [weightedHeightCore, max_eq_left hb, max_eq_left hb1,
    max_eq_left hb2] ; ring

/-- The corrected `A`, `B`, `C` decomposition; the final branch is `a`, not `b`. -/
theorem weightedHeightCore_cases (a b : ℕ) :
    weightedHeightCore a b =
      if a < b + 1 then (b : ℝ) + 1
      else if a = b + 1 then (b : ℝ) + 1 + 1 / 6
      else (a : ℝ) := by
  by_cases hlt : a < b + 1
  · rw [ite_eq_left hlt]
    exact weightedHeightCore_of_lt a b hlt
  · rw [ite_eq_right hlt]
    by_cases heq : a = b + 1
    · rw [ite_eq_left heq]
      exact weightedHeightCore_of_eq a b heq
    · rw [ite_eq_right heq]
      exact weightedHeightCore_of_gt a b (by omega)

/-- The scalar identity supporting the conclusion immediately after the
incorrect `C`-case expression in the manuscript. -/
theorem weightedHeightCore_eq_height_add_tie (a b : ℕ) :
    weightedHeightCore a b = (max a (b + 1) : ℕ) +
      (if a = b + 1 then (1 / 6 : ℝ) else 0) := by
  rcases lt_trichotomy a (b + 1) with h | h | h
  · rw [weightedHeightCore_of_lt a b h, ite_eq_right (ne_of_lt h),
      max_eq_right (le_of_lt h)]
    norm_num
  · rw [weightedHeightCore_of_eq a b h, ite_eq_left h, h, max_self]
    norm_num
  · rw [weightedHeightCore_of_gt a b h, ite_eq_right (ne_of_gt h),
      max_eq_left (le_of_lt h)]
    simp

/-- A concrete failure of the printed `C`-case height. This is a scalar
counterexample to that displayed identity, not a counterexample to `prop:increaseheight`. -/
theorem printed_C_case_counterexample :
    0 + 1 < (3 : ℕ) ∧ weightedHeightCore 3 0 = 3 ∧
      weightedHeightCore 3 0 ≠ (0 : ℝ) := by
  norm_num [weightedHeightCore]

/-- The five possible initial configurations in the height calculation of
`prop:increaseheight`(iii), with their printed weights. -/
noncomputable def heightMixture (a b : ℕ) : ℝ :=
  (1 / 6 : ℝ) * (max (a + 1) (b + 2) : ℕ) +
    (1 / 6 : ℝ) * (max a (b + 2) : ℕ) +
    (1 / 6 : ℝ) * (max 2 (max a (b + 1)) : ℕ) +
    (1 / 3 : ℝ) * (max a (b + 1) : ℕ) +
    (1 / 6 : ℝ) * (max (a + 1) (b + 1) : ℕ)

/-- The first simplification of the mixture, including the height-one correction. -/
theorem heightMixture_eq_core (a b : ℕ) :
    heightMixture a b = 1 / 3 + weightedHeightCore a b +
      (if max a (b + 1) = 1 then (1 / 6 : ℝ) else 0) := by
  have h1 : max (a + 1) (b + 2) = max a (b + 1) + 1 := by omega
  have h5 : max (a + 1) (b + 1) = max a b + 1 := by omega
  by_cases h : max a (b + 1) = 1
  · norm_num [heightMixture, weightedHeightCore, h1, h5, h] ; ring
  · have hm : 2 ≤ max a (b + 1) := by
      have hb := le_max_right a (b + 1)
      omega
    norm_num [heightMixture, weightedHeightCore, h1, h5, h,
      max_eq_right hm] ; ring

/-- The complete corrected deterministic height identity. Integrating it still
requires the separate random-tree law and coupling arguments from the paper. -/
theorem heightMixture_eq_height_add_corrections (a b : ℕ) :
    heightMixture a b = 1 / 3 + (max a (b + 1) : ℕ) +
      (if a = b + 1 then (1 / 6 : ℝ) else 0) +
      (if max a (b + 1) = 1 then (1 / 6 : ℝ) else 0) := by
  rw [heightMixture_eq_core, weightedHeightCore_eq_height_add_tie]
  ring

end FreezingGrowth
