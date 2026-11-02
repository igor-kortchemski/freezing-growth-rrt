module

public import FreezingGrowth.PWIT.LogBarrierGeometry
public import Mathlib.Algebra.Group.Fin.Basic

/-! Bounds for the short exceptional window of a logarithmic barrier. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem log_one_add_le_two_sqrt {q : ℝ} (hq : 0 ≤ q) :
    Real.log (q + 1) ≤ 2 * Real.sqrt (q + 1) := by
  have hp : 0 < q + 1 := by linarith
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hh
  linarith

/-- A logarithmic exceptional suffix has polynomially bounded length. -/
theorem short_log_window_bound {A c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hsmall : q ≤ 2 * (A + c * Real.log (q + 1))) :
    q ≤ 4 * A + 16 * c ^ 2 + 1 := by
  have hl := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt hq) hc
  have hs := Real.sq_sqrt (show 0 ≤ q + 1 by linarith)
  nlinarith [sq_nonneg (Real.sqrt (q + 1) - 4 * c)]

theorem short_log_window_polynomial {A c q : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hsmall : q ≤ 2 * (A + c * Real.log (q + 1))) :
    q ≤ 21 * (1 + A + c) ^ 2 := by
  have hh := short_log_window_bound hc hq hsmall
  nlinarith [sq_nonneg A, mul_nonneg hA hc]

theorem short_log_window_allowance_bound {A c q : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hsmall : q ≤ 2 * (A + c * Real.log (q + 1))) :
    A + c * Real.log (q + 1) ≤ 11 * (1 + A + c) ^ 2 := by
  let M := 1 + A + c
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hA' : A ≤ M := by dsimp [M]; linarith
  have hc' : c ≤ M := by dsimp [M]; linarith
  have hq' : q ≤ 21 * M ^ 2 := short_log_window_polynomial hA hc hq hsmall
  have hs : Real.sqrt (q + 1) ≤ 5 * M := by
    have hh := Real.sq_sqrt (show 0 ≤ q + 1 by linarith)
    nlinarith [Real.sqrt_nonneg (q + 1), sq_nonneg M]
  have hl := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt hq) hc
  have hm := mul_le_mul_of_nonneg_left hs hc
  have hcM := mul_le_mul_of_nonneg_right hc' (show 0 ≤ M by linarith)
  have hMM : M ≤ M ^ 2 := by nlinarith
  nlinarith

noncomputable def logBarrierAllowance {d : ℕ} [NeZero d]
    (A c : ℝ) (r : Fin d) : ℝ :=
  A + c * Real.log ((min r.val (d - r.val) : ℕ) + 1 : ℝ)

theorem logBarrierAllowance_nonneg {d : ℕ} [NeZero d]
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (r : Fin d) :
    0 ≤ logBarrierAllowance A c r := by
  apply add_nonneg hA
  apply mul_nonneg hc
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ min r.val (d - r.val) + 1 by omega))

theorem logBarrierAllowance_le_factor {d : ℕ} [NeZero d]
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (r : Fin d) :
    1 + logBarrierAllowance A c r ≤
      (1 + A + c) * (1 + Real.log ((min r.val (d - r.val) : ℕ) + 1 : ℝ)) := by
  have hl : 0 ≤ Real.log ((min r.val (d - r.val) : ℕ) + 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ min r.val (d - r.val) + 1 by omega))
  unfold logBarrierAllowance
  nlinarith [mul_nonneg (show 0 ≤ 1 + A by linarith) hl]

theorem logBarrierAllowance_neg {d : ℕ} [NeZero d] (A c : ℝ) (r : Fin d) :
    logBarrierAllowance A c (-r) = logBarrierAllowance A c r := by
  by_cases hr : r = 0
  · simp [hr]
  · have hrp : 0 < r.val := by
      have hh : r.val ≠ 0 := by intro hh; apply hr; exact Fin.ext hh
      omega
    have hn : (-r).val = d - r.val := by
      rw [Fin.val_neg']
      exact Nat.mod_eq_of_lt (by omega)
    unfold logBarrierAllowance
    rw [hn, show d - (d - r.val) = r.val by omega, Nat.min_comm]

theorem logBarrierAllowance_short_suffix {d : ℕ} [NeZero d]
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (r : Fin d)
    (hsmall : ((d - r.val : ℕ) : ℝ) ≤ 2 * logBarrierAllowance A c r) :
    ((d - r.val : ℕ) : ℝ) ≤ 21 * (1 + A + c) ^ 2 := by
  apply short_log_window_polynomial hA hc (Nat.cast_nonneg _)
  apply hsmall.trans
  unfold logBarrierAllowance
  have hh := Real.log_le_log
    (by positivity : (0 : ℝ) < ((min r.val (d - r.val) : ℕ) + 1 : ℝ))
    (show ((min r.val (d - r.val) : ℕ) + 1 : ℝ) ≤ ((d - r.val : ℕ) + 1 : ℝ) by
      exact_mod_cast Nat.add_le_add_right (Nat.min_le_right r.val (d - r.val)) 1)
  nlinarith [mul_le_mul_of_nonneg_left hh hc]

end FreezingGrowth.PWIT
