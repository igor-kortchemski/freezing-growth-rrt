module

public import FreezingGrowth.RRTLowerCenter
public import FreezingGrowth.RRTSplitCDF
public import FreezingGrowth.SplitContraction
import Mathlib.Tactic.Ring

/-! A constant-probability seed implies a geometric lower tail for the actual
RRT height laws. This module proves an implication, not the seed estimate. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory
open scoped Classical

noncomputable def lowerTail (n : ℕ) (t : ℝ) : ℝ :=
  (Forward.heightLaw allAttach n).real {h | (h : ℝ) < t}

def SeedAt (c A p : ℝ) : Prop :=
  ∀ n : ℕ, lowerTail n (lowerCenter c n - A) ≤ 1 - p

def ConstantSuccessSeed (c : ℝ) : Prop :=
  ∃ A p : ℝ, 0 ≤ A ∧ 0 < p ∧ p ≤ 1 ∧ SeedAt c A p

theorem lowerTail_nonneg (n : ℕ) (t : ℝ) : 0 ≤ lowerTail n t := measureReal_nonneg

theorem lowerTail_le_one (n : ℕ) (t : ℝ) : lowerTail n t ≤ 1 := measureReal_le_one

theorem lowerTail_mono (n : ℕ) {s t : ℝ} (hst : s ≤ t) :
    lowerTail n s ≤ lowerTail n t :=
  measureReal_mono (fun _ hh => lt_of_lt_of_le hh hst)

/-- Uniformly in size, every further grid step contracts the lower-tail bound. -/
theorem lowerTail_geometric_of_seed {c A p : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hp : 0 < p) (hp1 : p ≤ 1) (hseed : SeedAt c A p) (j n : ℕ) :
    lowerTail n (lowerCenter c n - A - (j : ℝ) * (Real.exp 1 * Real.log 4)) ≤
      (1 - p) * (1 - p / 2) ^ j := by
  let L : ℝ := Real.exp 1 * Real.log 4
  have hL : 0 ≤ L := (mul_pos (Real.exp_pos 1) (Real.log_pos (by norm_num))).le
  have hrho : 0 ≤ 1 - p / 2 := by linarith
  induction j generalizing n with
  | zero => simpa using hseed n
  | succ j ih =>
    let a : ℝ := (1 - p) * (1 - p / 2) ^ j
    have ha : 0 ≤ a := mul_nonneg (by linarith) (pow_nonneg hrho _)
    cases n with
    | zero =>
      have he : {h : ℕ | (h : ℝ) < lowerCenter c 0 - A -
          ((j + 1 : ℕ) : ℝ) * L} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro h hh
        simp only [lowerCenter_zero, Set.mem_ofPred_eq] at hh
        nlinarith [Nat.cast_nonneg (α := ℝ) h,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) (j + 1)) hL]
      change lowerTail 0 (lowerCenter c 0 - A - ((j + 1 : ℕ) : ℝ) * L) ≤ _
      rw [lowerTail, he, measureReal_empty]
      positivity
    | succ n =>
      let t : ℝ := lowerCenter c (n + 1) - A - ((j + 1 : ℕ) : ℝ) * L
      have hcomp (m : ℕ) (hm : m ≤ n + 1)
          (hq : (n + 1 : ℝ) + 1 ≤ 4 * ((m : ℝ) + 1)) :
          lowerTail m t ≤ a ∧ lowerTail m t ≤ 1 - p := by
        have hl := lowerCenter_sub_le_quarter hc hm
          (by simpa only [Nat.cast_add, Nat.cast_one] using hq)
        have ht : t ≤ lowerCenter c m - A - (j : ℝ) * L := by
          dsimp [t, L]
          push_cast
          linarith
        refine ⟨(lowerTail_mono m ht).trans (ih m), ?_⟩
        apply (lowerTail_mono m (ht.trans ?_)).trans (hseed m)
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hL]
      let f : ℕ → ℝ := fun k => lowerTail k t * lowerTail (n - k) (t - 1)
      have hall : ∀ k ∈ Finset.range (n + 1), f k ≤ a := by
        intro k hk
        have hk' := Finset.mem_range.mp hk
        by_cases hlarge : n - k ≤ k
        · have hq : (n + 1 : ℝ) + 1 ≤ 4 * ((k : ℝ) + 1) := by
            exact_mod_cast (show n + 1 + 1 ≤ 4 * (k + 1) by omega)
          exact mul_le_mul (hcomp k (by omega) hq).1
            (lowerTail_le_one _ _) (lowerTail_nonneg _ _) ha |>.trans_eq (mul_one a)
        · have hq : (n + 1 : ℝ) + 1 ≤ 4 * (((n - k : ℕ) : ℝ) + 1) := by
            exact_mod_cast (show n + 1 + 1 ≤ 4 * (n - k + 1) by omega)
          have hb := (lowerTail_mono (n - k) (by linarith : t - 1 ≤ t)).trans
            (hcomp (n - k) (by omega) hq).1
          exact mul_le_mul (lowerTail_le_one _ _) hb (lowerTail_nonneg _ _)
            (by norm_num : (0 : ℝ) ≤ 1) |>.trans_eq (one_mul a)
      have hcentral : ∀ k ∈ RRTSplit.centralSplits (n + 1), f k ≤ a * (1 - p) := by
        intro k hk
        have hh := Finset.mem_filter.mp hk
        have hk' := Finset.mem_range.mp hh.1
        have hq1 : (n + 1 : ℝ) + 1 ≤ 4 * ((k : ℝ) + 1) := by
          exact_mod_cast hh.2.1
        have hq2 : (n + 1 : ℝ) + 1 ≤ 4 * (((n - k : ℕ) : ℝ) + 1) := by
          have hn : n + 1 - k = n - k + 1 := by omega
          rw [hn] at hh
          exact_mod_cast hh.2.2
        have hb := (lowerTail_mono (n - k) (by linarith : t - 1 ≤ t)).trans
          (hcomp (n - k) (by omega) hq2).2
        exact mul_le_mul (hcomp k (by omega) hq1).1 hb (lowerTail_nonneg _ _) ha
      have hbound := RRTSplit.split_average_contraction (by omega : 0 < n + 1)
        ha hp.le f hall hcentral
      change lowerTail (n + 1) t ≤ _
      calc
        lowerTail (n + 1) t = (1 / ((n : ℝ) + 1)) *
            ∑ k ∈ Finset.range (n + 1), f k := RRTSplit.heightLaw_real_lt_succ n t
        _ ≤ a * (1 - p / 2) := by simpa using hbound
        _ = (1 - p) * (1 - p / 2) ^ (j + 1) := by dsimp [a]; rw [pow_succ]; ring

end FreezingGrowth.RRT
