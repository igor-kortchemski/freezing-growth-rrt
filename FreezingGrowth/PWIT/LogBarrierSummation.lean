module

public import FreezingGrowth.PWIT.LogBarrierSeries
public import Mathlib.Algebra.Order.Floor.Ring

/-! Positive-index logarithmic ballot weights and uniform finite-sum bounds. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open Filter
open scoped Topology Classical

noncomputable def logBallotWeight (P n : ℕ) : ℝ :=
  (1 + Real.log ((n : ℝ) + 1)) ^ P / ((n : ℝ) * Real.sqrt (n : ℝ))

theorem logBallotWeight_nonneg (P n : ℕ) : 0 ≤ logBallotWeight P n := by
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) n; linarith)
  unfold logBallotWeight
  positivity

theorem summable_logBallotWeight (P : ℕ) : Summable (logBallotWeight P) := by
  apply ((summable_log_power_three_halves P).mul_left 4).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hs : Real.sqrt ((n : ℝ) + 1) ≤ 2 * Real.sqrt (n : ℝ) := by
    have ha := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hb := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg ((n : ℝ) + 1)]
  have hden : ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) ≤
      4 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    calc
      _ ≤ (2 * (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hnum : 0 ≤ (1 + Real.log ((n : ℝ) + 1)) ^ P := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (logBallotWeight_nonneg P n)]
  unfold logBallotWeight
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * Real.sqrt (n : ℝ))
    (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))).mpr
  have hh := mul_le_mul_of_nonneg_left hden hnum
  nlinarith

noncomputable def logBallotSum (P : ℕ) : ℝ := 1 + ∑' n : ℕ, logBallotWeight P n

theorem logBallotSum_pos (P : ℕ) : 0 < logBallotSum P := by
  have hh : 0 ≤ ∑' n : ℕ, logBallotWeight P n := tsum_nonneg (logBallotWeight_nonneg P)
  unfold logBallotSum
  linarith

theorem sum_logBallotWeight_le (P : ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, logBallotWeight P n ≤ logBallotSum P := by
  have hh := (summable_logBallotWeight P).sum_le_tsum s
    (fun n _ => logBallotWeight_nonneg P n)
  unfold logBallotSum
  linarith

theorem sum_min_logBallotWeight_le (P d : ℕ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, k ≤ d) :
    ∑ k ∈ s, logBallotWeight P (min k (d - k)) ≤ 2 * logBallotSum P := by
  classical
  have hinj : ∀ a ∈ s, ∀ b ∈ s, d - a = d - b → a = b := by
    intro a ha b hb hab
    have ha' := hs a ha
    have hb' := hs b hb
    omega
  have hright : (∑ k ∈ s, logBallotWeight P (d - k)) ≤ logBallotSum P := by
    rw [← Finset.sum_image hinj]
    exact sum_logBallotWeight_le P _
  calc
    _ ≤ ∑ k ∈ s, (logBallotWeight P k + logBallotWeight P (d - k)) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k ≤ d - k
      · rw [Nat.min_eq_left hk]
        exact le_add_of_nonneg_right (logBallotWeight_nonneg P _)
      · rw [Nat.min_eq_right (by omega : d - k ≤ k)]
        exact le_add_of_nonneg_left (logBallotWeight_nonneg P _)
    _ = (∑ k ∈ s, logBallotWeight P k) + ∑ k ∈ s, logBallotWeight P (d - k) :=
      Finset.sum_add_distrib
    _ ≤ _ := by linarith [sum_logBallotWeight_le P s]

theorem sum_short_suffix_indicators_le (d : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (∑ r : Fin d, if ((d - r.val : ℕ) : ℝ) ≤ B then (1 : ℝ) else 0) ≤ B + 1 := by
  let s : Finset (Fin d) := Finset.univ.filter (fun r => ((d - r.val : ℕ) : ℝ) ≤ B)
  have he : (∑ r : Fin d, if ((d - r.val : ℕ) : ℝ) ≤ B then (1 : ℝ) else 0) =
      (s.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [s, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hinj : Set.InjOn (fun r : Fin d => d - r.val) s := by
    intro a ha b hb hab
    change d - a.val = d - b.val at hab
    apply Fin.ext
    have ha' := a.isLt
    have hb' := b.isLt
    omega
  have hsub : s.image (fun r => d - r.val) ⊆ Finset.Icc 1 (Nat.ceil B) := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have hrB := (Finset.mem_filter.mp hr).2
    have hceil : ((d - r.val : ℕ) : ℝ) ≤ Nat.ceil B := hrB.trans (Nat.le_ceil B)
    exact Finset.mem_Icc.mpr ⟨by have := r.isLt; omega, by exact_mod_cast hceil⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hcard
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  have hcast : (s.card : ℝ) ≤ Nat.ceil B := by exact_mod_cast hcard
  rw [he]
  exact hcast.trans (Nat.ceil_lt_add_one hB).le

end FreezingGrowth.PWIT
