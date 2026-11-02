module

public import FreezingGrowth.RRTFirstOrder
public import FreezingGrowth.PaperPrefixSize

/-! The actual mean comparisons used in the source's two threshold inclusions.
The coarse logarithmic-logarithmic error suffices; the sharp E1 expansion is
not used or asserted. Both inclusions concern the same height sample. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Topology

theorem abs_meanHeight_sub_log_succ_le (n : ℕ) :
    |meanHeight n - Real.exp 1 * Real.log ((n : ℝ) + 1)| ≤ roughAbsoluteDeviation n := by
  have he : (∫ h : ℕ, ((h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1))
      ∂Forward.heightLaw allAttach n) =
        meanHeight n - Real.exp 1 * Real.log ((n : ℝ) + 1) := by
    rw [integral_sub (Forward.heightLaw_integrable allAttach n _) (integrable_const _),
      integral_const, Forward.heightLaw_integral]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  rw [← he]
  exact abs_integral_le_integral_abs

theorem paperPrefixSize_log_succ_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((paperPrefixSize n : ℝ) + 1) ≤ (1 / 9 : ℝ) * Real.log (n : ℝ) + Real.log 2 := by
  have hm : 1 ≤ paperPrefixSize n := by
    apply Nat.le_floor
    simpa using Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n)
      (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hmp : (0 : ℝ) < paperPrefixSize n := by exact_mod_cast (by omega : 0 < paperPrefixSize n)
  have hmR : (1 : ℝ) ≤ paperPrefixSize n := by exact_mod_cast hm
  have hp : (paperPrefixSize n : ℝ) ^ 9 ≤ n := by
    exact_mod_cast paperPrefixSize_pow_nine_le n
  have hh := Real.log_le_log (pow_pos hmp 9) hp
  rw [Real.log_pow] at hh
  have hs := Real.log_le_log (by positivity : (0 : ℝ) < (paperPrefixSize n : ℝ) + 1)
    (show (paperPrefixSize n : ℝ) + 1 ≤ (paperPrefixSize n : ℝ) * 2 by linarith)
  rw [Real.log_mul hmp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hs
  push_cast at hh
  linarith

theorem half_log_succ_ge {n : ℕ} (hn : 1 ≤ n) :
    Real.log (n : ℝ) - Real.log 2 ≤ Real.log (((n / 2 : ℕ) : ℝ) + 1) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : n < (n / 2 + 1) * 2 := by omega
  have hc : (n : ℝ) ≤ (((n / 2 : ℕ) : ℝ) + 1) * 2 := by exact_mod_cast hn2.le
  have hh := Real.log_le_log hnp hc
  rw [Real.log_mul (by positivity : (((n / 2 : ℕ) : ℝ) + 1) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)] at hh
  linarith

theorem regularized_loglog_mono {k n : ℕ} (hkn : k ≤ n) :
    Real.log (1 + Real.log ((k : ℝ) + 1)) ≤ Real.log (1 + Real.log ((n : ℝ) + 1)) := by
  apply Real.log_le_log
  · have hh := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) k; linarith)
    linarith
  · have hh := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) + 1)
      (show (k : ℝ) + 1 ≤ (n : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hkn 1)
    linarith

/-- Exact mean margins in the two eventual source event inclusions. -/
theorem eventually_paper_mean_thresholds :
    ∀ᶠ n : ℕ in atTop,
      meanHeight (paperPrefixSize n) ≤ Real.exp 1 / 8 * Real.log (n : ℝ) ∧
      7 * Real.exp 1 / 8 * Real.log (n : ℝ) ≤ meanHeight (n / 2) := by
  obtain ⟨C, _, hrough⟩ := uniformRoughAbsoluteDeviation
  have he := Real.exp_pos (1 : ℝ)
  have hsmall := (tendsto_order.mp (tendsto_rough_error_div_log (C + Real.exp 1 * Real.log 2))).2
    (Real.exp 1 / 72) (by positivity)
  filter_upwards [eventually_ge_atTop 2, hsmall] with n hn hsmall
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have herr := (div_lt_iff₀ hlog).mp hsmall
  have hmn : paperPrefixSize n ≤ n := by
    have hh := paperPrefixSize_pow_nine_le n
    exact (Nat.le_self_pow (by norm_num : (9 : ℕ) ≠ 0) (paperPrefixSize n)).trans hh
  have hhalf : n / 2 ≤ n := Nat.div_le_self _ _
  have hm := (abs_le.mp (abs_meanHeight_sub_log_succ_le (paperPrefixSize n))).2
  have hhalfmean := (abs_le.mp (abs_meanHeight_sub_log_succ_le (n / 2))).1
  have hmrough := (hrough (paperPrefixSize n)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (regularized_loglog_mono hmn)
      (by norm_num : (0 : ℝ) ≤ 2)) C)
  have hhrough := (hrough (n / 2)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (regularized_loglog_mono hhalf)
      (by norm_num : (0 : ℝ) ≤ 2)) C)
  have hmlog := mul_le_mul_of_nonneg_left (paperPrefixSize_log_succ_le (by omega : 1 ≤ n)) he.le
  have hhlog := mul_le_mul_of_nonneg_left (half_log_succ_ge (by omega : 1 ≤ n)) he.le
  constructor <;> nlinarith [mul_nonneg he.le hlog.le]

/-- The lower-component event uses the very same height on both sides. -/
theorem eventually_paper_centered_event_inclusions :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℕ,
      (Real.exp 1 / 2 * Real.log (n : ℝ) ≤ (h : ℝ) →
        3 * Real.exp 1 / 8 * Real.log (n : ℝ) ≤ (h : ℝ) - meanHeight (paperPrefixSize n)) ∧
      ((h : ℝ) ≤ Real.exp 1 / 2 * Real.log (n : ℝ) →
        (h : ℝ) - meanHeight (n / 2) ≤ -(3 * Real.exp 1 / 8 * Real.log (n : ℝ))) := by
  filter_upwards [eventually_paper_mean_thresholds] with n hn
  intro h
  constructor <;> intro hh <;> linarith [hn.1, hn.2]

end FreezingGrowth.RRT
