module

public import FreezingGrowth.RRTSharpHeight
public import FreezingGrowth.RRTSplitRoughGap

/-! Uniform mean increments and the bounded actual split-height imbalance.
The split law is the genuine uniform mixture of two independent RRT laws. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory

namespace RRT

theorem log_one_add_difference_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.log (1 + v) - Real.log (1 + u) ≤ v - u := by
  have hU : 0 < 1 + u := by linarith
  have hV : 0 < 1 + v := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hV hU)
  rw [Real.log_div hV.ne' hU.ne'] at hlog
  have hdiv : (1 + v) / (1 + u) ≤ (v - u) + 1 := by
    apply (div_le_iff₀ hU).mpr
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huv)]
  linarith

theorem critical_lowerCenter_difference {i n : ℕ} (hin : i ≤ n) :
    |lowerCenter (3 / 2) n - lowerCenter (3 / 2) i| ≤
      Real.exp 1 * (Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1)) := by
  have hi : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) i; linarith)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (i : ℝ) + 1)
    (show (i : ℝ) + 1 ≤ (n : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hin 1)
  have hll := RRTSplit.loglog_mono hin
  have hllU := log_one_add_difference_le hi hl
  have he := Real.exp_one_gt_two
  have hm := mul_nonneg (show 0 ≤ Real.exp 1 - 3 / 2 by linarith) (sub_nonneg.mpr hl)
  unfold lowerCenter
  apply abs_le.mpr
  constructor <;> nlinarith

/-- LP2, including the finite initial sizes. -/
theorem meanHeight_logarithmic_increment :
    ∃ C : ℝ, 0 < C ∧ ∀ n i : ℕ, i ≤ n →
      |meanHeight n - meanHeight i| ≤
        C * (Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1)) + C := by
  obtain ⟨B, hB, hb⟩ := uniformCriticalMeanDeviation
  let C := Real.exp 1 + 2 * B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun n i hin => ?_⟩
  have hδ : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1) :=
    sub_nonneg.mpr (Real.log_le_log (by positivity)
      (show (i : ℝ) + 1 ≤ (n : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hin 1))
  have htri := abs_add_le (meanHeight n - lowerCenter (3 / 2) n)
    (lowerCenter (3 / 2) n - meanHeight i)
  have htri' := abs_add_le (lowerCenter (3 / 2) n - lowerCenter (3 / 2) i)
    (lowerCenter (3 / 2) i - meanHeight i)
  rw [sub_add_sub_cancel] at htri htri'
  have hni := critical_lowerCenter_difference hin
  have hbi := hb i
  rw [abs_sub_comm] at hbi
  have hbn := hb n
  have hCe : Real.exp 1 ≤ C := by dsimp [C]; linarith
  have hBC : 2 * B ≤ C := by
    dsimp [C]
    have := Real.exp_pos 1
    linarith
  have hmult := mul_le_mul_of_nonneg_right hCe hδ
  linarith

theorem meanHeight_logarithmic_increment_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ n i : ℕ, i ≤ n →
      |meanHeight n - meanHeight i| ≤
        -C * Real.log (((i : ℝ) + 1) / ((n : ℝ) + 1)) + C := by
  obtain ⟨C, hC, hh⟩ := meanHeight_logarithmic_increment
  refine ⟨C, hC, fun n i hin => ?_⟩
  rw [Real.log_div (by positivity : (i : ℝ) + 1 ≠ 0) (by positivity : (n : ℝ) + 1 ≠ 0)]
  nlinarith [hh n i hin]

theorem integral_abs_sub_larger_critical_center_le {i n : ℕ} (hin : i ≤ n) :
    (∫ h : ℕ, |(h : ℝ) - lowerCenter (3 / 2) n| ∂Forward.heightLaw allAttach i) ≤
      criticalAbsoluteDeviation i + Real.exp 1 *
        (Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1)) := by
  have hp (h : ℕ) : |(h : ℝ) - lowerCenter (3 / 2) n| ≤
      |(h : ℝ) - lowerCenter (3 / 2) i| + Real.exp 1 *
        (Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1)) := by
    have hh := abs_add_le ((h : ℝ) - lowerCenter (3 / 2) i)
      (lowerCenter (3 / 2) i - lowerCenter (3 / 2) n)
    rw [sub_add_sub_cancel] at hh
    have hdiff := critical_lowerCenter_difference hin
    rw [abs_sub_comm] at hdiff
    exact hh.trans (add_le_add le_rfl hdiff)
  calc
    _ ≤ ∫ h : ℕ, |(h : ℝ) - lowerCenter (3 / 2) i| + Real.exp 1 *
        (Real.log ((n : ℝ) + 1) - Real.log ((i : ℝ) + 1)) ∂Forward.heightLaw allAttach i :=
      integral_mono (Forward.heightLaw_integrable allAttach i _)
        ((criticalAbsoluteDeviation_integrable i).add (integrable_const _)) hp
    _ = _ := by
      rw [integral_add (criticalAbsoluteDeviation_integrable i) (integrable_const _), integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl

end RRT

namespace RRTSplit

/-- I6: a bounded first absolute moment of the actual split difference. -/
theorem uniformHeightGap : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, roughHeightGap n ≤ C := by
  obtain ⟨B, hB, hbound⟩ := RRT.uniformCriticalAbsoluteDeviation
  refine ⟨2 * (B + Real.exp 1), by positivity, fun n => ?_⟩
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (∫ h : ℕ, |(h : ℝ) - RRT.lowerCenter (3 / 2) n|
        ∂Forward.heightLaw RRT.allAttach k) ≤
          B + Real.exp 1 * (Real.log ((n : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    exact (RRT.integral_abs_sub_larger_critical_center_le hkn).trans
      (add_le_add (hbound k) le_rfl)
  have hmean : (∫ p : ℕ × ℕ, |(p.1 : ℝ) - RRT.lowerCenter (3 / 2) n|
      ∂heightPairLaw n) ≤ B + Real.exp 1 := by
    rw [integral_heightPairLaw_fst n (fun h : ℕ => |(h : ℝ) - RRT.lowerCenter (3 / 2) n|)]
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.mpr hN.le)).trans
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * B + Real.exp 1 * ((n : ℝ) + 1)) := by
        gcongr
        exact sum_log_defect_le n
      _ = B + Real.exp 1 := by field_simp
  exact (roughHeightGap_le_twice_centered n (RRT.lowerCenter (3 / 2) n)).trans
    (mul_le_mul_of_nonneg_left hmean (by norm_num))

end RRTSplit
end FreezingGrowth
