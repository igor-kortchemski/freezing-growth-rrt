module

public import FreezingGrowth.PWIT.LogBarrierGeometry
public import FreezingGrowth.PWIT.LogBarrierSeries

/-! Uniform depth summation for critical logarithmic first crossings.
The shifted denominator retains the final depth, whose symmetric index is zero. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open scoped Classical

noncomputable def criticalDepthWeight (d j : ℕ) : ℝ :=
  (d : ℝ) ^ (3 * (j : ℝ) / (2 * d)) /
    ((j : ℝ) * Real.sqrt j * (((min j (d - j) : ℕ) : ℝ) + 1) ^ 2)

theorem critical_depth_numerator_le {d j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d) :
    (d : ℝ) ^ (3 * (j : ℝ) / (2 * d)) ≤ 4 * ((j : ℝ) * Real.sqrt j) := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : (0 : ℝ) < j := by linarith
  have hdp : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hchord := log_chord_lower hdp (Nat.cast_nonneg (α := ℝ) j)
    (show (j : ℝ) ≤ d by exact_mod_cast hjd)
  have hlog := Real.log_le_log hdp (show (d : ℝ) ≤ (d : ℝ) + 1 by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog
    (div_nonneg (Nat.cast_nonneg (α := ℝ) j) hdp.le)
  have hrpow : (d : ℝ) ^ (3 * (j : ℝ) / (2 * d)) ≤
      ((j : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hdp, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    apply Real.exp_le_exp.mpr
    have he : Real.log (d : ℝ) * (3 * (j : ℝ) / (2 * d)) =
        (3 / 2) * ((j : ℝ) / d * Real.log d) := by ring
    rw [he]
    linarith
  have he : ((j : ℝ) + 1) ^ (3 / 2 : ℝ) = ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) := by
    symm
    calc
      _ = ((j : ℝ) + 1) ^ (1 : ℝ) * ((j : ℝ) + 1) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add (by positivity : (0 : ℝ) < (j : ℝ) + 1)]; norm_num
  have hs : Real.sqrt ((j : ℝ) + 1) ≤ 2 * Real.sqrt (j : ℝ) := by
    have hh := Real.sqrt_le_sqrt (show (j : ℝ) + 1 ≤ 4 * j by linarith)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    norm_num at hh
    exact hh
  calc
    _ ≤ ((j : ℝ) + 1) * Real.sqrt ((j : ℝ) + 1) := hrpow.trans_eq he
    _ ≤ (2 * (j : ℝ)) * (2 * Real.sqrt j) :=
      mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

theorem criticalDepthWeight_le {d j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d) :
    criticalDepthWeight d j ≤ 4 / ((((min j (d - j) : ℕ) : ℝ) + 1) ^ 2) := by
  have hjp : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
  unfold criticalDepthWeight
  calc
    _ ≤ (4 * ((j : ℝ) * Real.sqrt j)) /
        ((j : ℝ) * Real.sqrt j * (((min j (d - j) : ℕ) : ℝ) + 1) ^ 2) :=
      div_le_div_of_nonneg_right (critical_depth_numerator_le hj hjd) (by positivity)
    _ = _ := by field_simp

noncomputable def shiftedLogBallotWeight (P m : ℕ) : ℝ :=
  (1 + Real.log ((m : ℝ) + 1)) ^ P / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))

theorem shiftedLogBallotWeight_nonneg (P m : ℕ) : 0 ≤ shiftedLogBallotWeight P m := by
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ (m : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  unfold shiftedLogBallotWeight
  positivity

theorem summable_shiftedLogBallotWeight (P : ℕ) : Summable (shiftedLogBallotWeight P) :=
  summable_log_power_three_halves P

noncomputable def shiftedLogBallotSum (P : ℕ) : ℝ :=
  1 + ∑' m : ℕ, shiftedLogBallotWeight P m

theorem shiftedLogBallotSum_pos (P : ℕ) : 0 < shiftedLogBallotSum P := by
  have hh : (0 : ℝ) ≤ ∑' m : ℕ, shiftedLogBallotWeight P m :=
    tsum_nonneg (shiftedLogBallotWeight_nonneg P)
  unfold shiftedLogBallotSum
  linarith

theorem sum_shiftedLogBallotWeight_le (P : ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, shiftedLogBallotWeight P m ≤ shiftedLogBallotSum P := by
  have hh := (summable_shiftedLogBallotWeight P).sum_le_tsum s
    (fun m _ => shiftedLogBallotWeight_nonneg P m)
  unfold shiftedLogBallotSum
  linarith

theorem sum_min_shiftedLogBallotWeight_le (P d : ℕ) (s : Finset ℕ)
    (hs : ∀ j ∈ s, j ≤ d) :
    ∑ j ∈ s, shiftedLogBallotWeight P (min j (d - j)) ≤ 2 * shiftedLogBallotSum P := by
  have hinj : ∀ a ∈ s, ∀ b ∈ s, d - a = d - b → a = b := by
    intro a ha b hb hab
    have ha' := hs a ha
    have hb' := hs b hb
    omega
  have hright : (∑ j ∈ s, shiftedLogBallotWeight P (d - j)) ≤ shiftedLogBallotSum P := by
    rw [← Finset.sum_image hinj]
    exact sum_shiftedLogBallotWeight_le P _
  calc
    _ ≤ ∑ j ∈ s, (shiftedLogBallotWeight P j + shiftedLogBallotWeight P (d - j)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hh : j ≤ d - j
      · rw [Nat.min_eq_left hh]
        exact le_add_of_nonneg_right (shiftedLogBallotWeight_nonneg P _)
      · rw [Nat.min_eq_right (by omega : d - j ≤ j)]
        exact le_add_of_nonneg_left (shiftedLogBallotWeight_nonneg P _)
    _ = (∑ j ∈ s, shiftedLogBallotWeight P j) + ∑ j ∈ s, shiftedLogBallotWeight P (d - j) :=
      Finset.sum_add_distrib
    _ ≤ _ := by linarith [sum_shiftedLogBallotWeight_le P s]

theorem criticalDepthWeight_log_power_le (P : ℕ) {d j : ℕ}
    (hj : 1 ≤ j) (hjd : j ≤ d) :
    criticalDepthWeight d j * (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ P ≤
      4 * shiftedLogBallotWeight P (min j (d - j)) := by
  let m := min j (d - j)
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hl : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg hm
  have hnum : 0 ≤ (1 + Real.log ((m : ℝ) + 1)) ^ P := by positivity
  have hs : Real.sqrt ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
    nlinarith [Real.sqrt_nonneg ((m : ℝ) + 1)]
  have hden : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)]
  have hh := div_le_div_of_nonneg_left hnum
    (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) hden
  calc
    _ ≤ (4 / (((m : ℝ) + 1) ^ 2)) * (1 + Real.log ((m : ℝ) + 1)) ^ P :=
      mul_le_mul_of_nonneg_right (criticalDepthWeight_le hj hjd) hnum
    _ = 4 * ((1 + Real.log ((m : ℝ) + 1)) ^ P / (((m : ℝ) + 1) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)

/-- Uniform summation, including the final crossing depth `j=d`. -/
theorem sum_criticalDepthWeight_log_power_le (P d : ℕ) :
    (∑ j ∈ Finset.Icc 1 d, criticalDepthWeight d j *
      (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ P) ≤ 8 * shiftedLogBallotSum P := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 d, 4 * shiftedLogBallotWeight P (min j (d - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact criticalDepthWeight_log_power_le P (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
    _ = 4 * ∑ j ∈ Finset.Icc 1 d, shiftedLogBallotWeight P (min j (d - j)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * (2 * shiftedLogBallotSum P) := mul_le_mul_of_nonneg_left
      (sum_min_shiftedLogBallotWeight_le P d (Finset.Icc 1 d) (fun _ h => (Finset.mem_Icc.mp h).2))
      (by norm_num)
    _ = _ := by ring

end FreezingGrowth.PWIT
