module

public import FreezingGrowth.RRTNegativeMomentBound
public import Mathlib.Probability.Moments.Basic

/-! The elementary lower tail at the manuscript's threshold 1.1 log n. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def negativeRate : ℝ := Real.log (7 / 3)

theorem negativeRate_pos : 0 < negativeRate := Real.log_pos (by norm_num)

theorem negativeRate_exponent_lt_one : (11 / 10 : ℝ) * negativeRate < 1 := by
  have he : (7 / 3 : ℝ) = 2 * (7 / 6) := by norm_num
  have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 6)
  have hlog : negativeRate ≤ Real.log 2 + 1 / 6 := by
    rw [negativeRate, he, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  linarith [Real.log_two_lt_d9]

theorem mgf_negativeRate_eq (n : ℕ) :
    mgf (fun s => (Forward.treeHeight s : ℝ)) (Forward.treeLaw allAttach n)
      (-negativeRate) = negativeMoment n := by
  have he : Real.exp (-negativeRate) = negativeBase := by
    rw [negativeRate, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num [negativeBase]
  unfold mgf negativeMoment
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  dsimp only
  rw [mul_comm, Real.exp_nat_mul, he]

theorem height_lower_tail_tendsto_zero :
    Tendsto (fun n : ℕ => (Forward.heightLaw allAttach n).real
      {h | (h : ℝ) ≤ (11 / 10 : ℝ) * Real.log (n : ℝ)}) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := negativeMoment_bound
  let d : ℝ := 1 - (11 / 10 : ℝ) * negativeRate
  have hd : 0 < d := sub_pos.mpr negativeRate_exponent_lt_one
  have hlim : Tendsto (fun n : ℕ => C * Real.exp (-d * Real.log (n : ℝ)))
      atTop (𝓝 0) := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h := tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hd hlog)
    have he := Real.tendsto_exp_atBot.comp h
    simpa only [Function.comp_def, neg_mul, mul_zero] using he.const_mul C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : negativeMoment n ≤ C / (n : ℝ) :=
    (hbound n).trans (div_le_div_of_nonneg_left hC.le hnR (by linarith))
  rw [Forward.heightLaw, map_measureReal_apply measurable_from_top (by trivial)]
  calc
    _ ≤ Real.exp (-(-negativeRate) * ((11 / 10 : ℝ) * Real.log (n : ℝ))) *
        mgf (fun s => (Forward.treeHeight s : ℝ)) (Forward.treeLaw allAttach n) (-negativeRate) :=
      measure_le_le_exp_mul_mgf _ (by linarith [negativeRate_pos])
        (Forward.treeLaw_integrable_exp_treeHeight allAttach n (-negativeRate))
    _ ≤ Real.exp (negativeRate * ((11 / 10 : ℝ) * Real.log (n : ℝ))) * (C / n) := by
      rw [mgf_negativeRate_eq]
      simpa only [neg_neg] using mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = C * Real.exp (-d * Real.log (n : ℝ)) := by
      rw [show -d * Real.log (n : ℝ) =
        negativeRate * ((11 / 10 : ℝ) * Real.log (n : ℝ)) - Real.log (n : ℝ) by dsimp [d]; ring,
        Real.exp_sub, Real.exp_log hnR]
      ring

end FreezingGrowth.RRT
