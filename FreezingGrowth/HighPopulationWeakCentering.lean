module

public import FreezingGrowth.HighPopulationCentering
public import FreezingGrowth.RRTLowerCenter

/-! The corrected high-population index leaves a divergent gap even for the
weaker regularized center. This is deterministic, not an RRT lower-tail bound. -/

@[expose] public section
namespace FreezingGrowth

open Filter
open scoped Topology

/-- Quantitative margin for every nonnegative logarithmic correction. -/
theorem highPopulation_lowerCenter_gap_lower {c : ℝ} (hc : 0 ≤ c) {n : ℕ}
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hratio : 4 ≤ (n : ℝ) / (3 * Real.log n)) :
    (5 - Real.exp 1 - c) * Real.log (Real.log n) -
        Real.exp 1 * Real.log 6 - c * Real.log 3 ≤
      RRT.lowerCenter c (highPopulationIndex n) - mainThreshold n := by
  obtain ⟨hlower, hupper, htwo⟩ := highPopulationIndex_bounds hlog hratio
  have hn0 : n ≠ 0 := by intro h; norm_num [h] at hlog
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hipos : (0 : ℝ) < highPopulationIndex n := by
    exact_mod_cast (by omega : 0 < highPopulationIndex n)
  have hlo : Real.log (n : ℝ) - Real.log 6 - Real.log (Real.log n) ≤
      Real.log ((highPopulationIndex n : ℝ) + 1) := by
    have hh := Real.log_le_log (div_pos hnr (mul_pos (by norm_num) hlogpos))
      (hlower.trans (show (highPopulationIndex n : ℝ) ≤
        (highPopulationIndex n : ℝ) + 1 by linarith))
    rw [Real.log_div hnr.ne' (ne_of_gt (mul_pos (by norm_num) hlogpos)),
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hlogpos.ne'] at hh
    linarith
  have hln : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (show (n : ℝ) + 1 ≤ 2 * n by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnr.ne'] at hh
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hli : Real.log ((highPopulationIndex n : ℝ) + 1) ≤
      Real.log ((n : ℝ) + 1) := Real.log_le_log (by positivity) (by linarith)
  have harg : 1 + Real.log ((highPopulationIndex n : ℝ) + 1) ≤
      3 * Real.log n := by linarith
  have hll : Real.log (1 + Real.log ((highPopulationIndex n : ℝ) + 1)) ≤
      Real.log 3 + Real.log (Real.log n) := by
    have hh := Real.log_le_log (show 0 < 1 +
        Real.log ((highPopulationIndex n : ℝ) + 1) by
      have := Real.log_nonneg (show (1 : ℝ) ≤
        (highPopulationIndex n : ℝ) + 1 by linarith)
      linarith) harg
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogpos.ne'] at hh
  have he := mul_le_mul_of_nonneg_left hlo (Real.exp_pos 1).le
  have hh := mul_le_mul_of_nonneg_left hll hc
  unfold RRT.lowerCenter mainThreshold
  nlinarith

/-- The exact range of corrections sufficient for the M2 high branch. -/
theorem tendsto_highPopulation_lowerCenter_gap {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c < 5 - Real.exp 1) :
    Tendsto (fun n : ℕ => RRT.lowerCenter c (highPopulationIndex n) - mainThreshold n)
      atTop atTop := by
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hpos : 0 < 5 - Real.exp 1 - c := by linarith
  have hl : Tendsto (fun n : ℕ => (5 - Real.exp 1 - c) *
      Real.log (Real.log n) - Real.exp 1 * Real.log 6 - c * Real.log 3)
      atTop atTop := by
    have hm := hll.const_mul_atTop hpos
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hm.eventually_ge_atTop
      (b + Real.exp 1 * Real.log 6 + c * Real.log 3)] with n hn
    linarith
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_log_ge_one, eventually_populationRatio_ge_four] with n hn hr
  exact highPopulation_lowerCenter_gap_lower hc hn hr

/-- The chosen coefficient two leaves the positive margin `3 - e`. -/
theorem tendsto_highPopulation_lowerCenter_two_gap :
    Tendsto (fun n : ℕ => RRT.lowerCenter 2 (highPopulationIndex n) - mainThreshold n)
      atTop atTop :=
  tendsto_highPopulation_lowerCenter_gap (by norm_num)
    (by have := Real.exp_one_lt_three; linarith)

end FreezingGrowth
