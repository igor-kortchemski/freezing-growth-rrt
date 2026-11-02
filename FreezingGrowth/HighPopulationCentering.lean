module

public import FreezingGrowth.PopulationCutoff

/-!
# Centering in the high-population branch

Reaching `r` active vertices guarantees only `r - 1` attachments before a
first freeze. We use that corrected index throughout. The logarithmic gap
below is deterministic; it does not assume or prove the sharp RRT height law.
-/

@[expose] public section

namespace FreezingGrowth

open Filter
open scoped Topology

/-- The corrected RRT edge count in the high-population comparison. -/
noncomputable def highPopulationIndex (n : ℕ) : ℕ :=
  (populationCutoff n - 1).toNat

/-- The centering used for the sharp RRT height estimate. -/
noncomputable def rrtHeightCenter (n : ℕ) : ℝ :=
  Real.exp 1 * Real.log n - (3 / 2 : ℝ) * Real.log (Real.log n)

/-- The corrected edge count still tends to infinity. -/
theorem tendsto_highPopulationIndex : Tendsto highPopulationIndex atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hb : (0 : ℝ) < 3 * ((b : ℝ) + 2) := by positivity
  have hs : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (n : ℝ) < 1 / (3 * ((b : ℝ) + 2)) :=
    (tendsto_order.mp hlim).2 _ (one_div_pos.mpr hb)
  filter_upwards [hs, eventually_log_ge_one] with n hn hlog
  have hn0 : n ≠ 0 := by intro h; norm_num [h] at hlog
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hp := (div_lt_div_iff₀ hnr hb).mp hn
  have hratio : (b : ℝ) + 2 ≤ (n : ℝ) / (3 * Real.log n) := by
    apply (le_div_iff₀ (by linarith : 0 < 3 * Real.log (n : ℝ))).mpr
    nlinarith
  have hf : (b : ℤ) + 2 ≤ populationCutoff n := Int.le_floor.mpr (by simpa using hratio)
  unfold highPopulationIndex
  omega

theorem eventually_populationRatio_ge_four :
    ∀ᶠ n : ℕ in atTop, 4 ≤ (n : ℝ) / (3 * Real.log n) := by
  have hlim : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hs : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) / (n : ℝ) < 1 / 12 :=
    (tendsto_order.mp hlim).2 (1 / 12) (by norm_num)
  filter_upwards [hs, eventually_log_ge_one] with n hn hlog
  have hn0 : n ≠ 0 := by intro h; norm_num [h] at hlog
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hp := (div_lt_iff₀ hnr).mp hn
  apply (le_div_iff₀ (by linarith : 0 < 3 * Real.log (n : ℝ))).mpr
  nlinarith

/-- Floors and the corrected subtraction lose at most a fixed factor. -/
theorem highPopulationIndex_bounds {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ))
    (hratio : 4 ≤ (n : ℝ) / (3 * Real.log n)) :
    (n : ℝ) / (6 * Real.log n) ≤ (highPopulationIndex n : ℝ) ∧
      (highPopulationIndex n : ℝ) ≤ n ∧ 2 ≤ highPopulationIndex n := by
  have hr : (4 : ℤ) ≤ populationCutoff n := Int.le_floor.mpr (by simpa using hratio)
  have hi : 0 ≤ populationCutoff n - 1 := by omega
  have hcast : (highPopulationIndex n : ℝ) = (populationCutoff n : ℝ) - 1 := by
    have he : (highPopulationIndex n : ℤ) = populationCutoff n - 1 :=
      Int.toNat_of_nonneg hi
    exact_mod_cast he
  have hfloor : (n : ℝ) / (3 * Real.log n) - 1 < (populationCutoff n : ℝ) :=
    Int.sub_one_lt_floor _
  have hupper : (populationCutoff n : ℝ) ≤ (n : ℝ) / (3 * Real.log n) :=
    Int.floor_le _
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hhalf : (n : ℝ) / (6 * Real.log n) = ((n : ℝ) / (3 * Real.log n)) / 2 := by
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hcast, hhalf]
    linarith
  · rw [hcast]
    have hx : (n : ℝ) / (3 * Real.log n) ≤ n := by
      apply (div_le_iff₀ (by linarith : 0 < 3 * Real.log (n : ℝ))).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  · have he : (highPopulationIndex n : ℤ) = populationCutoff n - 1 :=
      Int.toNat_of_nonneg hi
    omega

/-- A quantitative lower bound for the gap between the RRT centering at the
corrected cutoff and the threshold of Theorem 1.2. -/
theorem highPopulation_center_gap_lower {n : ℕ} (hlog : 1 ≤ Real.log (n : ℝ))
    (hratio : 4 ≤ (n : ℝ) / (3 * Real.log n)) :
    (1 / 2 : ℝ) * Real.log (Real.log n) - Real.exp 1 * Real.log 6 ≤
      rrtHeightCenter (highPopulationIndex n) - mainThreshold n := by
  obtain ⟨hlower, hupper, htwo⟩ := highPopulationIndex_bounds hlog hratio
  have hn0 : n ≠ 0 := by intro h; norm_num [h] at hlog
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hipos : (0 : ℝ) < highPopulationIndex n := by exact_mod_cast (by omega : 0 < highPopulationIndex n)
  have hlogi : 0 < Real.log (highPopulationIndex n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < highPopulationIndex n)
  have hlo : Real.log (n : ℝ) - Real.log 6 - Real.log (Real.log n) ≤
      Real.log (highPopulationIndex n : ℝ) := by
    have hh := Real.log_le_log (div_pos hnr (mul_pos (by norm_num) hlogpos)) hlower
    rw [Real.log_div (ne_of_gt hnr) (ne_of_gt (mul_pos (by norm_num) hlogpos)),
      Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) (ne_of_gt hlogpos)] at hh
    linarith
  have hhi := Real.log_le_log hlogi (Real.log_le_log hipos hupper)
  have hepos : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_left hlo hepos.le
  have hll : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hlog
  have hc := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hll
  unfold rrtHeightCenter mainThreshold
  nlinarith

/-- The corrected index preserves the divergent gap needed in both high-value
arguments. Sharp RRT mean and lower-tail estimates are separate obligations. -/
theorem tendsto_highPopulation_center_gap :
    Tendsto (fun n : ℕ => rrtHeightCenter (highPopulationIndex n) - mainThreshold n)
      atTop atTop := by
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.log (Real.log n) -
      Real.exp 1 * Real.log 6) atTop atTop := by
    have hm := hll.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hm.eventually_ge_atTop (b + Real.exp 1 * Real.log 6)] with n hn
    linarith
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [eventually_log_ge_one, eventually_populationRatio_ge_four] with n hn hr
  exact highPopulation_center_gap_lower hn hr

end FreezingGrowth
