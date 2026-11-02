module

public import FreezingGrowth.RRTSharpHeight
public import FreezingGrowth.HighPopulationCentering

/-! The source's sharp mean expansion at the corrected population cutoff.
The cutoff counts active vertices; its recursive tree has one fewer edge. -/

@[expose] public section
namespace FreezingGrowth

open Filter
open scoped Topology

theorem highPopulation_mean_bounded_error :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |RRT.meanHeight (highPopulationIndex n) - rrtHeightCenter (highPopulationIndex n)| ≤ B := by
  obtain ⟨B, hB, hh⟩ := RRT.sourceMeanHeightExpansion
  refine ⟨B, hB, ?_⟩
  filter_upwards [tendsto_highPopulationIndex.eventually_ge_atTop 2] with n hn
  simpa only [rrtHeightCenter, RRT.sourceHeightCenter] using hh (highPopulationIndex n) hn

theorem tendsto_highPopulation_mean_gap :
    Tendsto (fun n : ℕ => RRT.meanHeight (highPopulationIndex n) - mainThreshold n)
      atTop atTop := by
  obtain ⟨B, _, hh⟩ := highPopulation_mean_bounded_error
  have hl : Tendsto (fun n : ℕ =>
      (rrtHeightCenter (highPopulationIndex n) - mainThreshold n) - B) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-B)
      tendsto_highPopulation_center_gap
  apply tendsto_atTop_mono' _ _ hl
  filter_upwards [hh] with n hn
  have he := (abs_le.mp hn).1
  linarith

/-- The displayed source expansion, with the corrected edge count. -/
theorem highPopulation_mean_log_ratio_expansion :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |(RRT.meanHeight (highPopulationIndex n) - Real.exp 1 * Real.log n) -
        (Real.exp 1 * Real.log ((highPopulationIndex n : ℝ) / n) -
          (3 / 2) * Real.log (Real.log (highPopulationIndex n : ℝ)))| ≤ B := by
  obtain ⟨B, hB, hh⟩ := highPopulation_mean_bounded_error
  refine ⟨B, hB, ?_⟩
  filter_upwards [hh, tendsto_highPopulationIndex.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with n hn hi hn2
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hipos : (0 : ℝ) < highPopulationIndex n := Nat.cast_pos.mpr (by omega)
  rw [Real.log_div hipos.ne' hnpos.ne']
  unfold rrtHeightCenter at hn
  have he : (RRT.meanHeight (highPopulationIndex n) - Real.exp 1 * Real.log n) -
      (Real.exp 1 * (Real.log (highPopulationIndex n : ℝ) - Real.log n) -
        (3 / 2) * Real.log (Real.log (highPopulationIndex n : ℝ))) =
      RRT.meanHeight (highPopulationIndex n) -
        (Real.exp 1 * Real.log (highPopulationIndex n : ℝ) -
          (3 / 2) * Real.log (Real.log (highPopulationIndex n : ℝ))) := by ring
  rw [he]
  exact hn

end FreezingGrowth
