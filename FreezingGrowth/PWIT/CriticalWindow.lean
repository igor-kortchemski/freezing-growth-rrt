module

public import FreezingGrowth.PWIT.TimeCenterEstimates

/-!
# Critical endpoint-window intensity

The positive limit here is a first-moment ingredient, not a success probability.
The division by the generation is the factor supplied by the cyclic lemma.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open Filter
open scoped Topology

theorem tendsto_timeCenter : Tendsto timeCenter atTop atTop := by
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) / Real.exp 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (Real.exp_pos 1)
  apply tendsto_atTop_mono' atTop _ hlin
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  unfold timeCenter
  exact le_add_of_nonneg_right (by positivity)

/-- The Stirling constant, written exponentially to avoid a square-root
normalization convention in the asymptotic arguments. -/
noncomputable def criticalIntensityConstant : ℝ :=
  Real.exp (-Real.log (Real.sqrt Real.pi) - (1 / 2 : ℝ) * Real.log 2)

theorem criticalIntensityConstant_pos : 0 < criticalIntensityConstant := Real.exp_pos _

theorem tendsto_critical_intensity (s : ℝ) :
    Tendsto (fun n : ℕ => (timeCenter n - s) ^ n / ((n.factorial : ℝ) * (n : ℝ)))
      atTop (𝓝 (Real.exp (-Real.exp 1 * s) * criticalIntensityConstant)) := by
  have h := (tendsto_critical_log_intensity s).exp
  simp only [← Real.exp_eq_exp_ℝ] at h
  have he : Real.exp (-Real.exp 1 * s - Real.log (Real.sqrt Real.pi) -
      (1 / 2 : ℝ) * Real.log 2) =
      Real.exp (-Real.exp 1 * s) * criticalIntensityConstant := by
    unfold criticalIntensityConstant
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [tendsto_timeCenter.eventually_gt_atTop s, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact Real.exp_log (by positivity)

/-- Endpoint-window intensity divided by the generation. It becomes the mean
of exactly leading paths after the actual all-rank cyclic identity is applied. -/
noncomputable def leadingWindowIntensity (d : ℕ) : ℝ :=
  ((timeCenter d) ^ d - (timeCenter d - 1) ^ d) / ((d.factorial : ℝ) * (d : ℝ))

theorem tendsto_leadingWindowIntensity :
    Tendsto leadingWindowIntensity atTop
      (𝓝 ((1 - Real.exp (-Real.exp 1)) * criticalIntensityConstant)) := by
  have h := (tendsto_critical_intensity 0).sub (tendsto_critical_intensity 1)
  change Tendsto (fun n : ℕ =>
    ((timeCenter n) ^ n - (timeCenter n - 1) ^ n) / ((n.factorial : ℝ) * (n : ℝ))) _ _
  simpa only [neg_mul, mul_zero, Real.exp_zero, one_mul, mul_one, sub_zero,
    ← sub_div, sub_mul, one_mul] using h

/-- A fixed strictly positive lower bound, uniform over all sufficiently large
generations. No probabilistic second moment is asserted here. -/
theorem eventually_leadingWindowIntensity_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ d : ℕ in atTop, c ≤ leadingWindowIntensity d := by
  let L : ℝ := (1 - Real.exp (-Real.exp 1)) * criticalIntensityConstant
  have hL : 0 < L := by
    have he : Real.exp (-Real.exp 1) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos 1))
    exact mul_pos (sub_pos.mpr he) criticalIntensityConstant_pos
  refine ⟨L / 2, by positivity, ?_⟩
  exact (tendsto_leadingWindowIntensity.eventually_const_lt (by linarith : L / 2 < L)).mono
    fun _ hh => hh.le

end FreezingGrowth.PWIT
