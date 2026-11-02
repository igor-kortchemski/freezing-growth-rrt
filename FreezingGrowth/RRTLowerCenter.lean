module

public import FreezingGrowth.RRTMeanUpper

/-! Regularized lower centers for the M2 proof. No height estimate is assumed. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory

noncomputable def lowerCenter (c : ℝ) (n : ℕ) : ℝ :=
  Real.exp 1 * Real.log ((n : ℝ) + 1) -
    c * Real.log (1 + Real.log ((n : ℝ) + 1))

@[simp] theorem lowerCenter_zero (c : ℝ) : lowerCenter c 0 = 0 := by
  simp [lowerCenter]

/-- The logarithmic correction improves the loss when passing to a smaller tree. -/
theorem lowerCenter_sub_le_log_ratio {c : ℝ} (hc : 0 ≤ c) {k n : ℕ} (hkn : k ≤ n) :
    lowerCenter c n - lowerCenter c k ≤
      Real.exp 1 * Real.log (((n : ℝ) + 1) / ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hl : Real.log ((k : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hk (by exact_mod_cast Nat.add_le_add_right hkn 1)
  have hll : Real.log (1 + Real.log ((k : ℝ) + 1)) ≤
      Real.log (1 + Real.log ((n : ℝ) + 1)) := by
    apply Real.log_le_log
    · have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      linarith
    · linarith
  rw [Real.log_div hn.ne' hk.ne']
  unfold lowerCenter
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hll)]

/-- A component retaining a quarter of the vertices loses at most `e log 4`. -/
theorem lowerCenter_sub_le_quarter {c : ℝ} (hc : 0 ≤ c) {k n : ℕ}
    (hkn : k ≤ n) (hquarter : (n : ℝ) + 1 ≤ 4 * ((k : ℝ) + 1)) :
    lowerCenter c n - lowerCenter c k ≤ Real.exp 1 * Real.log 4 := by
  apply (lowerCenter_sub_le_log_ratio hc hkn).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  apply Real.log_le_log (by positivity)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr hquarter

noncomputable def lowerDeficit (c : ℝ) (n : ℕ) : ℝ :=
  ∫ h : ℕ, max (lowerCenter c n - (h : ℝ)) 0 ∂Forward.heightLaw allAttach n

theorem lowerDeficit_integrable (c : ℝ) (n : ℕ) :
    Integrable (fun h : ℕ => max (lowerCenter c n - (h : ℝ)) 0)
      (Forward.heightLaw allAttach n) := by
  apply Integrable.mono' (integrable_const (max (lowerCenter c n) 0))
    (measurable_from_top.aestronglyMeasurable)
  filter_upwards [] with h
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le_max (by have := Nat.cast_nonneg (α := ℝ) h; linarith) le_rfl

theorem lowerDeficit_nonneg (c : ℝ) (n : ℕ) : 0 ≤ lowerDeficit c n :=
  integral_nonneg (fun _ => le_max_right _ _)

end FreezingGrowth.RRT
