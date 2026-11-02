module

public import FreezingGrowth.PWIT.AllRankCount

/-! Global second-moment assembly for the actual all-rank good-path count.
The probabilistic first and second moment estimates remain visible premises.
No fixed-labelled-path conditional overlap bound is used. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

theorem probability_pos_lower_of_moments {Z : Sample → ℝ}
    (hZm : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z law)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) law)
    {C c : ℝ} (hC : 0 < C) (hfirst : c ≤ ∫ ω, Z ω ∂law)
    (hsecond : (∫ ω, Z ω ^ 2 ∂law) ≤ C * ∫ ω, Z ω ∂law) :
    c / C ≤ law.real {ω | 0 < Z ω} := by
  let E : Set Sample := {ω | 0 < Z ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hZm
  have hI : Integrable (E.indicator (fun _ => (1 : ℝ))) law :=
    (integrable_const (1 : ℝ)).indicator hE
  have hQ : 0 ≤ ∫ ω, Z ω ^ 2 - 2 * C * Z ω +
      C ^ 2 * E.indicator (fun _ => (1 : ℝ)) ω ∂law := by
    apply integral_nonneg
    intro ω
    change (0 : ℝ) ≤ Z ω ^ 2 - 2 * C * Z ω + C ^ 2 * E.indicator (fun _ => (1 : ℝ)) ω
    by_cases hω : ω ∈ E
    · simp only [Set.indicator_of_mem hω, mul_one]
      nlinarith [sq_nonneg (Z ω - C)]
    · have hz : Z ω = 0 := le_antisymm (le_of_not_gt hω) (hZ0 ω)
      simp [Set.indicator_of_notMem hω, hz]
  have hsub : Integrable (fun ω => Z ω ^ 2 - 2 * C * Z ω) law :=
    hZ2.sub (hZi.const_mul (2 * C))
  rw [integral_add hsub (hI.const_mul (C ^ 2)),
    integral_sub hZ2 (hZi.const_mul (2 * C)), integral_const_mul, integral_const_mul,
    integral_indicator_const (μ := law) (1 : ℝ) hE] at hQ
  simp only [smul_eq_mul, mul_one] at hQ
  rw [div_le_iff₀ hC]
  have hmain : C * (∫ ω, Z ω ∂law) ≤ C ^ 2 * law.real E := by linarith
  have hmean : (∫ ω, Z ω ∂law) ≤ C * law.real E := by
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith [hmain]
  simpa only [E, mul_comm] using hfirst.trans hmean

/-- A global bound for the square of the actual count suffices. This theorem
does not assume or claim any conditional estimate at a fixed child rank. -/
theorem reaches_probability_lower_of_allRank_moments (d : ℕ) (a : ℝ) {C c : ℝ}
    (hC : 0 < C) (hfirst : c ≤ ∫ ω, allRankGoodCount (d + 1) a ω ∂law)
    (hZ2 : Integrable (fun ω => allRankGoodCount (d + 1) a ω ^ 2) law)
    (hsecond : (∫ ω, allRankGoodCount (d + 1) a ω ^ 2 ∂law) ≤
      C * ∫ ω, allRankGoodCount (d + 1) a ω ∂law) :
    c / C ≤ law.real (reaches (d + 1) (timeCenter (d + 1))) := by
  have hm : Measurable (allRankGoodCount (d + 1) a) :=
    (measurable_pathEventCount _ (measurableSet_allRankGoodEvent _ _)).ennreal_toReal
  exact (probability_pos_lower_of_moments hm (fun _ => ENNReal.toReal_nonneg)
    (integrable_allRankGoodCount d a) hZ2 hC hfirst hsecond).trans
      (measureReal_mono (allRankGoodCount_pos_subset_reaches _ _))

end FreezingGrowth.PWIT
