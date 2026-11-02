module

public import FreezingGrowth.PWIT.HeightRenewal

/-! The zero-height boundary of the actual clock model. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory

/-- The first child is the earliest possible non-root birth, almost surely. -/
theorem reaches_one_ae (t : ℝ) :
    reaches 1 t =ᵐ[law] {ω | firstClock ω ≤ t} := by
  filter_upwards [ae_all_clocks_pos] with ω hω
  change (ω ∈ reaches (0 + 1) t) = (firstClock ω ≤ t)
  apply propext
  rw [reaches_succ_firstBirth]
  constructor
  · rintro (⟨v, hv, hb⟩ | ⟨v, hv, hb⟩)
    · have hn := birth_nonneg (fun c => (hω (leftIndex c)).le) v
      change 0 ≤ birth (leftSample ω) v at hn
      linarith
    · have hv' : v = [] := List.length_eq_zero_iff.mp hv
      subst v
      simp only [birth_nil] at hb
      linarith
  · intro ht
    right
    exact ⟨[], rfl, by simp only [birth_nil]; linarith⟩

/-- Probability of no non-root birth by time t. -/
theorem heightCDF_zero_height {t : ℝ} (ht : 0 ≤ t) : heightCDF 0 t = Real.exp (-t) := by
  have he : law.real (reaches 1 t) = clockLaw.real (Set.Iic t) := by
    rw [← map_firstClock, map_measureReal_apply measurable_firstClock measurableSet_Iic]
    exact measureReal_congr (reaches_one_ae t)
  rw [heightCDF, measureReal_compl (measurableSet_reaches 1 t), probReal_univ, he,
    ← cdf_eq_real]
  simp [clockLaw, cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1), ht]

end FreezingGrowth.PWIT
