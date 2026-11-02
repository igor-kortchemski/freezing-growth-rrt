module

public import FreezingGrowth.PWIT.VectorLeading
public import FreezingGrowth.PWIT.Leading
public import FreezingGrowth.PWIT.SimplexBridge
public import FreezingGrowth.PWIT.RankDensity

/-! Exact reference-simplex leading probability. No conditioning on a null
endpoint is used: positive scaling preserves the zero-allowance barrier. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

theorem rankIncrementMeasure_zero_eq_finiteClockLaw (d : ℕ) :
    rankIncrementMeasure d 0 = finiteClockLaw d := by
  rw [rankIncrementMeasure_eq_withDensity, finiteClockLaw_density]
  congr 1
  funext x
  simp [rankIncrementPDF, totalWait]

theorem finiteClockLaw_leading_zero_probability (d : ℕ) [NeZero d] :
    (finiteClockLaw d).real {x | vectorLeading 0 x} = 1 / (d : ℝ) := by
  have h := integral_rank_leading (d := d) 0 (fun _ => (1 : ℝ)) (integrable_const 1)
  rw [rankIncrementMeasure_zero_eq_finiteClockLaw] at h
  have hset : {x : Fin d → ℝ | minimumAt (centeredBridge x) 0} =
      {x | vectorLeading 0 x} := by
    ext x
    exact (vectorLeading_zero_iff_minimumAt x).symm
  rw [hset, integral_indicator_const (μ := finiteClockLaw d) (1 : ℝ)
    (measurableSet_vectorLeading d 0)] at h
  simp only [integral_const, smul_eq_mul, mul_one] at h
  have hu : (finiteClockLaw d).real Set.univ = 1 := by simp [measureReal_def]
  rw [hu] at h
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne d))).mpr
  simpa only [mul_comm] using h

theorem vectorLeading_normalized_iff {d : ℕ} {x : Fin d → ℝ}
    (hx : 0 < totalWait x) :
    vectorLeading 0 (normalizedSpacings x) ↔ vectorLeading 0 x := by
  have he : normalizedSpacings x = (totalWait x)⁻¹ • x := by
    ext i
    simp [normalizedSpacings, div_eq_mul_inv, mul_comm]
  rw [he, vectorLeading_smul_iff (inv_pos.mpr hx), zero_div]

/-- The cycle lemma for the canonical normalized iid exponential bridge. -/
theorem simplexLaw_leading_zero_probability (d : ℕ) [NeZero d] :
    (simplexLaw d).real {p | vectorLeading 0 p} = 1 / (d : ℝ) := by
  rw [← finiteClockLaw_leading_zero_probability d]
  unfold simplexLaw
  simp only [measureReal_def]
  rw [Measure.map_apply (measurable_normalizedSpacings d) (measurableSet_vectorLeading d 0)]
  congr 1
  apply measure_congr
  filter_upwards [finiteClockLaw_ae_total_pos d] with x hx
  exact propext (vectorLeading_normalized_iff hx)

end FreezingGrowth.PWIT
