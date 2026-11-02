module

public import FreezingGrowth.PWIT.SimplexCyclicBarrier
public import FreezingGrowth.PWIT.SimplexTwoBlockPrefix
public import FreezingGrowth.PWIT.LogBarrierBounds
public import FreezingGrowth.PWIT.LogBarrierSeries

/-! Identification of the actual cyclic-barrier terms with the two-block
occupancy events. The uniform degree-fourteen summation is a separate step. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

theorem simplexCenteredBridge_zero {d : ℕ} [NeZero d] (p : Fin d → ℝ) :
    simplexCenteredBridge p 0 = 0 := centeredBridge_zero _

theorem simplexCenteredBridge_minimum_iff {d : ℕ} [NeZero d] (p : Fin d → ℝ) :
    minimumAt (simplexCenteredBridge p) 0 ↔ vectorLeading 0 p := by
  unfold simplexCenteredBridge
  rw [← vectorLeading_zero_iff_minimumAt,
    vectorLeading_smul_iff (Nat.cast_pos.mpr (NeZero.pos d) : (0 : ℝ) < d), zero_div]

theorem simplexCenteredBridge_at_prefix {k q : ℕ} [NeZero (k + q)] (hq : 0 < q)
    (p : Fin (k + q) → ℝ) (hp : totalWait p = 1) :
    simplexCenteredBridge p ⟨k, by omega⟩ = simplexSplitSurplus k q p := by
  unfold simplexCenteredBridge
  rw [centeredBridge_smul]
  change ((k + q : ℕ) : ℝ) *
    (cyclicPrefix p k - (k : ℝ) / (k + q : ℕ) * ∑ i, p i) = _
  rw [cyclicPrefix_eq_vectorPrefix p k (by omega), show (∑ i, p i) = 1 from hp]
  unfold simplexSplitSurplus
  have hN : ((k + q : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem simplex_near_position_probability_eq_occupancy {k q : ℕ} [NeZero (k + q)]
    (_hk : 0 < k) (hq : 0 < q) (L : ℝ) :
    (simplexLaw (k + q)).real
      {p | minimumAt (simplexCenteredBridge p) 0 ∧
        simplexCenteredBridge p ⟨k, by omega⟩ - simplexCenteredBridge p 0 ≤ L} =
      (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) := by
  apply measureReal_congr
  filter_upwards [simplexLaw_ae_nonnegative_sum_one (k + q)] with p hp
  apply propext
  change (minimumAt (simplexCenteredBridge p) 0 ∧
    simplexCenteredBridge p ⟨k, by omega⟩ - simplexCenteredBridge p 0 ≤ L) ↔ _
  rw [simplexCenteredBridge_zero, sub_zero, simplexCenteredBridge_minimum_iff,
    simplexCenteredBridge_at_prefix hq p hp.2]
  change (vectorLeading 0 p ∧ simplexSplitSurplus k q p ≤ L) ↔
    (vectorLeading 0 p ∧ 0 ≤ simplexSplitSurplus k q p ∧ simplexSplitSurplus k q p ≤ L)
  constructor
  · rintro ⟨h, hL⟩
    refine ⟨h, ?_, hL⟩
    have hm := (simplexCenteredBridge_minimum_iff p).mpr h ⟨k, by omega⟩
    rw [simplexCenteredBridge_zero, simplexCenteredBridge_at_prefix hq p hp.2] at hm
    exact hm
  · exact fun h => ⟨h.1, h.2.2⟩

theorem simplex_zero_position_probability {d : ℕ} [NeZero d] {A : ℝ} (hA : 0 ≤ A) :
    (simplexLaw d).real {p | minimumAt (simplexCenteredBridge p) 0 ∧
      simplexCenteredBridge p 0 - simplexCenteredBridge p 0 ≤ A} = 1 / (d : ℝ) := by
  have he : {p : Fin d → ℝ | minimumAt (simplexCenteredBridge p) 0 ∧
      simplexCenteredBridge p 0 - simplexCenteredBridge p 0 ≤ A} =
        {p | vectorLeading 0 p} := by
    ext p
    simp [simplexCenteredBridge_minimum_iff, hA]
  rw [he]
  exact simplexLaw_leading_zero_probability d

end FreezingGrowth.PWIT
