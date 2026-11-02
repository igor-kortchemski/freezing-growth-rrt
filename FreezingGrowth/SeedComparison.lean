module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Scalar bounds for the seeded-height comparison. The residual maximum is
kept explicitly, including the height of a newly attached frozen child. -/

@[expose] public section
namespace FreezingGrowth

theorem seeded_height_upper (a M X Y : ℝ) (ha : 0 ≤ a) :
    max M (max (a + X) (a + 1 + Y)) ≤
      a + max X Y + 1 + max (M - max X Y) 0 := by
  have hres := le_max_left (M - max X Y) 0
  have hzero := le_max_right (M - max X Y) 0
  apply max_le
  · linarith
  · apply max_le
    · linarith [le_max_left X Y]
    · linarith [le_max_right X Y]

theorem seeded_height_lower (a b M X Y : ℝ) :
    max a b + min X Y ≤ max M (max (a + X) (b + Y)) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact ((add_le_add (le_refl b) (min_le_right X Y)).trans
      (le_max_right _ _)).trans (le_max_right M _)
  · rw [max_eq_left h]
    exact ((add_le_add (le_refl a) (min_le_left X Y)).trans
      (le_max_left _ _)).trans (le_max_right M _)

/-- A pair of different seed depths gains half their gap, up to component
height imbalance, one new edge, and the old-tree residual. -/
theorem seeded_pair_gap_lower (a b M X Y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| / 2 - |X - Y| - 1 - max (M - max X Y) 0 ≤
      max M (max (a + X) (b + Y)) -
        (max M (max (a + X) (a + 1 + Y)) +
          max M (max (b + X) (b + 1 + Y))) / 2 := by
  have hlow := seeded_height_lower a b M X Y
  have hupa := seeded_height_upper a M X Y ha
  have hupb := seeded_height_upper b M X Y hb
  have hab : |a - b| = 2 * max a b - a - b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have hXY : |X - Y| = max X Y - min X Y := by
    simpa only [abs_sub_comm] using (max_sub_min_eq_abs X Y).symm
  rw [hab, hXY]
  linarith

theorem residual_max_le_threshold (M X Y T : ℝ) :
    max (M - max X Y) 0 ≤ max (M - T) 0 + max (T - max X Y) 0 := by
  apply max_le
  · linarith [le_max_left (M - T) 0, le_max_left (T - max X Y) 0]
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

end FreezingGrowth
