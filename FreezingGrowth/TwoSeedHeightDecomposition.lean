module

public import FreezingGrowth.TwoSeedHeightMarginals
public import FreezingGrowth.TwoSeedRemainders
public import FreezingGrowth.HeightAlgebra

/-! The exact two maximum decompositions on the genuine joint height model. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

def componentImbalance (z : ModelSample) : ℝ := (z.2.2 : ℝ) - z.2.1

private theorem max_with_residual (M G : ℝ) : max M G = G + max (M - G) 0 := by
  rw [max_comm M G, max_eq_left_add_positivePart G M, max_comm 0 (M - G)]

private theorem long_graft_max (a X Y : ℝ) :
    max (a + 1 + X) (a + Y) = X + a + max 1 (Y - X) := by
  by_cases h : 1 ≤ Y - X
  · rw [max_eq_right (show a + 1 + X ≤ a + Y by linarith), max_eq_right h]
    ring
  · have hh : Y - X ≤ 1 := by linarith
    rw [max_eq_left (show a + Y ≤ a + 1 + X by linarith), max_eq_left hh]
    ring

private theorem baseline_graft_max (a b X Y : ℝ) :
    max (a + X) (b + Y) = X + a + max 0 (b - a + (Y - X)) := by
  rw [max_eq_left_add_positivePart (a + X) (b + Y),
    show (b + Y) - (a + X) = b - a + (Y - X) by ring]
  ring

theorem sourceZ_height_decomposition (z : ModelSample) :
    (longHeight z : ℝ) = (z.2.1 : ℝ) + z.1.1 + max 1 (componentImbalance z) +
      sourceZPositive z := by
  simp only [longHeight, HeightProfile.seedHeight, Nat.cast_max, Nat.cast_add, Nat.cast_one]
  unfold sourceZPositive sourceZ componentImbalance
  rw [max_with_residual, long_graft_max]

theorem sourceHatZ_height_decomposition (z : ModelSample) :
    (baselineHeight z : ℝ) = (z.2.1 : ℝ) + z.1.1 +
      max 0 ((z.1.2.1 : ℝ) - z.1.1 + componentImbalance z) + sourceHatZPositive z := by
  simp only [baselineHeight, HeightProfile.seedHeight, Nat.cast_max, Nat.cast_add]
  unfold sourceHatZPositive sourceHatZ componentImbalance
  rw [max_with_residual, baseline_graft_max]

theorem source_decompositions_joint (z : ModelSample) :
    ((longHeight z : ℝ) = (z.2.1 : ℝ) + z.1.1 + max 1 (componentImbalance z) + sourceZPositive z) ∧
      ((baselineHeight z : ℝ) = (z.2.1 : ℝ) + z.1.1 +
        max 0 ((z.1.2.1 : ℝ) - z.1.1 + componentImbalance z) + sourceHatZPositive z) :=
  ⟨sourceZ_height_decomposition z, sourceHatZ_height_decomposition z⟩

end FreezingGrowth.TwoSeedCoupling
