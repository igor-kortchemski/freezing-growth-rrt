module

public import FreezingGrowth.PWIT.GlobalSecondMoment

/-!
# An exponential lower tail from the actual constant-success seed

The existing discrete contraction gives an exponential bound at every real
threshold. Its positive rate depends on the proved seed; no specified sharp
rate from the manuscript is asserted here.
-/

@[expose] public section

namespace FreezingGrowth.RRT

noncomputable def lowerTailStep : ℝ := Real.exp 1 * Real.log 4

theorem lowerTailStep_pos : 0 < lowerTailStep :=
  mul_pos (Real.exp_pos _) (Real.log_pos (by norm_num))

noncomputable def lowerTailRate (p : ℝ) : ℝ :=
  -Real.log (1 - p / 2) / lowerTailStep

theorem lowerTailRate_pos {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 < lowerTailRate p := by
  have hρ : 0 < 1 - p / 2 := by linarith
  have hρ1 : 1 - p / 2 < 1 := by linarith
  exact div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) lowerTailStep_pos

theorem lowerTailRate_mul_step (p : ℝ) :
    lowerTailRate p * lowerTailStep = -Real.log (1 - p / 2) := by
  unfold lowerTailRate
  exact div_mul_cancel₀ _ lowerTailStep_pos.ne'

/-- Continuous-threshold form of the discrete lower-tail amplifier. -/
theorem lowerTail_exp_of_seed {c A p : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hp : 0 < p) (hp1 : p ≤ 1) (hs : SeedAt c A p) (n : ℕ) (r : ℝ) :
    lowerTail n r ≤
      Real.exp (lowerTailRate p * (A + lowerTailStep + r - lowerCenter c n)) := by
  let L := lowerTailStep
  let ρ := 1 - p / 2
  let α := lowerTailRate p
  let D := lowerCenter c n - A - r
  have hL : 0 < L := lowerTailStep_pos
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hα : 0 < α := lowerTailRate_pos hp hp1
  have hαL : α * L = -Real.log ρ := lowerTailRate_mul_step p
  by_cases hD : 0 ≤ D
  · let j : ℕ := ⌊D / L⌋₊
    have hjL : (j : ℝ) * L ≤ D :=
      (le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg hD hL.le))
    have hLj : D < ((j : ℝ) + 1) * L :=
      (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (D / L))
    have hr : r ≤ lowerCenter c n - A - (j : ℝ) * L := by
      dsimp [D] at hjL
      linarith
    have hgrid := lowerTail_geometric_of_seed hc hA hp hp1 hs j n
    have hpow : ρ ^ j = Real.exp ((j : ℝ) * Real.log ρ) := by
      rw [Real.exp_nat_mul, Real.exp_log hρ]
    have hexp : (j : ℝ) * Real.log ρ ≤
        α * (A + L + r - lowerCenter c n) := by
      have hmul := mul_le_mul_of_nonneg_left hLj.le hα.le
      have heq : α * (((j : ℝ) + 1) * L) =
          -(j : ℝ) * Real.log ρ + α * L := by
        calc
          _ = (j : ℝ) * (α * L) + α * L := by ring
          _ = _ := by rw [hαL]; ring
      rw [heq] at hmul
      dsimp [D] at hmul
      nlinarith
    calc
      lowerTail n r ≤ lowerTail n (lowerCenter c n - A - (j : ℝ) * L) :=
        lowerTail_mono n hr
      _ ≤ (1 - p) * ρ ^ j := hgrid
      _ ≤ ρ ^ j := mul_le_of_le_one_left (pow_nonneg hρ.le _) (by linarith)
      _ = Real.exp ((j : ℝ) * Real.log ρ) := hpow
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  · have hexp : 0 ≤ α * (A + L + r - lowerCenter c n) := by
      apply mul_nonneg hα.le
      dsimp [D] at hD
      linarith
    exact (lowerTail_le_one n r).trans (Real.one_le_exp_iff.mpr hexp)

/-- An actual uniform exponential bound, with fixed positive rate and fixed
offset, valid for every number of edges and every real threshold. -/
theorem uniformLowerTailExponential :
    ∃ α B : ℝ, 0 < α ∧ 0 ≤ B ∧ ∀ n : ℕ, ∀ r : ℝ,
      lowerTail n r ≤ Real.exp (α * (B + r - lowerCenter 2 n)) := by
  obtain ⟨A, p, hA, hp, hp1, hs⟩ :=
    constantSuccessSeed_of_clockLowerSeed PWIT.clockLowerSeed
  refine ⟨lowerTailRate p, A + lowerTailStep, lowerTailRate_pos hp hp1,
    add_nonneg hA lowerTailStep_pos.le, ?_⟩
  intro n r
  exact lowerTail_exp_of_seed (by norm_num : (0 : ℝ) ≤ 2) hA hp hp1 hs n r

end FreezingGrowth.RRT
