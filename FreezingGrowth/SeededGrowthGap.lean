module

public import FreezingGrowth.SeededDeletionExpectations
public import FreezingGrowth.RRTSplitResidual
public import FreezingGrowth.SeedComparison

/-! The local mean-height gain from using two different active seed depths. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory

theorem meanGrowth_eq_seed (a b M n : ℕ) (hab : max a b ≤ M) :
    meanGrowth ⟨{a, b}, M⟩ n =
      ∫ p, (seedHeight a b M p : ℝ) ∂RRTSplit.heightPairLaw n :=
  join_seed_mean a b M hab n

/-- The new child's own height is already included in its grafted component. -/
theorem meanGrowth_child_pair (a M n : ℕ) :
    meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n =
      ∫ p, (seedHeight a (a + 1) M p : ℝ) ∂RRTSplit.heightPairLaw n := by
  rw [meanGrowth_eq_seed a (a + 1) (max M (a + 1)) n (by omega)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    have he : seedHeight a (a + 1) (max M (a + 1)) p = seedHeight a (a + 1) M p := by
      unfold seedHeight
      omega
    exact congrArg (fun k : ℕ => (k : ℝ)) he)

theorem meanGrowth_pair_gap_lower (a b M n : ℕ) (hab : max a b ≤ M) :
    |(a : ℝ) - b| / 2 - RRTSplit.roughHeightGap n - 1 -
      RRTSplit.splitDeficitAt n (M : ℝ) ≤
        meanGrowth ⟨{a, b}, M⟩ n -
          (meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
            meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2 := by
  rw [meanGrowth_eq_seed a b M n hab, meanGrowth_child_pair a M n,
    meanGrowth_child_pair b M n]
  let μ := RRTSplit.heightPairLaw n
  let F : ℕ × ℕ → ℝ := fun p => (seedHeight a b M p : ℝ)
  let A : ℕ × ℕ → ℝ := fun p => (seedHeight a (a + 1) M p : ℝ)
  let B : ℕ × ℕ → ℝ := fun p => (seedHeight b (b + 1) M p : ℝ)
  let D : ℕ × ℕ → ℝ := fun p => |(p.1 : ℝ) - p.2|
  let R : ℕ × ℕ → ℝ := fun p => max ((M : ℝ) - (max p.1 p.2 : ℕ)) 0
  let c : ℝ := |(a : ℝ) - b| / 2
  have hi (f : ℕ × ℕ → ℝ) : Integrable f μ := RRTSplit.heightPairLaw_integrable n f
  have hs (f g : ℕ × ℕ → ℝ) : (∫ p, f p - g p ∂μ) = (∫ p, f p ∂μ) - ∫ p, g p ∂μ := by
    simpa only [Pi.sub_apply] using integral_sub (hi f) (hi g)
  have hadd (f g : ℕ × ℕ → ℝ) : (∫ p, f p + g p ∂μ) = (∫ p, f p ∂μ) + ∫ p, g p ∂μ := by
    simpa only [Pi.add_apply] using integral_add (hi f) (hi g)
  have hpoint (p : ℕ × ℕ) : c - D p - 1 - R p ≤ F p - (A p + B p) / 2 := by
    simpa only [c, D, R, F, A, B, seedHeight, Nat.cast_max, Nat.cast_add, Nat.cast_one] using
      seeded_pair_gap_lower (a : ℝ) (b : ℝ) (M : ℝ) (p.1 : ℝ) (p.2 : ℝ)
        (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  have hmono := integral_mono (hi (fun p => c - D p - 1 - R p))
    (hi (fun p => F p - (A p + B p) / 2)) hpoint
  simp only [hs, hadd, integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  exact hmono

end FreezingGrowth.HeightProfile
