module

public import FreezingGrowth.HeightMonotonicity
public import FreezingGrowth.FiniteLowProfile
public import FreezingGrowth.TreeCounts

/-! Upper-tail domination implies expected-height domination for the actual
finite tree laws. No admissibility or survival assumption is needed. -/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped ENNReal

/-- The finite tail-sum formula for a bounded natural-valued probability law. -/
theorem integral_natCast_eq_sum_real_tails (μ : Measure ℕ) [IsFiniteMeasure μ]
    (N : ℕ) (hb : ∀ᵐ k ∂μ, k ≤ N) :
    (∫ k : ℕ, (k : ℝ) ∂μ) = ∑ i ∈ Finset.range N, μ.real {k | i + 1 ≤ k} := by
  classical
  calc
    _ = ∫ k : ℕ, ∑ i ∈ Finset.range N,
        ({k : ℕ | i + 1 ≤ k}).indicator (fun _ => (1 : ℝ)) k ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb] with k hk
      have he : (Finset.range N).filter (fun i => i + 1 ≤ k) = Finset.range k := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [Finset.sum_boole, he, Finset.card_range]
    _ = ∑ i ∈ Finset.range N, ∫ k : ℕ,
        ({k : ℕ | i + 1 ≤ k}).indicator (fun _ => (1 : ℝ)) k ∂μ :=
      integral_finsetSum _ (fun _ _ => (integrable_const (1 : ℝ)).indicator (by trivial))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (by trivial)

namespace Word

theorem heightLaw_ae_le_length (xs : Word) : ∀ᵐ k ∂xs.heightLaw, k ≤ xs.length :=
  (Forward.heightLaw_height_le_plusCount xs.toSigns xs.length).mono
    (fun _ hk => hk.trans (plusCount_le _ _))

/-- Domination of every upper tail compares the means of the genuine finite laws. -/
theorem HeightLE.expectedHeight_le {xs ys : Word} (h : HeightLE xs ys) :
    xs.expectedHeight ≤ ys.expectedHeight := by
  let N := xs.length + ys.length
  have hx : ∀ᵐ k ∂xs.heightLaw, k ≤ N :=
    (heightLaw_ae_le_length xs).mono (fun _ hk => hk.trans (by dsimp [N]; omega))
  have hy : ∀ᵐ k ∂ys.heightLaw, k ≤ N :=
    (heightLaw_ae_le_length ys).mono (fun _ hk => hk.trans (by dsimp [N]; omega))
  unfold expectedHeight
  rw [integral_natCast_eq_sum_real_tails xs.heightLaw N hx,
    integral_natCast_eq_sum_real_tails ys.heightLaw N hy]
  apply Finset.sum_le_sum
  intro i _
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (h (i + 1))

/-- Appending any operations cannot lower the expected maximum height. -/
theorem expectedHeight_le_append (xs tail : Word) :
    xs.expectedHeight ≤ (xs ++ tail).expectedHeight :=
  (heightLE_append xs tail).expectedHeight_le

end Word
end FreezingGrowth
