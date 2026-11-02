module

public import FreezingGrowth.TaggedTwoSeedHeightModel
public import FreezingGrowth.FloorDeletionGaps

/-! The conditional third freezing case has the source's divergent mean gap. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory Filter

theorem case_two_expected_difference (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ h : ℕ, (h : ℝ) ∂caseHeightLaw m n 2) -
      Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) =
        -freezeAttachExpectedGap m n := by
  rw [caseHeightLaw_two m hm n]
  unfold freezeAttachExpectedGap
  simp only [Word.expectedHeight]
  ring

theorem case_two_expected_difference_floor_tendsto :
    Tendsto (fun n : ℕ =>
      (∫ h : ℕ, (h : ℝ) ∂caseHeightLaw (paperPrefixSize n) n 2) -
        Word.expectedHeight (twoActivePrefix (paperPrefixSize n) ++ List.replicate n true))
      atTop atBot := by
  have hh : Tendsto (fun n : ℕ => -freezeAttachExpectedGap (paperPrefixSize n) n) atTop atBot := by
    simpa only [Function.comp_def] using
      tendsto_neg_atTop_atBot.comp freezeAttachExpectedGap_floor_tendsto
  apply hh.congr'
  filter_upwards [tendsto_paperPrefixSize_atTop.eventually_ge_atTop 1] with n hn
  exact (case_two_expected_difference (paperPrefixSize n) hn n).symm

end FreezingGrowth.TwoSeedCoupling
