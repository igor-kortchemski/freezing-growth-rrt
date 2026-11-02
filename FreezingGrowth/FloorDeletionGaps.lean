module

public import FreezingGrowth.FreezeAttachGap
public import FreezingGrowth.AttachFreezeGap
public import FreezingGrowth.PaperPrefixSize
public import FreezingGrowth.RRTSplitResidualPolynomial

/-! The manuscript's full floor-indexed divergent deletion gaps, rather than
only the polynomial subsequence needed for the Introduction's existential claims. -/

@[expose] public section
namespace FreezingGrowth

open Filter
open scoped Topology

theorem freezeAttachExpectedGap_floor_tendsto :
    Tendsto (fun n : ℕ => freezeAttachExpectedGap (paperPrefixSize n) n) atTop atTop := by
  obtain ⟨C, _, hsplit⟩ := RRTSplit.uniformRoughHeightGap
  obtain ⟨D, _, hres⟩ := RRTSplit.uniformResidualBound_of_pow_nine_le
  have hbase_m : Tendsto (fun m : ℕ =>
      (RRT.expectedDistinctDepthGap m -
        8 * Real.log (1 + Real.log (((m ^ 18 : ℕ) : ℝ) + 1))) / 2 - (C + 1 + D))
      atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(C + 1 + D))
        ((RRT.tendsto_expectedDistinctDepthGap_sub_natPolynomialSuffixLogLog 8 18).atTop_div_const
          (by norm_num : (0 : ℝ) < 2))
  have hbase : Tendsto (fun n : ℕ =>
      (RRT.expectedDistinctDepthGap (paperPrefixSize n) -
        8 * Real.log (1 + Real.log (((paperPrefixSize n ^ 18 : ℕ) : ℝ) + 1))) / 2 -
          (C + 1 + D)) atTop atTop := by
    simpa only [Function.comp_def] using hbase_m.comp tendsto_paperPrefixSize_atTop
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [tendsto_paperPrefixSize_atTop.eventually_ge_atTop 2,
    eventually_le_paperPrefixSize_pow_eighteen] with n hm hn
  have hg := freezeAttachExpectedGap_lower (paperPrefixSize n) (by omega) n
  have hr := hres (paperPrefixSize n) n hm (paperPrefixSize_pow_nine_le n)
  have hs := hsplit n
  have hlog := RRTSplit.loglog_mono hn
  have hmul := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 4)
  linarith

noncomputable def attachFreezeExpectedGap (m n : ℕ) : ℝ :=
  Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) -
    Word.expectedHeight ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true)

theorem attachFreezeExpectedGap_floor_tendsto :
    Tendsto (fun n : ℕ => attachFreezeExpectedGap (paperPrefixSize n) n) atTop atTop := by
  have hbase : Tendsto (fun n : ℕ =>
      (freezeAttachExpectedGap (paperPrefixSize n) n - 2) / 3) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-2) freezeAttachExpectedGap_floor_tendsto).atTop_div_const
        (by norm_num : (0 : ℝ) < 3)
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [tendsto_paperPrefixSize_atTop.eventually_ge_atTop 1] with n hm
  exact attachFreeze_expected_gap_ge (paperPrefixSize n) hm n

/-- The sign convention used in the manuscript's final attachment/freezing limit. -/
theorem attachFreezeExpectedDifference_floor_tendsto :
    Tendsto (fun n : ℕ =>
      Word.expectedHeight ((twoActivePrefix (paperPrefixSize n) ++ [true, false]) ++
        List.replicate n true) -
      Word.expectedHeight (twoActivePrefix (paperPrefixSize n) ++ List.replicate n true))
      atTop atBot := by
  simpa only [Function.comp_def, attachFreezeExpectedGap, neg_sub] using
    tendsto_neg_atTop_atBot.comp attachFreezeExpectedGap_floor_tendsto

end FreezingGrowth
