module

public import FreezingGrowth.SeededGrowthGap
public import FreezingGrowth.PairMaximumStatistics
public import FreezingGrowth.RRTDepthGapAsymptotics

/-!
# Divergence of the actual freeze-attach deletion height gain

The local seeded comparison is averaged over actual distinct active vertices
of the same old tree. Its retained maximum stays coupled to their depths. A
bounded old-height residual and a coarse component imbalance suffice for the
diverging gain; no sharp height theorem is assumed.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Classical Topology

noncomputable def freezeAttachExpectedGap (m n : ℕ) : ℝ :=
  Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) -
    Word.expectedHeight ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true)

theorem activePairFreezeAttachGap_lower {m : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt m s) (hcard : 2 ≤ s.active.card) (n : ℕ) :
    RRT.treeDistinctDepthGap s / 2 - RRTSplit.roughHeightGap n - 1 -
      RRTSplit.splitDeficitAt n (Forward.treeHeight s : ℝ) ≤
        Forward.activePairHeightMean s
          (fun a b M => HeightProfile.meanGrowth ⟨{a, b}, M⟩ n) -
        Forward.activePairHeightMean s
          (fun a b M => (HeightProfile.meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
            HeightProfile.meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2) := by
  have hmono := Forward.activePairHeightMean_mono s hcard
    (fun a b M => (1 / 2 : ℝ) * |(a : ℝ) - b| - RRTSplit.roughHeightGap n - 1 -
      RRTSplit.splitDeficitAt n (M : ℝ))
    (fun a b M => HeightProfile.meanGrowth ⟨{a, b}, M⟩ n -
      (HeightProfile.meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
        HeightProfile.meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2)
    (by
      intro u hu v hv _
      have hab : max (s.height u) (s.height v) ≤ Forward.treeHeight s :=
        max_le (Forward.height_le_treeHeight (hs.active_subset hu))
          (Forward.height_le_treeHeight (hs.active_subset hv))
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        HeightProfile.meanGrowth_pair_gap_lower (s.height u) (s.height v)
          (Forward.treeHeight s) n hab)
  simp only [Forward.activePairHeightMean_sub s hcard,
    Forward.activePairHeightMean_const_mul s hcard,
    Forward.activePairHeightMean_const s hcard,
    Forward.activePairHeightMean_depth_gap s hcard] at hmono
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hmono

theorem freezeAttachExpectedGap_lower (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    RRT.expectedDistinctDepthGap m / 2 - RRTSplit.roughHeightGap n - 1 -
      RRTSplit.residual m n ≤ freezeAttachExpectedGap m n := by
  let μ := Forward.treeLaw RRT.allAttach m
  let A : Forward.State → ℝ := fun s => Forward.activePairHeightMean s
    (fun a b M => HeightProfile.meanGrowth ⟨{a, b}, M⟩ n)
  let B : Forward.State → ℝ := fun s => Forward.activePairHeightMean s
    (fun a b M => (HeightProfile.meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
      HeightProfile.meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2)
  let R : Forward.State → ℝ := fun s => RRTSplit.splitDeficitAt n (Forward.treeHeight s : ℝ)
  have hi (f : Forward.State → ℝ) : Integrable f μ :=
    Forward.treeLaw_integrable_state RRT.allAttach m f
  have hsub (f g : Forward.State → ℝ) :
      (∫ s, f s - g s ∂μ) = (∫ s, f s ∂μ) - ∫ s, g s ∂μ := by
    simpa only [Pi.sub_apply] using integral_sub (hi f) (hi g)
  have hpoint : ∀ᵐ s ∂μ,
      RRT.treeDistinctDepthGap s / 2 - RRTSplit.roughHeightGap n - 1 - R s ≤ A s - B s := by
    filter_upwards [Forward.treeLaw_valid RRT.allAttach m,
      Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs hc
    have hcZ : (s.active.card : ℤ) = (m : ℤ) + 1 := by
      simpa only [RRT.activeCount_allAttach] using hc.1
    have hcard : 2 ≤ s.active.card := by omega
    exact activePairFreezeAttachGap_lower hs hcard n
  have hmono := integral_mono_ae
    (hi (fun s => RRT.treeDistinctDepthGap s / 2 - RRTSplit.roughHeightGap n - 1 - R s))
    (hi (fun s => A s - B s)) hpoint
  simp only [hsub, integral_div, integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  have hres : (∫ s, R s ∂μ) = RRTSplit.residual m n :=
    (RRTSplit.residual_eq_treeIntegral_splitDeficitAt m n).symm
  rw [hres] at hmono
  rw [freezeAttachExpectedGap,
    HeightProfile.expectedHeight_twoActivePrefix_grow m hm n,
    HeightProfile.expectedHeight_twoActivePrefix_freeze_attach m hm n]
  exact hmono

/-- The concrete ninth-power suffix gives arbitrarily large actual gains. -/
theorem tendsto_freezeAttachExpectedGap_atTop :
    Tendsto (fun m : ℕ => freezeAttachExpectedGap m (m ^ 9)) atTop atTop := by
  obtain ⟨C, _, hsplit⟩ := RRTSplit.uniformRoughHeightGap
  obtain ⟨D, _, hres⟩ := RRTSplit.uniformResidualBound_pow_nine
  have hbase : Tendsto (fun m : ℕ =>
      (RRT.expectedDistinctDepthGap m -
        8 * Real.log (1 + Real.log (((m ^ 9 : ℕ) : ℝ) + 1))) / 2 - (C + 1 + D))
      atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(C + 1 + D))
        ((RRT.tendsto_expectedDistinctDepthGap_sub_natPolynomialSuffixLogLog 8 9).atTop_div_const
          (by norm_num : (0 : ℝ) < 2))
  apply tendsto_atTop_mono' _ _ hbase
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hg := freezeAttachExpectedGap_lower m (by omega) (m ^ 9)
  have hs := hsplit (m ^ 9)
  have hr := hres m hm
  linarith

theorem exists_freezeAttachExpectedGap_ge (A : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ A ≤ freezeAttachExpectedGap m (m ^ 9) := by
  obtain ⟨m, hm, hA⟩ := ((eventually_ge_atTop 2).and
    (tendsto_freezeAttachExpectedGap_atTop.eventually_ge_atTop A)).exists
  exact ⟨m, hm, hA⟩

end FreezingGrowth
