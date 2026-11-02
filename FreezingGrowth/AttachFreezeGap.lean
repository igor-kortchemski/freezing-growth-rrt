module

public import FreezingGrowth.AttachFreezeMeanComparison
public import FreezingGrowth.PairMaximumStatistics

/-! Averaging the local attachment/freezing comparison through the actual
recursive-tree prefix, without decorrelating its depths and old maximum. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory

theorem attachFreeze_expected_gap_ge (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) -
      Word.expectedHeight ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true) - 2) / 3 ≤
        Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) -
          Word.expectedHeight ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true) := by
  let B : ℕ → ℕ → ℕ → ℝ := fun a b M => HeightProfile.meanGrowth ⟨{a, b}, M⟩ n
  let F : ℕ → ℕ → ℕ → ℝ := fun a b M => HeightProfile.freezeAttachMean a b M n
  let A : ℕ → ℕ → ℕ → ℝ := fun a b M => HeightProfile.attachFreezeMean a b M n
  let bfun : Forward.State → ℝ := fun s => Forward.activePairHeightMean s B
  let ffun : Forward.State → ℝ := fun s => Forward.activePairHeightMean s F
  let afun : Forward.State → ℝ := fun s => Forward.activePairHeightMean s A
  have hstate : ∀ᵐ s ∂Forward.treeLaw RRT.allAttach m,
      bfun s - ffun s - 2 ≤ 3 * (bfun s - afun s) := by
    filter_upwards [Forward.treeLaw_valid RRT.allAttach m,
      Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs hcounts
    have hcZ : (s.active.card : ℤ) = (m : ℤ) + 1 := by
      simpa only [RRT.activeCount_allAttach] using hcounts.1
    have hc : 2 ≤ s.active.card := by omega
    have hpair := Forward.activePairHeightMean_mono s hc
      (fun a b M => B a b M - F a b M - 2)
      (fun a b M => 3 * (B a b M - A a b M)) (by
        intro u hu v hv _
        have hseed : max (s.height u) (s.height v) ≤ Forward.treeHeight s :=
          max_le (Forward.height_le_treeHeight (hs.active_subset hu))
            (Forward.height_le_treeHeight (hs.active_subset hv))
        have hh := HeightProfile.baseline_sub_attachFreezeMean_ge
          (s.height u) (s.height v) (Forward.treeHeight s) n hseed
        simp only [Multiset.insert_eq_cons] at hh
        dsimp [B, F, A]
        linarith)
    simp only [Forward.activePairHeightMean_sub s hc,
      Forward.activePairHeightMean_const s hc,
      Forward.activePairHeightMean_const_mul s hc] at hpair
    exact hpair
  have hi (f : Forward.State → ℝ) : Integrable f (Forward.treeLaw RRT.allAttach m) :=
    Forward.treeLaw_integrable_state RRT.allAttach m f
  have hsInt (f g : Forward.State → ℝ) :
      (∫ s, f s - g s ∂Forward.treeLaw RRT.allAttach m) =
        (∫ s, f s ∂Forward.treeLaw RRT.allAttach m) -
          ∫ s, g s ∂Forward.treeLaw RRT.allAttach m := by
    simpa only [Pi.sub_apply] using integral_sub (hi f) (hi g)
  have hmono := integral_mono_ae (hi (fun s => bfun s - ffun s - 2))
    (hi (fun s => 3 * (bfun s - afun s))) hstate
  simp only [hsInt, integral_const_mul, integral_const, probReal_univ,
    smul_eq_mul, one_mul] at hmono
  simp only [HeightProfile.expectedHeight_twoActivePrefix_grow m hm n,
    HeightProfile.expectedHeight_twoActivePrefix_freeze_attach m hm n,
    HeightProfile.expectedHeight_twoActivePrefix_attach_freeze m hm n]
  change ((∫ s, bfun s ∂Forward.treeLaw RRT.allAttach m) -
    (∫ s, ffun s ∂Forward.treeLaw RRT.allAttach m) - 2) / 3 ≤
      (∫ s, bfun s ∂Forward.treeLaw RRT.allAttach m) -
        ∫ s, afun s ∂Forward.treeLaw RRT.allAttach m
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
  simpa only [mul_comm] using hmono

end FreezingGrowth
