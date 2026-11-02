module

public import FreezingGrowth.SeededHeightExpectation
public import FreezingGrowth.HeightAlgebra

/-! The genuine expectation identities for the words in Proposition 1.1(iii). -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

def removalLong (n : ℕ) : Word := [true, true, false] ++ List.replicate n true
def removalShort (n : ℕ) : Word := [true, false] ++ List.replicate n true

theorem removalShort_expectedHeight {n : ℕ} (hn : 1 ≤ n) :
    (removalShort n).expectedHeight = RRT.meanHeight n + 1 / 2 := by
  rw [HeightProfile.expectedHeight_eq_wordLaw, removalShort, HeightProfile.short_word_law,
    integral_smul_measure,
    integral_add_measure (HeightProfile.single_seed_integrable 0 1 (by omega) n)
      (HeightProfile.single_seed_integrable 1 1 (by omega) n),
    HeightProfile.single_seed_mean 0 1 (by omega),
    HeightProfile.single_seed_mean 1 1 (by omega)]
  have h0 : (∫ s, ((max 1 (0 + Forward.treeHeight s) : ℕ) : ℝ)
      ∂Forward.treeLaw RRT.allAttach n) = RRT.meanHeight n := by
    apply integral_congr_ae
    filter_upwards [RRT.treeHeight_pos hn] with s hs
    congr 1
    omega
  have h1 : (∫ s, ((max 1 (1 + Forward.treeHeight s) : ℕ) : ℝ)
      ∂Forward.treeLaw RRT.allAttach n) = 1 + RRT.meanHeight n := by
    simp only [show ∀ k : ℕ, max 1 (1 + k) = 1 + k by intro k; omega,
      Nat.cast_add, Nat.cast_one]
    rw [integral_add (integrable_const _) (Forward.treeLaw_integrable_heightTest
      RRT.allAttach n (fun k => (k : ℝ)))]
    simp [RRT.meanHeight]
  rw [h0, h1]
  norm_num
  ring

theorem heightMixture_eq_seeds (p : ℕ × ℕ) : heightMixture p.1 p.2 =
    (1 / 6 : ℝ) *
      (2 * (HeightProfile.seedHeight 0 1 1 p : ℝ) +
        (HeightProfile.seedHeight 0 1 2 p : ℝ) +
        (HeightProfile.seedHeight 0 2 2 p : ℝ) +
        (HeightProfile.seedHeight 1 1 1 p : ℝ) +
        (HeightProfile.seedHeight 1 2 2 p : ℝ)) := by
  have h01 : HeightProfile.seedHeight 0 1 1 p = max p.1 (p.2 + 1) := by
    simp only [HeightProfile.seedHeight]; omega
  have h012 : HeightProfile.seedHeight 0 1 2 p = max 2 (max p.1 (p.2 + 1)) := by
    simp only [HeightProfile.seedHeight]; omega
  have h02 : HeightProfile.seedHeight 0 2 2 p = max p.1 (p.2 + 2) := by
    simp only [HeightProfile.seedHeight]; omega
  have h11 : HeightProfile.seedHeight 1 1 1 p = max (p.1 + 1) (p.2 + 1) := by
    simp only [HeightProfile.seedHeight]; omega
  have h12 : HeightProfile.seedHeight 1 2 2 p = max (p.1 + 1) (p.2 + 2) := by
    simp only [HeightProfile.seedHeight]; omega
  rw [h01, h012, h02, h11, h12, heightMixture]
  ring

theorem removalLong_expectedHeight_mixture (n : ℕ) :
    (removalLong n).expectedHeight =
      ∫ p, heightMixture p.1 p.2 ∂RRTSplit.heightPairLaw n := by
  have h01 := HeightProfile.join_seed_integrable 0 1 1 (by decide) n
  have h012 := HeightProfile.join_seed_integrable 0 1 2 (by decide) n
  have h02 := HeightProfile.join_seed_integrable 0 2 2 (by decide) n
  have h11 := HeightProfile.join_seed_integrable 1 1 1 (by decide) n
  have h12 := HeightProfile.join_seed_integrable 1 2 2 (by decide) n
  have htwo : Integrable (fun p => (p.maximum : ℝ))
      (2 • HeightProfile.grow ⟨{0, 1}, 1⟩ n) := by
    simpa [two_smul] using h01.add_measure h01
  rw [HeightProfile.expectedHeight_eq_wordLaw, removalLong, HeightProfile.long_word_law,
    integral_smul_measure,
    integral_add_measure (((htwo.add_measure h012).add_measure h02).add_measure h11) h12,
    integral_add_measure ((htwo.add_measure h012).add_measure h02) h11,
    integral_add_measure (htwo.add_measure h012) h02,
    integral_add_measure htwo h012,
    show 2 • HeightProfile.grow ⟨{0, 1}, 1⟩ n =
      HeightProfile.grow ⟨{0, 1}, 1⟩ n + HeightProfile.grow ⟨{0, 1}, 1⟩ n by simp [two_smul],
    integral_add_measure h01 h01]
  rw [HeightProfile.join_seed_mean 0 1 1 (by decide),
    HeightProfile.join_seed_mean 0 1 2 (by decide),
    HeightProfile.join_seed_mean 0 2 2 (by decide),
    HeightProfile.join_seed_mean 1 1 1 (by decide),
    HeightProfile.join_seed_mean 1 2 2 (by decide)]
  simp only [ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  rw [show (∫ p, heightMixture p.1 p.2 ∂RRTSplit.heightPairLaw n) =
    ∫ p, (1 / 6 : ℝ) *
      (2 * (HeightProfile.seedHeight 0 1 1 p : ℝ) +
        (HeightProfile.seedHeight 0 1 2 p : ℝ) +
        (HeightProfile.seedHeight 0 2 2 p : ℝ) +
        (HeightProfile.seedHeight 1 1 1 p : ℝ) +
        (HeightProfile.seedHeight 1 2 2 p : ℝ)) ∂RRTSplit.heightPairLaw n from
      integral_congr_ae (Filter.Eventually.of_forall heightMixture_eq_seeds)]
  rw [integral_const_mul]
  simp only [integral_add (RRTSplit.heightPairLaw_integrable n _) (RRTSplit.heightPairLaw_integrable n _),
    integral_const_mul]
  ring

theorem removalLong_expectedHeight (n : ℕ) :
    (removalLong n).expectedHeight = RRT.meanHeight (n + 1) + 1 / 3 +
      (1 / 6 : ℝ) * (RRTSplit.heightPairLaw n).real {p | p.1 = p.2 + 1} +
      1 / (6 * ((n + 1).factorial : ℝ)) := by
  rw [removalLong_expectedHeight_mixture]
  have hfun : (∫ p, heightMixture p.1 p.2 ∂RRTSplit.heightPairLaw n) =
      ∫ p, (1 / 3 : ℝ) + (max p.1 (p.2 + 1) : ℕ) +
        (if p.1 = p.2 + 1 then (1 / 6 : ℝ) else 0) +
        (if max p.1 (p.2 + 1) = 1 then (1 / 6 : ℝ) else 0)
        ∂RRTSplit.heightPairLaw n :=
    integral_congr_ae (Filter.Eventually.of_forall
      (fun p => heightMixture_eq_height_add_corrections p.1 p.2))
  rw [hfun]
  have hind (P : ℕ × ℕ → Prop) [DecidablePred P] :
      (∫ p, if P p then (1 / 6 : ℝ) else 0 ∂RRTSplit.heightPairLaw n) =
        (1 / 6 : ℝ) * (RRTSplit.heightPairLaw n).real {p | P p} := by
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, smul_eq_mul, mul_comm] using
      integral_indicator_const (μ := RRTSplit.heightPairLaw n) (1 / 6 : ℝ)
        (s := {p | P p}) (Set.to_countable _).measurableSet
  rw [integral_add (RRTSplit.heightPairLaw_integrable n _) (RRTSplit.heightPairLaw_integrable n _),
    integral_add (RRTSplit.heightPairLaw_integrable n _) (RRTSplit.heightPairLaw_integrable n _),
    integral_add (RRTSplit.heightPairLaw_integrable n _) (RRTSplit.heightPairLaw_integrable n _),
    hind, hind]
  have hmax : (∫ p, ((max p.1 (p.2 + 1) : ℕ) : ℝ) ∂RRTSplit.heightPairLaw n) =
      RRT.meanHeight (n + 1) := by
    simpa only [Nat.cast_max, Nat.cast_add, Nat.cast_one] using
      RRTSplit.integral_max_heightPairLaw n
  rw [hmax, RRTSplit.heightPairLaw_height_one]
  simp only [integral_const]
  norm_num
  ring

theorem removal_expectedHeight_comparison {n : ℕ} (hn : 1 ≤ n) :
    (removalLong n).expectedHeight - (removalShort n).expectedHeight ≤
      -1 / 12 + (RRT.meanHeight (n + 1) - RRT.meanHeight n) +
        1 / (6 * ((n + 1).factorial : ℝ)) := by
  rw [removalLong_expectedHeight, removalShort_expectedHeight hn]
  have h := RRTSplit.heightPairLaw_tie_le_half n
  linarith

end FreezingGrowth
