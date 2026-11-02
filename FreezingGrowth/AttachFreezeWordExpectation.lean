module

public import FreezingGrowth.AttachFreezeSeeds
public import FreezingGrowth.SeededDeletionExpectations

/-! The six-branch attachment/freezing decomposition integrated through the
actual two-survivor prefix and its all-attachment continuation. The two depths
and the old maximum retain their joint law in the original recursive tree. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal

theorem integral_transitionLaw_triple (a b c M : ℕ) (sign : Bool)
    (f : HeightProfile → ℝ) :
    (∫ p, f p ∂transitionLaw ⟨{a, b, c}, M⟩ sign) =
      (f (step ⟨{a, b, c}, M⟩ sign a) + f (step ⟨{a, b, c}, M⟩ sign b) +
        f (step ⟨{a, b, c}, M⟩ sign c)) / 3 := by
  have hi (p : HeightProfile) : Integrable f (Measure.dirac p) := integrable_dirac (by simp)
  rw [transitionLaw_triple, integral_smul_measure,
    integral_add_measure ((hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp [smul_eq_mul, div_eq_mul_inv, mul_add]
  ring

private theorem pair_profile_comm (a b M : ℕ) :
    (⟨{a, b}, M⟩ : HeightProfile) = ⟨{b, a}, M⟩ := by
  congr 1
  exact Multiset.pair_comm _ _

/-- An arbitrary observable has the exact average of the six labelled choices.
Coincident depth profiles still appear with their full multiplicities. -/
theorem integral_attach_freeze_pair (a b M : ℕ) (f : HeightProfile → ℝ) :
    (∫ p, (∫ q, f q ∂transitionLaw p false) ∂transitionLaw ⟨{a, b}, M⟩ true) =
      (f ⟨{a, b}, max M (a + 1)⟩ +
        f ⟨{a + 1, b}, max M (a + 1)⟩ +
        f ⟨{a, a + 1}, max M (a + 1)⟩ +
        f ⟨{a, b}, max M (b + 1)⟩ +
        f ⟨{b, b + 1}, max M (b + 1)⟩ +
        f ⟨{a, b + 1}, max M (b + 1)⟩) / 6 := by
  rw [integral_transitionLaw_pair]
  simp only [step, ↓reduceIte, attach]
  change ((∫ q, f q ∂transitionLaw ⟨{a + 1, a, b}, max M (a + 1)⟩ false) +
    (∫ q, f q ∂transitionLaw ⟨{b + 1, a, b}, max M (b + 1)⟩ false)) / 2 = _
  rw [integral_transitionLaw_triple, integral_transitionLaw_triple]
  simp only [step, Bool.false_eq_true, ↓reduceIte, freeze_triple_first,
    freeze_triple_second, freeze_triple_third]
  rw [pair_profile_comm (a + 1) a (max M (a + 1)),
    pair_profile_comm (b + 1) b (max M (b + 1)),
    pair_profile_comm (b + 1) a (max M (b + 1))]
  ring

/-- The original RRT is averaged only after the exact six-branch continuation;
the actual sampled depths and old maximum are never decoupled. -/
theorem expectedHeight_twoActivePrefix_attach_freeze (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Word.expectedHeight ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true) =
      ∫ s, Forward.activePairHeightMean s
        (fun a b M => (meanGrowth ⟨{a, b}, max M (a + 1)⟩ n +
          meanGrowth ⟨{a + 1, b}, max M (a + 1)⟩ n +
          meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
          meanGrowth ⟨{a, b}, max M (b + 1)⟩ n +
          meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n +
          meanGrowth ⟨{a, b + 1}, max M (b + 1)⟩ n) / 6)
            ∂Forward.treeLaw RRT.allAttach m := by
  rw [expectedHeight_eq_wordLaw, integral_wordLaw_append_replicate,
    show twoActivePrefix m ++ [true, false] =
      (twoActivePrefix m ++ [true]) ++ [false] by simp,
    integral_wordLaw_append_singleton, integral_wordLaw_append_singleton]
  change (∫ p, (∫ q, (∫ r, meanGrowth r n ∂transitionLaw q false)
    ∂transitionLaw p true)
      ∂law (twoActivePrefix m).toSigns (twoActivePrefix m).length) = _
  rw [twoActivePrefix_profile_integral m hm]
  simp_rw [integral_attach_freeze_pair]

end FreezingGrowth.HeightProfile
