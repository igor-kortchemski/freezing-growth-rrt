module

public import FreezingGrowth.SeededPrefixExpectations

/-! Expected heights of the actual two-survivor words and their local deletion
comparisons. The common old maximum remains part of the profile law. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal ProbabilityTheory

noncomputable def meanGrowth (p : HeightProfile) (n : ℕ) : ℝ :=
  ∫ q, (q.maximum : ℝ) ∂grow p n

theorem integral_wordLaw_append_singleton (xs : Word) (sign : Bool)
    (f : HeightProfile → ℝ) :
    (∫ q, f q ∂wordLaw (xs ++ [sign])) =
      ∫ p, (∫ q, f q ∂transitionLaw p sign) ∂wordLaw xs := by
  let K : ProbabilityTheory.Kernel HeightProfile HeightProfile :=
    ⟨fun p => transitionLaw p sign, measurable_from_top⟩
  have hw : wordLaw (xs ++ [sign]) = (wordLaw xs).bind (fun p => transitionLaw p sign) := by
    exact ProfileCompute.profile_law_append_singleton xs sign
  have hi := wordLaw_integrable (xs ++ [sign]) f
  rw [hw] at hi ⊢
  have hi' : Integrable f ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (wordLaw xs)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.const_apply] using hh

theorem integral_transitionLaw_pair (a b M : ℕ) (sign : Bool)
    (f : HeightProfile → ℝ) :
    (∫ p, f p ∂transitionLaw ⟨{a, b}, M⟩ sign) =
      (f (step ⟨{a, b}, M⟩ sign a) + f (step ⟨{a, b}, M⟩ sign b)) / 2 := by
  rw [transitionLaw_pair, integral_smul_measure,
    integral_add_measure (integrable_dirac (by simp)) (integrable_dirac (by simp))]
  simp [smul_eq_mul, div_eq_mul_inv, mul_add]
  ring

theorem integral_transitionLaw_singleton (a M : ℕ) (sign : Bool)
    (f : HeightProfile → ℝ) :
    (∫ p, f p ∂transitionLaw ⟨{a}, M⟩ sign) = f (step ⟨{a}, M⟩ sign a) := by
  rw [transitionLaw_singleton]
  simp

theorem integral_freeze_attach_pair (a b M : ℕ) (f : HeightProfile → ℝ) :
    (∫ p, (∫ q, f q ∂transitionLaw p true) ∂transitionLaw ⟨{a, b}, M⟩ false) =
      (f ⟨{a, a + 1}, max M (a + 1)⟩ +
        f ⟨{b, b + 1}, max M (b + 1)⟩) / 2 := by
  rw [integral_transitionLaw_pair]
  simp only [step, Bool.false_eq_true, ↓reduceIte, freeze_pair_left, freeze_pair_right,
    integral_transitionLaw_singleton, attach_singleton]
  ring

theorem expectedHeight_twoActivePrefix_freeze_attach (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Word.expectedHeight ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true) =
      ∫ s, Forward.activePairHeightMean s
        (fun a b M => (meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
          meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2)
            ∂Forward.treeLaw RRT.allAttach m := by
  rw [expectedHeight_eq_wordLaw, integral_wordLaw_append_replicate,
    show twoActivePrefix m ++ [false, true] =
      (twoActivePrefix m ++ [false]) ++ [true] by simp,
    integral_wordLaw_append_singleton, integral_wordLaw_append_singleton]
  change (∫ p, (∫ q, (∫ r, meanGrowth r n ∂transitionLaw q true)
    ∂transitionLaw p false)
      ∂law (twoActivePrefix m).toSigns (twoActivePrefix m).length) = _
  rw [twoActivePrefix_profile_integral m hm]
  simp_rw [integral_freeze_attach_pair]

end FreezingGrowth.HeightProfile
