module

public import FreezingGrowth.ProfileWordExpectations
public import FreezingGrowth.TwoSurvivorGap

/-! Actual seeded-profile continuations for the main deletion comparisons. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal

theorem transitionLaw_pair (a b M : ℕ) (sign : Bool) :
    transitionLaw ⟨{a, b}, M⟩ sign = (2 : ℝ≥0∞)⁻¹ •
      (Measure.dirac (step ⟨{a, b}, M⟩ sign a) +
        Measure.dirac (step ⟨{a, b}, M⟩ sign b)) := by
  rw [transitionLaw, ite_eq_right (by simp), ProfileCompute.ofMultiset_eq_inverse_smul,
    Measure.map_smul _ measurable_from_top.aemeasurable]
  simp only [Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]
  norm_num only [Multiset.card_cons, Multiset.card_singleton]
  rw [Measure.map_add _ _ measurable_from_top,
    Measure.map_dirac' measurable_from_top, Measure.map_dirac' measurable_from_top]

theorem transitionLaw_singleton (a M : ℕ) (sign : Bool) :
    transitionLaw ⟨{a}, M⟩ sign = Measure.dirac (step ⟨{a}, M⟩ sign a) := by
  rw [transitionLaw, ite_eq_right (by simp), ProfileCompute.ofMultiset_eq_inverse_smul]
  simp [measurable_from_top]

theorem freeze_pair_left (a b M : ℕ) : freeze ⟨{a, b}, M⟩ a = ⟨{b}, M⟩ := by
  simp [freeze, Multiset.insert_eq_cons]

theorem freeze_pair_right (a b M : ℕ) : freeze ⟨{a, b}, M⟩ b = ⟨{a}, M⟩ := by
  have he : (⟨{a, b}, M⟩ : HeightProfile) = ⟨{b, a}, M⟩ := by
    congr 1
    exact Multiset.pair_comm _ _
  rw [he, freeze_pair_left]

theorem attach_singleton (a M : ℕ) :
    attach ⟨{a}, M⟩ a = ⟨{a, a + 1}, max M (a + 1)⟩ := by
  apply HeightProfile.ext
  · simpa only [attach, Multiset.insert_eq_cons] using Multiset.pair_comm (a + 1) a
  · rfl

theorem freeze_attach_pair_law (a b M : ℕ) :
    (transitionLaw ⟨{a, b}, M⟩ false).bind (fun p => transitionLaw p true) =
      (2 : ℝ≥0∞)⁻¹ •
        (Measure.dirac ⟨{a, a + 1}, max M (a + 1)⟩ +
          Measure.dirac ⟨{b, b + 1}, max M (b + 1)⟩) := by
  rw [transitionLaw_pair, Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.dirac_bind measurable_from_top, Measure.dirac_bind measurable_from_top]
  simp only [step, Bool.false_eq_true, ↓reduceIte, freeze_pair_left, freeze_pair_right,
    transitionLaw_singleton, attach_singleton]
  rw [add_comm]

/-- The old maximum is retained alongside the selected seed and its new child. -/
theorem freeze_attach_pair_grow_law (a b M n : ℕ) :
    ((transitionLaw ⟨{a, b}, M⟩ false).bind (fun p => transitionLaw p true)).bind
      (fun p => grow p n) =
      (2 : ℝ≥0∞)⁻¹ •
        (grow ⟨{a, a + 1}, max M (a + 1)⟩ n +
          grow ⟨{b, b + 1}, max M (b + 1)⟩ n) := by
  rw [freeze_attach_pair_law, Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.dirac_bind measurable_from_top, Measure.dirac_bind measurable_from_top]

theorem expectedHeight_twoActivePrefix_grow (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) =
      ∫ s, Forward.activePairHeightMean s
        (fun a b M => ∫ p, (p.maximum : ℝ) ∂grow ⟨{a, b}, M⟩ n)
          ∂Forward.treeLaw RRT.allAttach m := by
  rw [expectedHeight_eq_wordLaw, integral_wordLaw_append_replicate]
  exact twoActivePrefix_profile_integral m hm _

end FreezingGrowth.HeightProfile
