module

public import FreezingGrowth.SeededHeightExpectation
public import FreezingGrowth.ForwardFiniteSupport

/-! Finite-word expectation identities for the actual height-profile law. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped ProbabilityTheory

theorem wordLaw_integrable (xs : Word) (f : HeightProfile → ℝ) :
    Integrable f (wordLaw xs) := by
  rw [wordLaw, ← map_treeLaw]
  apply (integrable_map_measure measurable_from_top.aestronglyMeasurable
    measurable_from_top.aemeasurable).mpr
  exact Forward.treeLaw_integrable_state xs.toSigns xs.length (fun s => f (ofState s))

theorem integral_wordLaw_append_replicate (xs : Word) (n : ℕ) (f : HeightProfile → ℝ) :
    (∫ q, f q ∂wordLaw (xs ++ List.replicate n true)) =
      ∫ p, (∫ q, f q ∂grow p n) ∂wordLaw xs := by
  let K : ProbabilityTheory.Kernel HeightProfile HeightProfile :=
    ⟨fun p => grow p n, measurable_from_top⟩
  have hi := wordLaw_integrable (xs ++ List.replicate n true) f
  rw [wordLaw_append_replicate] at hi ⊢
  have hi' : Integrable f ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (wordLaw xs)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.const_apply] using hh

end FreezingGrowth.HeightProfile
