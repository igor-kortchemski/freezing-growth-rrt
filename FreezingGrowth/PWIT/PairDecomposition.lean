module

public import FreezingGrowth.PWIT.PairCount

/-! Evaluating the actual common-ancestor identity on finite-dimensional events.
The diagonal and distinct root branches are kept explicit, including infinities. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical ENNReal

theorem map_extendedGenerationIntensity_restrict (d : ℕ) :
    (extendedGenerationIntensity d).map (restrictSequence d) = positiveOrthantVolume d := by
  unfold extendedGenerationIntensity
  rw [Measure.map_map (measurable_restrictSequence d) (measurable_extendVector d)]
  have he : restrictSequence d ∘ extendVector = id := by
    funext x
    exact restrict_extendVector x
  rw [he, Measure.map_id]

theorem extendedGenerationIntensity_preimage (d : ℕ) {E : Set (Fin d → ℝ)}
    (hE : MeasurableSet E) :
    extendedGenerationIntensity d ((restrictSequence d) ⁻¹' E) = generationIncrementIntensity d E := by
  rw [← Measure.map_apply (measurable_restrictSequence d) hE,
    map_extendedGenerationIntensity_restrict, generationIncrementIntensity_eq]

theorem generationPairIntensity_event_decomposition (d : ℕ) {E : Set (Fin d → ℝ)}
    (hE : MeasurableSet E) :
    generationPairIntensity d (E ×ˢ E) = generationIncrementIntensity d E +
      ∑ j ∈ Finset.range d, extendedOverlapIntensity j (d - j)
        (((restrictSequence d) ⁻¹' E) ×ˢ ((restrictSequence d) ⁻¹' E)) := by
  let F := (restrictSequence d) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage (measurable_restrictSequence d)
  have hp : (restrictSequencePair d) ⁻¹' (E ×ˢ E) = F ×ˢ F := by
    ext p
    simp [restrictSequencePair, F]
  rw [← map_extendedGenerationPairIntensity_restrict d,
    Measure.map_apply (measurable_restrictSequencePair d) (hE.prod hE), hp,
    extendedGenerationPairIntensity_manyToTwo, Measure.add_apply,
    Measure.finsetSum_apply,
    Measure.map_apply (by fun_prop) (hF.prod hF)]
  have hdiag : (fun x : IncrementSequence => (x, x)) ⁻¹' (F ×ˢ F) = F := by
    ext x
    simp
  rw [hdiag, extendedGenerationIntensity_preimage d hE]

theorem generationPairIntensity_event_decomposition_pos {d : ℕ} (hd : 0 < d)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    generationPairIntensity d (E ×ˢ E) = generationIncrementIntensity d E +
      (generationIncrementIntensity d E) ^ 2 +
      ∑ j ∈ Finset.Icc 1 (d - 1), extendedOverlapIntensity j (d - j)
        (((restrictSequence d) ⁻¹' E) ×ˢ ((restrictSequence d) ⁻¹' E)) := by
  rw [generationPairIntensity_event_decomposition d hE]
  have hset : Finset.range d = insert 0 (Finset.Icc 1 (d - 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp), Nat.sub_zero, extendedOverlapIntensity_zero,
    Measure.prod_prod, extendedGenerationIntensity_preimage d hE]
  rw [pow_two, add_assoc]

theorem lintegral_vectorEventCount_sq_decomposition {d : ℕ} (hd : 0 < d)
    {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    (∫⁻ ω, vectorEventCount d E ω ^ 2 ∂law) = generationIncrementIntensity d E +
      (generationIncrementIntensity d E) ^ 2 +
      ∑ j ∈ Finset.Icc 1 (d - 1), extendedOverlapIntensity j (d - j)
        (((restrictSequence d) ⁻¹' E) ×ˢ ((restrictSequence d) ⁻¹' E)) := by
  rw [lintegral_vectorEventCount_sq d hE, generationPairIntensity_event_decomposition_pos hd hE]

end FreezingGrowth.PWIT
