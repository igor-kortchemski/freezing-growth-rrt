module

public import FreezingGrowth.ReverseDistinguishedInitialization
public import FreezingGrowth.FirstPeakDeletion

/-! Actual source-tail parameters and almost-sure validity of Algorithm 3's
initialization. The shorter field is the incoming common forest; identification
with the shortened schedule's labelled tail is a separate relabelling task. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

noncomputable def initializationTailLaw (k : ℕ) (tail : Word) : Measure Forest :=
  lawAfter (Word.toSigns (List.replicate k true ++ [false] ++ tail))
    (List.replicate k true ++ [false] ++ tail).length tail.length

instance initializationTailLaw_probability (k : ℕ) (tail : Word) :
    IsProbabilityMeasure (initializationTailLaw k tail) := lawAfter_probability _ _ _

/-- Immediately before the removed freeze is read backwards, its label is
fresh and the common forest contains exactly `k` components. -/
theorem initializationTailLaw_parameters (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ F ∂initializationTailLaw k tail,
      Sum.inr k ∉ F.forest.vertices ∧ F.forest.roots.card = k := by
  have hv := lawAfter_valid (Word.toSigns (List.replicate k true ++ [false] ++ tail))
    (List.replicate k true ++ [false] ++ tail).length tail.length
    ((Word.admissible_iff_le_extinctionTime _).mp ha) (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)
  have hphase : (List.replicate k true ++ [false] ++ tail).length - tail.length = k + 1 := by
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega
  rw [hphase] at hv
  filter_upwards [hv] with F hF
  refine ⟨valid_freezing_fresh hF, ?_⟩
  have hcount : activeCount (Word.toSigns (List.replicate k true ++ [false] ++ tail)) (k + 1) =
      (k : ℤ) := by
    calc
      _ = activeCount (Word.toSigns (List.replicate k true ++ [false])) (k + 1) :=
        Word.activeCount_append_left _ tail (by simp)
      _ = _ := Word.first_peak_prefix_activeCount k
  simpa only [hcount, Int.toNat_natCast] using hF.roots_card

def InitializationValid (k i : ℕ) (z : InitializationSample) : Prop :=
  z.longer.forest.roots.card = k ∧ z.shorter.forest.roots.card = k ∧
  (z.longer.forest.IsSingletonRoot (.inr i) ↔ z.used = false) ∧
  z.delayedPair.1 ≤ k ∧ z.delayedPair.2 ≤ k ∧ z.delayedPair.1 ≠ z.delayedPair.2 ∧
  (z.used = false → 0 < z.delayedPair.1 ∧ 0 < z.delayedPair.2)

theorem initializationChoice_valid_predicate (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin (prependLabel F i).forest.roots.card ×
      Fin (prependLabel F i).forest.roots.card) (hp : p.1 ≠ p.2) :
    InitializationValid F.forest.roots.card i (initializationChoice F i p) := by
  obtain ⟨hs, hc, hflag, hfirst, hsecond, hne⟩ := initializationChoice_valid F hi p hp
  refine ⟨hc, by rw [hs], hflag, hfirst, hsecond, hne, ?_⟩
  intro hz
  simp only [initializationChoice, decide_eq_false_iff_not, not_or] at hz
  change 0 < p.1.val ∧ 0 < p.2.val
  omega

theorem initializationLaw_ae_valid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    ∀ᵐ z ∂initializationLaw F i, InitializationValid F.forest.roots.card i z := by
  unfold initializationLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
  have hp : ∀ᵐ p ∂uniformRootPair
      (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)),
      p ∈ (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)).offDiag := by
    rw [ae_iff]
    simp [uniformRootPair, Measure.uniformOfFinset_apply]
  filter_upwards [hp] with p hp
  exact initializationChoice_valid_predicate F hi p (Finset.mem_offDiag.mp hp).2.2

theorem initializationLaw_shorter (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    (initializationLaw F i).map InitializationSample.shorter = Measure.dirac F := by
  have hc : 2 ≤ (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)).card := by
    simp only [Finset.card_univ, Fintype.card_fin, prependLabel_roots_card F hi]
    omega
  let := uniformRootPair_isProbabilityMeasure _ hc
  rw [initializationLaw, Measure.map_map measurable_from_top (measurable_of_countable _)]
  change (uniformRootPair _).map (fun _ => F) = _
  rw [Measure.map_const]
  simp

noncomputable def sourceInitializationLaw (k : ℕ) (tail : Word) : Measure InitializationSample :=
  (initializationTailLaw k tail).bind (fun F => initializationLaw F k)

theorem sourceInitializationLaw_probability (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    IsProbabilityMeasure (sourceInitializationLaw k tail) := by
  unfold sourceInitializationLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  exact initializationLaw_probability F hF.1 (by omega)

/-- The source's two initialization cases are well defined under the actual
incoming tail law, with the original pair positions retained. -/
theorem sourceInitializationLaw_ae_valid (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ z ∂sourceInitializationLaw k tail, InitializationValid k k z := by
  rw [ae_iff, sourceInitializationLaw,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  exact ae_iff.mp (by simpa only [hF.2] using initializationLaw_ae_valid F hF.1)

/-- The comparison forest is left unchanged at initialization. -/
theorem sourceInitializationLaw_shorter (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    (sourceInitializationLaw k tail).map InitializationSample.shorter =
      initializationTailLaw k tail := by
  rw [sourceInitializationLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = (initializationTailLaw k tail).bind Measure.dirac := by
      apply Measure.bind_congr_right
      filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
      exact initializationLaw_shorter F hF.1 (by omega)
    _ = _ := Measure.bind_dirac

/-- The boundary `k=1` necessarily uses the distinguished singleton. -/
theorem sourceInitializationLaw_one_used (tail : Word)
    (ha : Word.admissible (List.replicate 1 true ++ [false] ++ tail)) :
    ∀ᵐ z ∂sourceInitializationLaw 1 tail, z.used = true := by
  filter_upwards [sourceInitializationLaw_ae_valid 1 tail ha] with z hz
  obtain ⟨_, _, _, hfirst, hsecond, hne, hpos⟩ := hz
  by_cases hu : z.used = false
  · have hp := hpos hu
    omega
  · cases h : z.used <;> simp_all

end FreezingGrowth.ReverseOrdered
