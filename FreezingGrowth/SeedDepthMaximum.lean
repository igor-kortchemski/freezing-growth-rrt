module

public import FreezingGrowth.PairMaximumStatistics
public import FreezingGrowth.ProfileWordExpectations
public import FreezingGrowth.TwoSurvivorGap

/-! The genuine joint law of two ordered-distinct depths and the old maximum.
Its countable carrier forgets labels only after the actual same-tree sampling. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory
open scoped Classical ENNReal ProbabilityTheory

abbrev DepthMaximum := ℕ × (ℕ × ℕ)

def depthProfile (d : DepthMaximum) : HeightProfile := ⟨{d.1, d.2.1}, d.2.2⟩

noncomputable def depthMaximumLaw (m : ℕ) : Measure DepthMaximum :=
  (Forward.treeLaw RRT.allAttach m).bind fun s =>
    (uniformRootPair s.active).map (fun p => (s.height p.1, s.height p.2, Forward.treeHeight s))

theorem depthMaximumLaw_probability (m : ℕ) (hm : 1 ≤ m) :
    IsProbabilityMeasure (depthMaximumLaw m) := by
  unfold depthMaximumLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs
  have hc : (s.active.card : ℤ) = (m : ℤ) + 1 := by
    simpa only [RRT.activeCount_allAttach] using hs.1
  let := uniformRootPair_isProbabilityMeasure s.active (by omega : 2 ≤ s.active.card)
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance

private theorem uniformRootPair_ae (s : Finset ℕ) (hs : 2 ≤ s.card)
    (P : ℕ × ℕ → Prop) (hP : ∀ p ∈ s.offDiag, P p) :
    ∀ᵐ p ∂uniformRootPair s, P p := by
  let := uniformRootPair_isProbabilityMeasure s hs
  apply (ae_iff_prob_eq_one (measurable_of_countable P)).mpr
  rw [uniformRootPair, Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  have he : s.offDiag.filter P = s.offDiag := Finset.filter_eq_self.mpr hP
  rw [he]
  exact ENNReal.div_self (by exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')
    (ENNReal.natCast_ne_top _)

theorem depthMaximumLaw_ae_valid (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ d ∂depthMaximumLaw m, max d.1 d.2.1 ≤ d.2.2 ∧ d.2.2 ≤ m := by
  let := depthMaximumLaw_probability m hm
  let P : Set DepthMaximum := {d | max d.1 d.2.1 ≤ d.2.2 ∧ d.2.2 ≤ m}
  have hP : MeasurableSet P := (Set.to_countable _).measurableSet
  apply (ae_iff_prob_eq_one (measurable_of_countable
    (fun d : DepthMaximum => max d.1 d.2.1 ≤ d.2.2 ∧ d.2.2 ≤ m))).mpr
  change (depthMaximumLaw m) P = 1
  rw [depthMaximumLaw, Measure.bind_apply hP measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂Forward.treeLaw RRT.allAttach m := by
      apply lintegral_congr_ae
      filter_upwards [Forward.treeLaw_valid RRT.allAttach m,
        Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs hc
      have hcZ : (s.active.card : ℤ) = (m : ℤ) + 1 := by
        simpa only [RRT.activeCount_allAttach] using hc.1
      have hcard : 2 ≤ s.active.card := by omega
      let := uniformRootPair_isProbabilityMeasure s.active hcard
      rw [Measure.map_apply (measurable_of_countable _) hP]
      apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
      apply uniformRootPair_ae s.active hcard
      intro p hp
      have hp' := Finset.mem_offDiag.mp hp
      exact ⟨max_le (Forward.height_le_treeHeight (hs.active_subset hp'.1))
        (Forward.height_le_treeHeight (hs.active_subset hp'.2.1)), hs.treeHeight_le⟩
    _ = 1 := by simp

theorem depthMaximumLaw_integrable (m : ℕ) (hm : 1 ≤ m) (F : DepthMaximum → ℝ) :
    Integrable F (depthMaximumLaw m) := by
  let := depthMaximumLaw_probability m hm
  let S := (Finset.range (m + 1)).product
    ((Finset.range (m + 1)).product (Finset.range (m + 1)))
  let C : ℝ := ∑ d ∈ S, |F d|
  apply (integrable_const C).mono' (measurable_of_countable F).aestronglyMeasurable
  filter_upwards [depthMaximumLaw_ae_valid m hm] with d hd
  rw [Real.norm_eq_abs]
  apply Finset.single_le_sum (fun d _ => abs_nonneg (F d))
  dsimp [S]
  simp only [Finset.mem_product, Finset.mem_range]
  omega

theorem depthMaximumLaw_integral (m : ℕ) (hm : 1 ≤ m) (F : DepthMaximum → ℝ) :
    (∫ d, F d ∂depthMaximumLaw m) =
      ∫ s, Forward.activePairHeightMean s (fun a b M => F (a, b, M))
        ∂Forward.treeLaw RRT.allAttach m := by
  let K : ProbabilityTheory.Kernel Forward.State DepthMaximum :=
    ⟨fun s => (uniformRootPair s.active).map
      (fun p => (s.height p.1, s.height p.2, Forward.treeHeight s)), measurable_from_top⟩
  have hi := depthMaximumLaw_integrable m hm F
  have hi' : Integrable F ((K ∘ₖ ProbabilityTheory.Kernel.const Unit
      (Forward.treeLaw RRT.allAttach m)) ()) := by
    simpa only [K, depthMaximumLaw, ProbabilityTheory.Kernel.coe_mk,
      ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  have he : (∫ d, F d ∂depthMaximumLaw m) =
      ∫ s, (∫ d, F d ∂(uniformRootPair s.active).map
        (fun p => (s.height p.1, s.height p.2, Forward.treeHeight s)))
          ∂Forward.treeLaw RRT.allAttach m := by
    simpa only [K, depthMaximumLaw, ProbabilityTheory.Kernel.coe_mk,
      ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hh
  rw [he]
  apply integral_congr_ae
  filter_upwards [Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs
  have hc : (s.active.card : ℤ) = (m : ℤ) + 1 := by
    simpa only [RRT.activeCount_allAttach] using hs.1
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  exact (Forward.activePairHeightMean_eq_integral s (by omega)
    (fun a b M => F (a, b, M))).symm

theorem measures_eq_of_integrals {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : α → ℝ, (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real A = ν.real A
  rw [← integral_indicator_one hA, ← integral_indicator_one hA]
  exact h _

theorem depthMaximumLaw_profile (m : ℕ) (hm : 1 ≤ m) :
    (depthMaximumLaw m).map depthProfile = HeightProfile.wordLaw (twoActivePrefix m) := by
  let := depthMaximumLaw_probability m hm
  let : IsProbabilityMeasure ((depthMaximumLaw m).map depthProfile) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  let : IsProbabilityMeasure (HeightProfile.wordLaw (twoActivePrefix m)) :=
    HeightProfile.law_probability _ _
  apply measures_eq_of_integrals
  intro G
  rw [integral_map (measurable_of_countable _).aemeasurable
    measurable_from_top.aestronglyMeasurable, depthMaximumLaw_integral m hm]
  exact (twoActivePrefix_profile_integral m hm G).symm

theorem depthMaximumLaw_maximum (m : ℕ) (hm : 1 ≤ m) :
    (depthMaximumLaw m).map (fun d => d.2.2) = Forward.heightLaw RRT.allAttach m := by
  let := depthMaximumLaw_probability m hm
  let : IsProbabilityMeasure ((depthMaximumLaw m).map (fun d => d.2.2)) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  apply measures_eq_of_integrals
  intro f
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    depthMaximumLaw_integral m hm, Forward.heightLaw_integral]
  apply integral_congr_ae
  filter_upwards [Forward.treeLaw_counts RRT.allAttach m (RRT.before_extinction m).le] with s hs
  have hc : (s.active.card : ℤ) = (m : ℤ) + 1 := by
    simpa only [RRT.activeCount_allAttach] using hs.1
  exact Forward.activePairHeightMean_const s (by omega) f

end FreezingGrowth.TwoSeedCoupling
