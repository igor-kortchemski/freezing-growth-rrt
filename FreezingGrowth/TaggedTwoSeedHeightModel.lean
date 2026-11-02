module

public import FreezingGrowth.TwoSeedHeightMarginals
public import FreezingGrowth.AttachFreezeWordExpectation
public import FreezingGrowth.ForwardTwoSeedCases
public import Mathlib.Probability.Independence.Basic

/-! The source's three freezing cases on an actual height coupling. The tag is
identified with the vertex-identity freezing kernel before any depths are
averaged. The old depths and old maximum retain their joint law. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

noncomputable def threeCaseLaw : Measure (Fin 3) :=
  Measure.uniformOfFinset Finset.univ

theorem threeCaseLaw_eq : threeCaseLaw = (3 : ℝ≥0∞)⁻¹ •
    (Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp
  simp [threeCaseLaw, hu, Measure.uniformOfFinset, smul_add, add_assoc]

instance threeCaseLaw_probability : IsProbabilityMeasure threeCaseLaw := by
  constructor
  rw [threeCaseLaw_eq]
  norm_num [Measure.smul_apply, Measure.add_apply]
  calc
    (3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹ + (3 : ℝ≥0∞)⁻¹ = (3 : ℝ≥0∞)⁻¹ * 3 := by ring
    _ = 1 := ENNReal.inv_mul_cancel (by norm_num) (by finiteness)

theorem threeCaseLaw_singleton (c : Fin 3) : threeCaseLaw {c} = (3 : ℝ≥0∞)⁻¹ := by
  simp [threeCaseLaw]

theorem threeCaseLaw_integrable (f : Fin 3 → ℝ) : Integrable f threeCaseLaw := by
  rw [threeCaseLaw_eq]
  have hi (c : Fin 3) : Integrable f (Measure.dirac c) := integrable_dirac (by simp)
  exact (((hi 0).add_measure (hi 1)).add_measure (hi 2)).smul_measure (by norm_num)

theorem threeCaseLaw_integral (f : Fin 3 → ℝ) :
    (∫ c, f c ∂threeCaseLaw) = (f 0 + f 1 + f 2) / 3 := by
  have hi (c : Fin 3) : Integrable f (Measure.dirac c) := integrable_dirac (by simp)
  rw [threeCaseLaw_eq, integral_smul_measure,
    integral_add_measure ((hi 0).add_measure (hi 1)) (hi 2),
    integral_add_measure (hi 0) (hi 1)]
  simp [smul_eq_mul, div_eq_mul_inv, mul_add]
  ring

/-- The profile after freezing the child, parent, or other old vertex. -/
def caseProfile (c : Fin 3) (d : DepthMaximum) : HeightProfile :=
  if c = 0 then ⟨{d.1, d.2.1}, max d.2.2 (d.1 + 1)⟩
  else if c = 1 then ⟨{d.1 + 1, d.2.1}, max d.2.2 (d.1 + 1)⟩
  else ⟨{d.1, d.1 + 1}, max d.2.2 (d.1 + 1)⟩

/-- This identifies the model's tags with actual vertex IDs, including when
different active vertices have equal depth. -/
theorem actual_tagged_profile_kernel {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    Forward.twoSeedTaggedFreezeLaw s n u = threeCaseLaw.map
      (fun c => (c, caseProfile c (s.height u, s.height v, Forward.treeHeight s))) := by
  rw [Forward.twoSeedTaggedFreezeLaw_eq hs hactive huv, threeCaseLaw_eq,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _)]
  simp [caseProfile]

def caseHeight (c : Fin 3) (z : ModelSample) : ℕ :=
  if c = 0 then HeightProfile.seedHeight z.1.1 z.1.2.1
    (max z.1.2.2 (z.1.1 + 1)) z.2
  else if c = 1 then HeightProfile.seedHeight (z.1.1 + 1) z.1.2.1
    (max z.1.2.2 (z.1.1 + 1)) z.2
  else HeightProfile.seedHeight (z.1.1 + 1) z.1.1 z.1.2.2 z.2

theorem caseProfile_test (c : Fin 3) (d : DepthMaximum)
    (hd : max d.1 d.2.1 ≤ d.2.2) (n : ℕ) (f : ℕ → ℝ) :
    testGrowth (caseProfile c d) n f =
      ∫ p, f (caseHeight c (d, p)) ∂RRTSplit.heightPairLaw n := by
  fin_cases c
  · simpa [caseProfile, caseHeight] using
      testGrowth_eq_seed d.1 d.2.1 (max d.2.2 (d.1 + 1)) n (by omega) f
  · simpa [caseProfile, caseHeight] using
      testGrowth_eq_seed (d.1 + 1) d.2.1 (max d.2.2 (d.1 + 1)) n (by omega) f
  · simpa [caseProfile, caseHeight] using child_testGrowth_eq_seed d.1 d.2.2 n f

noncomputable def caseHeightLaw (m n : ℕ) (c : Fin 3) : Measure ℕ :=
  (heightModelLaw m n).map (caseHeight c)

theorem caseHeightLaw_probability (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (c : Fin 3) :
    IsProbabilityMeasure (caseHeightLaw m n c) := by
  let := heightModelLaw_probability m hm n
  exact Measure.isProbabilityMeasure_map_iff
    (measurable_of_countable _).aemeasurable |>.mpr inferInstance

theorem caseHeightLaw_integrable (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (c : Fin 3)
    (f : ℕ → ℝ) : Integrable f (caseHeightLaw m n c) := by
  unfold caseHeightLaw
  apply (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).mpr
  exact heightModelLaw_integrable m hm n _

theorem caseHeightLaw_integral (m n : ℕ) (c : Fin 3) (f : ℕ → ℝ) :
    (∫ h, f h ∂caseHeightLaw m n c) =
      ∫ z, f (caseHeight c z) ∂heightModelLaw m n :=
  integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable

theorem caseHeightLaw_two (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    caseHeightLaw m n 2 =
      ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true).heightLaw := by
  have hc : caseHeight 2 = longHeight := by
    funext z
    simp [caseHeight, longHeight]
  rw [caseHeightLaw, hc]
  exact longHeight_marginal m hm n

abbrev TaggedSample := DepthMaximum × (Fin 3 × (ℕ × ℕ))

noncomputable def taggedHeightModelLaw (m n : ℕ) : Measure TaggedSample :=
  (depthMaximumLaw m).prod (threeCaseLaw.prod (RRTSplit.heightPairLaw n))

def caseTag (z : TaggedSample) : Fin 3 := z.2.1

def forgetCase (z : TaggedSample) : ModelSample := (z.1, z.2.2)

def taggedHeight (z : TaggedSample) : ℕ := caseHeight (caseTag z) (forgetCase z)

theorem taggedHeightModelLaw_probability (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IsProbabilityMeasure (taggedHeightModelLaw m n) := by
  let := depthMaximumLaw_probability m hm
  unfold taggedHeightModelLaw
  infer_instance

/-- The fresh case tag is independent of the entire old data and fresh split,
not only of their separate one-dimensional marginals. -/
theorem taggedHeightModelLaw_joint (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (taggedHeightModelLaw m n).map (fun z => (caseTag z, forgetCase z)) =
      threeCaseLaw.prod (heightModelLaw m n) := by
  let := depthMaximumLaw_probability m hm
  have h₁ := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : (DepthMaximum × Fin 3) × (ℕ × ℕ) ≃ᵐ TaggedSample)
    (measurePreserving_prodAssoc (depthMaximumLaw m) threeCaseLaw (RRTSplit.heightPairLaw n))
  have h₂ := (Measure.measurePreserving_swap (μ := depthMaximumLaw m) (ν := threeCaseLaw)).prod
    (MeasurePreserving.id (RRTSplit.heightPairLaw n))
  have h₃ := measurePreserving_prodAssoc threeCaseLaw (depthMaximumLaw m)
    (RRTSplit.heightPairLaw n)
  exact (h₃.comp (h₂.comp h₁)).map_eq

theorem taggedHeightModelLaw_tag (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (taggedHeightModelLaw m n).map caseTag = threeCaseLaw := by
  let := heightModelLaw_probability m hm n
  have h := congrArg (fun μ => μ.map Prod.fst) (taggedHeightModelLaw_joint m hm n)
  rw [Measure.map_map measurable_fst (measurable_of_countable _),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem taggedHeightModelLaw_forget (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (taggedHeightModelLaw m n).map forgetCase = heightModelLaw m n := by
  have h := congrArg (fun μ => μ.map Prod.snd) (taggedHeightModelLaw_joint m hm n)
  rw [Measure.map_map measurable_snd (measurable_of_countable _),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem caseTag_independent_data (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IndepFun caseTag forgetCase (taggedHeightModelLaw m n) := by
  let := taggedHeightModelLaw_probability m hm n
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable).mpr
  rw [taggedHeightModelLaw_tag m hm n, taggedHeightModelLaw_forget m hm n]
  exact taggedHeightModelLaw_joint m hm n

theorem taggedHeightModelLaw_integrable (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (F : TaggedSample → ℝ) : Integrable F (taggedHeightModelLaw m n) := by
  unfold taggedHeightModelLaw
  apply (integrable_prod_iff (measurable_of_countable F).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro d
    apply (integrable_prod_iff (measurable_of_countable _).aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun c => RRTSplit.heightPairLaw_integrable n _),
      threeCaseLaw_integrable _⟩
  · exact depthMaximumLaw_integrable m hm _

theorem taggedHeightModelLaw_integral (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (F : TaggedSample → ℝ) :
    (∫ z, F z ∂taggedHeightModelLaw m n) = ∫ d,
      ((∫ p, F (d, 0, p) ∂RRTSplit.heightPairLaw n) +
        (∫ p, F (d, 1, p) ∂RRTSplit.heightPairLaw n) +
        (∫ p, F (d, 2, p) ∂RRTSplit.heightPairLaw n)) / 3 ∂depthMaximumLaw m := by
  unfold taggedHeightModelLaw
  rw [integral_prod F (taggedHeightModelLaw_integrable m hm n F)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro d
  have hi : Integrable (fun z => F (d, z))
      (threeCaseLaw.prod (RRTSplit.heightPairLaw n)) := by
    apply (integrable_prod_iff (measurable_of_countable _).aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall (fun c => RRTSplit.heightPairLaw_integrable n _),
      threeCaseLaw_integrable _⟩
  dsimp only
  rw [integral_prod _ hi, threeCaseLaw_integral]

/-- A branch restriction has mass one third; its normalized height law is the
corresponding actual split-law model. -/
theorem taggedHeightModelLaw_restrict_case (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (c : Fin 3) :
    ((taggedHeightModelLaw m n).restrict {z | caseTag z = c}).map taggedHeight =
      (3 : ℝ≥0∞)⁻¹ • caseHeightLaw m n c := by
  let := heightModelLaw_probability m hm n
  let R : TaggedSample → Fin 3 × ModelSample := fun z => (caseTag z, forgetCase z)
  let E : Set (Fin 3 × ModelSample) := {c} ×ˢ Set.univ
  have hR : Measurable R := measurable_of_countable _
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  have hpre : R ⁻¹' E = {z | caseTag z = c} := by
    ext z
    simp [R, E]
  have hrestrict : ((taggedHeightModelLaw m n).restrict {z | caseTag z = c}).map R =
      (threeCaseLaw.prod (heightModelLaw m n)).restrict E := by
    rw [← taggedHeightModelLaw_joint m hm n, Measure.restrict_map hR hE, hpre]
  have hh := congrArg (fun μ : Measure (Fin 3 × ModelSample) =>
    μ.map (fun z => caseHeight z.1 z.2)) hrestrict
  rw [Measure.map_map (measurable_of_countable _) hR,
    ← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_singleton, threeCaseLaw_singleton,
    Measure.prod_smul_left, Measure.dirac_prod,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_map (measurable_of_countable _) measurable_prodMk_left] at hh
  exact hh

private theorem cons_pair_comm (a b : ℕ) : a ::ₘ {b} = b ::ₘ {a} := by
  simpa only [Multiset.insert_eq_cons] using Multiset.pair_comm a b

theorem attachFreeze_word_test (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (f : ℕ → ℝ) :
    (∫ h, f h ∂((twoActivePrefix m ++ [true, false]) ++ List.replicate n true).heightLaw) =
      ∫ d, (testGrowth (caseProfile 0 d) n f + testGrowth (caseProfile 1 d) n f +
        testGrowth (caseProfile 2 d) n f) / 3 ∂depthMaximumLaw m := by
  let A : DepthMaximum → ℝ := fun d =>
    (testGrowth (caseProfile 0 d) n f + testGrowth (caseProfile 1 d) n f +
      testGrowth (caseProfile 2 d) n f) / 3
  have hswap : (∫ d, A (swapDepthMaximum d) ∂depthMaximumLaw m) =
      ∫ d, A d ∂depthMaximumLaw m := by
    have hh := integral_map (μ := depthMaximumLaw m) (f := A)
      (measurable_of_countable swapDepthMaximum).aemeasurable
      (measurable_of_countable A).aestronglyMeasurable
    rw [depthMaximumLaw_swap m hm] at hh
    exact hh.symm
  have hadd : (∫ d, A d + A (swapDepthMaximum d) ∂depthMaximumLaw m) =
      (∫ d, A d ∂depthMaximumLaw m) + ∫ d, A (swapDepthMaximum d) ∂depthMaximumLaw m := by
    simpa only [Pi.add_apply] using integral_add
      (depthMaximumLaw_integrable m hm A) (depthMaximumLaw_integrable m hm _)
  have havg : (∫ d, (A d + A (swapDepthMaximum d)) / 2 ∂depthMaximumLaw m) =
      ∫ d, A d ∂depthMaximumLaw m := by
    rw [integral_div, hadd, hswap]
    ring
  rw [word_height_test_as_profile, HeightProfile.integral_wordLaw_append_replicate,
    show twoActivePrefix m ++ [true, false] =
      (twoActivePrefix m ++ [true]) ++ [false] by simp,
    HeightProfile.integral_wordLaw_append_singleton, HeightProfile.integral_wordLaw_append_singleton,
    ← depthMaximumLaw_profile m hm,
    integral_map (measurable_of_countable _).aemeasurable measurable_from_top.aestronglyMeasurable]
  change (∫ d, (∫ p, (∫ q, testGrowth q n f ∂HeightProfile.transitionLaw p false)
    ∂HeightProfile.transitionLaw (depthProfile d) true) ∂depthMaximumLaw m) = _
  simp_rw [depthProfile, HeightProfile.integral_attach_freeze_pair]
  calc
    _ = ∫ d, (A d + A (swapDepthMaximum d)) / 2 ∂depthMaximumLaw m := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro d
      simp [A, caseProfile, swapDepthMaximum]
      rw [cons_pair_comm d.2.1 d.1, cons_pair_comm (d.2.1 + 1) d.1]
      ring
    _ = _ := havg

/-- The tag-preserving model has the actual attachment/freezing word's height
marginal, with all three branches and all coincident profiles retained. -/
theorem taggedHeight_marginal (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (taggedHeightModelLaw m n).map taggedHeight =
      ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true).heightLaw := by
  let := taggedHeightModelLaw_probability m hm n
  let : IsProbabilityMeasure ((taggedHeightModelLaw m n).map taggedHeight) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  apply measures_eq_of_integrals
  intro f
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable,
    taggedHeightModelLaw_integral m hm n, attachFreeze_word_test m hm n f]
  apply integral_congr_ae
  filter_upwards [depthMaximumLaw_ae_valid m hm] with d hd
  simp only [taggedHeight, caseTag, forgetCase,
    caseProfile_test 0 d hd.1 n f, caseProfile_test 1 d hd.1 n f,
    caseProfile_test 2 d hd.1 n f]

end FreezingGrowth.TwoSeedCoupling
