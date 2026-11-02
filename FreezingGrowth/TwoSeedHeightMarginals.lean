module

public import FreezingGrowth.TwoSeedHeightModel
public import FreezingGrowth.SeededDeletionExpectations

/-! The two height coordinates of the source coupling have the actual finite
word laws. This constructs their joint height law without asserting a joint
graft construction of every labelled edge. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedCoupling

open MeasureTheory
open scoped Classical

noncomputable def testGrowth (p : HeightProfile) (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∫ q, f q.maximum ∂HeightProfile.grow p n

theorem testGrowth_eq_seed (a b M n : ℕ) (hab : max a b ≤ M) (f : ℕ → ℝ) :
    testGrowth ⟨{a, b}, M⟩ n f =
      ∫ p, f (HeightProfile.seedHeight a b M p) ∂RRTSplit.heightPairLaw n := by
  unfold testGrowth
  rw [← integral_map measurable_from_top.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    HeightProfile.join_seed_maximum_law a b M hab n,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable]

/-- The first component is assigned to the new child, as in the source. -/
theorem child_testGrowth_eq_seed (a M n : ℕ) (f : ℕ → ℝ) :
    testGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n f =
      ∫ p, f (HeightProfile.seedHeight (a + 1) a M p) ∂RRTSplit.heightPairLaw n := by
  have hp : (⟨{a, a + 1}, max M (a + 1)⟩ : HeightProfile) =
      ⟨{a + 1, a}, max M (a + 1)⟩ := by
    congr 1
    exact Multiset.pair_comm _ _
  rw [hp, testGrowth_eq_seed (a + 1) a (max M (a + 1)) n (by omega) f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    have he : HeightProfile.seedHeight (a + 1) a (max M (a + 1)) p =
        HeightProfile.seedHeight (a + 1) a M p := by
      unfold HeightProfile.seedHeight
      omega
    exact congrArg f he)

theorem word_height_test_as_profile (xs : Word) (f : ℕ → ℝ) :
    (∫ h, f h ∂xs.heightLaw) = ∫ p, f p.maximum ∂HeightProfile.wordLaw xs := by
  rw [Word.heightLaw, ← HeightProfile.map_law_maximum,
    integral_map measurable_from_top.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable]
  rfl

theorem baseline_word_test (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (f : ℕ → ℝ) :
    (∫ h, f h ∂(twoActivePrefix m ++ List.replicate n true).heightLaw) =
      ∫ d, testGrowth (depthProfile d) n f ∂depthMaximumLaw m := by
  rw [word_height_test_as_profile, HeightProfile.integral_wordLaw_append_replicate,
    ← depthMaximumLaw_profile m hm,
    integral_map (measurable_of_countable _).aemeasurable measurable_from_top.aestronglyMeasurable]
  rfl

theorem long_word_test (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (f : ℕ → ℝ) :
    (∫ h, f h ∂((twoActivePrefix m ++ [false, true]) ++ List.replicate n true).heightLaw) =
      ∫ d, (testGrowth ⟨{d.1, d.1 + 1}, max d.2.2 (d.1 + 1)⟩ n f +
        testGrowth ⟨{d.2.1, d.2.1 + 1}, max d.2.2 (d.2.1 + 1)⟩ n f) / 2
          ∂depthMaximumLaw m := by
  rw [word_height_test_as_profile, HeightProfile.integral_wordLaw_append_replicate,
    show twoActivePrefix m ++ [false, true] =
      (twoActivePrefix m ++ [false]) ++ [true] by simp,
    HeightProfile.integral_wordLaw_append_singleton, HeightProfile.integral_wordLaw_append_singleton,
    ← depthMaximumLaw_profile m hm,
    integral_map (measurable_of_countable _).aemeasurable measurable_from_top.aestronglyMeasurable]
  change (∫ d, (∫ p, (∫ q, testGrowth q n f ∂HeightProfile.transitionLaw p true)
    ∂HeightProfile.transitionLaw (depthProfile d) false) ∂depthMaximumLaw m) = _
  simp_rw [depthProfile, HeightProfile.integral_freeze_attach_pair]

theorem baselineHeight_marginal (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (heightModelLaw m n).map baselineHeight =
      (twoActivePrefix m ++ List.replicate n true).heightLaw := by
  let := heightModelLaw_probability m hm n
  let : IsProbabilityMeasure ((heightModelLaw m n).map baselineHeight) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  apply measures_eq_of_integrals
  intro f
  rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    heightModelLaw_integral m hm n, baseline_word_test m hm n f]
  apply integral_congr_ae
  filter_upwards [depthMaximumLaw_ae_valid m hm] with d hd
  exact (testGrowth_eq_seed d.1 d.2.1 d.2.2 n hd.1 f).symm

theorem longHeight_marginal (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (heightModelLaw m n).map longHeight =
      ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true).heightLaw := by
  let := heightModelLaw_probability m hm n
  let : IsProbabilityMeasure ((heightModelLaw m n).map longHeight) :=
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  apply measures_eq_of_integrals
  intro f
  let A : DepthMaximum → ℝ := fun d =>
    ∫ p, f (HeightProfile.seedHeight (d.1 + 1) d.1 d.2.2 p) ∂RRTSplit.heightPairLaw n
  let B : DepthMaximum → ℝ := fun d =>
    ∫ p, f (HeightProfile.seedHeight (d.2.1 + 1) d.2.1 d.2.2 p) ∂RRTSplit.heightPairLaw n
  have hswap : (∫ d, B d ∂depthMaximumLaw m) = ∫ d, A d ∂depthMaximumLaw m := by
    have hh := integral_map (μ := depthMaximumLaw m) (f := A)
      (measurable_of_countable swapDepthMaximum).aemeasurable
      (measurable_of_countable A).aestronglyMeasurable
    rw [depthMaximumLaw_swap m hm] at hh
    exact hh.symm
  have hadd : (∫ d, A d + B d ∂depthMaximumLaw m) =
      (∫ d, A d ∂depthMaximumLaw m) + ∫ d, B d ∂depthMaximumLaw m := by
    simpa only [Pi.add_apply] using integral_add
      (depthMaximumLaw_integrable m hm A) (depthMaximumLaw_integrable m hm B)
  have havg : (∫ d, (A d + B d) / 2 ∂depthMaximumLaw m) =
      ∫ d, A d ∂depthMaximumLaw m := by
    rw [integral_div, hadd, hswap]
    ring
  rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    heightModelLaw_integral m hm n, long_word_test m hm n f]
  simp_rw [child_testGrowth_eq_seed]
  exact havg.symm

/-- Both actual finite-word height laws are realized on the same model space. -/
theorem source_height_coupling (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (heightModelLaw m n).map longHeight =
        ((twoActivePrefix m ++ [false, true]) ++ List.replicate n true).heightLaw ∧
      (heightModelLaw m n).map baselineHeight =
        (twoActivePrefix m ++ List.replicate n true).heightLaw :=
  ⟨longHeight_marginal m hm n, baselineHeight_marginal m hm n⟩

end FreezingGrowth.TwoSeedCoupling
