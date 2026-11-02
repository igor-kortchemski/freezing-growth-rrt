module

public import FreezingGrowth.TaggedTwoSeedHeightModel
public import FreezingGrowth.RRTSplitCDF

/-!
# Exact height errors in the first two tagged freezing cases

The first case can add one only when its first recursive-tree component is
empty. Its genuine size tag is retained in an explicit almost-sure bridge.
The second case changes height by at most one on the same height model.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Classical ENNReal

namespace RRTSplit

theorem componentLaw_first_height_pos (k l : ℕ) :
    ∀ᵐ r ∂componentLaw k l, r.1 ≠ 0 → 0 < Forward.treeHeight r.2.1 := by
  rw [componentLaw, ae_map_iff measurable_prodMk_left.aemeasurable (by measurability)]
  by_cases hk : k = 0
  · exact Eventually.of_forall (fun _ hh => False.elim (hh hk))
  · apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [RRT.treeHeight_pos (by omega : 1 ≤ k)] with s hs
    exact Eventually.of_forall (fun _ _ => hs)

/-- The size tag is the actual first-component edge count. -/
theorem mixtureLaw_first_height_pos (n : ℕ) :
    ∀ᵐ r ∂mixtureLaw n, r.1 ≠ 0 → 0 < Forward.treeHeight r.2.1 := by
  let P : Result → Prop := fun r => r.1 ≠ 0 → 0 < Forward.treeHeight r.2.1
  have hc (k : ℕ) : componentLaw k (n - k) {r | ¬P r} = 0 :=
    ae_iff.mp (componentLaw_first_height_pos k (n - k))
  rw [ae_iff]
  change mixtureLaw n {r | ¬P r} = 0
  rw [mixtureLaw_eq_sum, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  simp_rw [hc]
  simp

/-- The same implication holds for the split of the genuine larger tree. -/
theorem firstEdgeSplit_first_height_pos (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw RRT.allAttach (n + 1),
      (firstEdgeSplit n s).1 ≠ 0 →
        0 < Forward.treeHeight (firstEdgeSplit n s).2.1 := by
  have hh := mixtureLaw_first_height_pos n
  rw [← treeLaw_firstEdgeSplit n] at hh
  exact ae_of_ae_map measurable_from_top.aemeasurable hh

theorem heightLaw_zero_real_mass (k : ℕ) :
    (Forward.heightLaw RRT.allAttach k).real {h | h = 0} = if k = 0 then 1 else 0 := by
  have he : {h : ℕ | h = 0} = {h | h ≤ 0} := by ext h; simp
  rw [he]
  cases k with
  | zero => simpa using heightLaw_cdf_initial 0
  | succ k => simpa using heightLaw_cdf_zero k

theorem heightPairLaw_first_zero (n : ℕ) :
    (heightPairLaw n).real {p | p.1 = 0} = 1 / ((n : ℝ) + 1) := by
  have he : {p : ℕ × ℕ | p.1 = 0} = {h : ℕ | h = 0} ×ˢ Set.univ := by ext p; simp
  rw [he, heightPairLaw_real_rectangle]
  simp only [probReal_univ, mul_one]
  simp_rw [heightLaw_zero_real_mass]
  simp

end RRTSplit

namespace TwoSeedCoupling

theorem baselineHeight_le_caseHeight_zero (z : ModelSample) : baselineHeight z ≤ caseHeight 0 z := by
  simp only [baselineHeight, caseHeight, ↓reduceIte, HeightProfile.seedHeight]
  omega

theorem caseHeight_zero_le_baseline_succ (z : ModelSample) : caseHeight 0 z ≤ baselineHeight z + 1 := by
  simp only [baselineHeight, caseHeight, ↓reduceIte, HeightProfile.seedHeight]
  omega

theorem caseHeight_zero_eq_of_first_pos (z : ModelSample) (hX : 1 ≤ z.2.1) :
    caseHeight 0 z = baselineHeight z := by
  simp only [baselineHeight, caseHeight, ↓reduceIte, HeightProfile.seedHeight]
  omega

/-- Source case (a): a nonzero actual split-size tag forces exact equality. -/
theorem caseHeight_zero_eq_of_size_ne_zero (n : ℕ) (d : DepthMaximum) :
    ∀ᵐ r ∂RRTSplit.mixtureLaw n, r.1 ≠ 0 →
      caseHeight 0 (d, (Forward.treeHeight r.2.1, Forward.treeHeight r.2.2)) =
        baselineHeight (d, (Forward.treeHeight r.2.1, Forward.treeHeight r.2.2)) := by
  filter_upwards [RRTSplit.mixtureLaw_first_height_pos n] with r hr
  intro hk
  exact caseHeight_zero_eq_of_first_pos _ (hr hk)

theorem caseHeight_zero_real_le (z : ModelSample) :
    (caseHeight 0 z : ℝ) ≤ (baselineHeight z : ℝ) + (if z.2.1 = 0 then 1 else 0) := by
  by_cases hX : z.2.1 = 0
  · rw [ite_eq_left hX]
    exact_mod_cast caseHeight_zero_le_baseline_succ z
  · rw [ite_eq_right hX, add_zero, caseHeight_zero_eq_of_first_pos z (by omega)]

theorem baselineHeight_le_caseHeight_one (z : ModelSample) : baselineHeight z ≤ caseHeight 1 z := by
  simp only [baselineHeight, caseHeight, show (1 : Fin 3) ≠ 0 by decide,
    ↓reduceIte, HeightProfile.seedHeight]
  omega

theorem caseHeight_one_le_baseline_succ (z : ModelSample) : caseHeight 1 z ≤ baselineHeight z + 1 := by
  simp only [baselineHeight, caseHeight, show (1 : Fin 3) ≠ 0 by decide,
    ↓reduceIte, HeightProfile.seedHeight]
  omega

theorem caseHeight_one_abs_sub_baseline_le (z : ModelSample) :
    |(caseHeight 1 z : ℝ) - (baselineHeight z : ℝ)| ≤ 1 := by
  have hlo : (baselineHeight z : ℝ) ≤ caseHeight 1 z := by
    exact_mod_cast baselineHeight_le_caseHeight_one z
  have hhi : (caseHeight 1 z : ℝ) ≤ (baselineHeight z : ℝ) + 1 := by
    exact_mod_cast caseHeight_one_le_baseline_succ z
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem integral_baselineHeight (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ z, (baselineHeight z : ℝ) ∂heightModelLaw m n) =
      Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) := by
  rw [Word.expectedHeight, ← baselineHeight_marginal m hm n,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]

theorem integral_first_component_zero (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ z : ModelSample, (if z.2.1 = 0 then (1 : ℝ) else 0) ∂heightModelLaw m n) =
      1 / ((n : ℝ) + 1) := by
  let := depthMaximumLaw_probability m hm
  rw [heightModelLaw_integral m hm n]
  have hi : (∫ p : ℕ × ℕ, (if p.1 = 0 then (1 : ℝ) else 0)
      ∂RRTSplit.heightPairLaw n) = 1 / ((n : ℝ) + 1) := by
    have hh := integral_indicator_one (μ := RRTSplit.heightPairLaw n)
      (by measurability : MeasurableSet {p : ℕ × ℕ | p.1 = 0})
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] at hh
    exact hh.trans (RRTSplit.heightPairLaw_first_zero n)
  simp_rw [hi]
  simp

/-- Exact source error `1/(n+1)` for the new-child-frozen branch. -/
theorem caseHeightLaw_zero_mean_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ h : ℕ, (h : ℝ) ∂caseHeightLaw m n 0) ≤
      Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) + 1 / ((n : ℝ) + 1) := by
  rw [caseHeightLaw_integral]
  calc
    _ ≤ ∫ z : ModelSample, ((baselineHeight z : ℝ) + if z.2.1 = 0 then (1 : ℝ) else 0)
        ∂heightModelLaw m n :=
      integral_mono (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _)
        caseHeight_zero_real_le
    _ = _ := by
      rw [integral_add (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _),
        integral_baselineHeight m hm n, integral_first_component_zero m hm n]

/-- Exact source error one for the old-parent-frozen branch. -/
theorem caseHeightLaw_one_mean_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∫ h : ℕ, (h : ℝ) ∂caseHeightLaw m n 1) ≤
      Word.expectedHeight (twoActivePrefix m ++ List.replicate n true) + 1 := by
  let := heightModelLaw_probability m hm n
  rw [caseHeightLaw_integral]
  calc
    _ ≤ ∫ z : ModelSample, ((baselineHeight z : ℝ) + 1) ∂heightModelLaw m n := by
      apply integral_mono (heightModelLaw_integrable m hm n _) (heightModelLaw_integrable m hm n _)
      intro z
      change (caseHeight 1 z : ℝ) ≤ (baselineHeight z : ℝ) + 1
      exact_mod_cast caseHeight_one_le_baseline_succ z
    _ = _ := by
      rw [integral_add (heightModelLaw_integrable m hm n _) (integrable_const _),
        integral_baselineHeight m hm n, integral_const]
      simp

end TwoSeedCoupling
end FreezingGrowth
