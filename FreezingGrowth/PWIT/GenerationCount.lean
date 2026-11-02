module

public import FreezingGrowth.PWIT.GenerationFirstMoment
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Counting a whole generation by its disjoint finite rank slices. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical ENNReal

noncomputable def generationCount (d : ℕ) (t : ℝ) (ω : Sample) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (rankBirthCount d k t ω)

theorem rankBirthCount_nonneg (d k : ℕ) (t : ℝ) (ω : Sample) :
    0 ≤ rankBirthCount d k t ω := by
  unfold rankBirthCount
  apply Finset.sum_nonneg
  intro v hv
  exact Set.indicator_nonneg (fun _ _ => by norm_num) ω

@[fun_prop] theorem measurable_rankBirthCount (d k : ℕ) (t : ℝ) :
    Measurable (rankBirthCount d k t) := by
  unfold rankBirthCount
  exact Finset.measurable_sum _ (fun v _ =>
    measurable_const.indicator (measurableSet_le (measurable_birth v) measurable_const))

@[fun_prop] theorem measurable_generationCount (d : ℕ) (t : ℝ) :
    Measurable (generationCount d t) := by
  unfold generationCount
  exact Measurable.tsum (fun k => (measurable_rankBirthCount d k t).ennreal_ofReal)

theorem one_le_generationCount_of_reaches {d : ℕ} {t : ℝ} {ω : Sample}
    (hh : ω ∈ reaches d t) : (1 : ℝ≥0∞) ≤ generationCount d t ω := by
  obtain ⟨v, hv, hb⟩ := hh
  have hmem : v ∈ rankClass d v.sum := mem_rankClass.mpr ⟨hv, rfl⟩
  have hone : (1 : ℝ) ≤ rankBirthCount d v.sum t ω := by
    have hs := Finset.single_le_sum (s := rankClass d v.sum)
      (f := fun v => {ω | birth ω v ≤ t}.indicator (fun _ => (1 : ℝ)) ω)
      (fun v _ => Set.indicator_nonneg (fun _ _ => by norm_num) ω) hmem
    simpa only [rankBirthCount, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hb] using hs
  have hh := ENNReal.ofReal_le_ofReal hone
  simp only [ENNReal.ofReal_one] at hh
  unfold generationCount
  exact hh.trans (ENNReal.le_tsum (f := fun k => ENNReal.ofReal (rankBirthCount d k t ω)) v.sum)

/-- The count represents exactly the measurable path-existence event. -/
theorem reaches_iff_generationCount_pos (d : ℕ) (t : ℝ) (ω : Sample) :
    ω ∈ reaches d t ↔ 0 < generationCount d t ω := by
  constructor
  · intro hh
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) (one_le_generationCount_of_reaches hh)
  · intro hh
    by_contra hn
    have hz (k : ℕ) : rankBirthCount d k t ω = 0 := by
      unfold rankBirthCount
      apply Finset.sum_eq_zero
      intro v hv
      have hb : ¬ birth ω v ≤ t := fun hb => hn ⟨v, (mem_rankClass.mp hv).1, hb⟩
      simp [hb]
    simp only [generationCount, hz, ENNReal.ofReal_zero, tsum_zero, lt_self_iff_false] at hh

/-- Exact first moment for the actual count, hence finite almost surely. -/
theorem lintegral_generationCount (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ ω, generationCount (d + 1) t ω ∂law) =
      ENNReal.ofReal (t ^ (d + 1) / (d + 1).factorial) := by
  unfold generationCount
  rw [lintegral_tsum (fun k => ((measurable_rankBirthCount (d + 1) k t).ennreal_ofReal).aemeasurable)]
  have he (k : ℕ) : (∫⁻ ω, ENNReal.ofReal (rankBirthCount (d + 1) k t ω) ∂law) =
      ENNReal.ofReal (∫ ω, rankBirthCount (d + 1) k t ω ∂law) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_rankBirthCount _ _ _)
      (Filter.Eventually.of_forall (rankBirthCount_nonneg _ _ _))).symm
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => integral_nonneg (rankBirthCount_nonneg _ _ _))
    (hasSum_integral_rankBirthCount d ht).summable,
    (hasSum_integral_rankBirthCount d ht).tsum_eq]

theorem ae_generationCount_finite (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂law, generationCount (d + 1) t ω < ∞ := by
  apply ae_lt_top (measurable_generationCount _ _)
  rw [lintegral_generationCount d ht]
  exact ENNReal.ofReal_ne_top

theorem integrable_generationCount_toReal (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => (generationCount (d + 1) t ω).toReal) law := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_generationCount _ _).aemeasurable
  rw [lintegral_generationCount d ht]
  exact ENNReal.ofReal_ne_top

theorem integral_generationCount_toReal (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, (generationCount (d + 1) t ω).toReal ∂law) =
      t ^ (d + 1) / (d + 1).factorial := by
  rw [integral_toReal (measurable_generationCount _ _).aemeasurable
    (ae_generationCount_finite d ht), lintegral_generationCount d ht,
    ENNReal.toReal_ofReal (by positivity)]

/-- First-moment bound on reaching a fixed positive generation by a given time. -/
theorem reaches_probability_le_firstMoment (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    law.real (reaches (d + 1) t) ≤ t ^ (d + 1) / (d + 1).factorial := by
  have he : law (reaches (d + 1) t) ≤ ∫⁻ ω, generationCount (d + 1) t ω ∂law := by
    rw [← lintegral_indicator_one (measurableSet_reaches _ _)]
    apply lintegral_mono
    intro ω
    by_cases hh : ω ∈ reaches (d + 1) t
    · rw [Set.indicator_of_mem hh]
      exact one_le_generationCount_of_reaches hh
    · rw [Set.indicator_of_notMem hh]
      exact zero_le
  rw [lintegral_generationCount d ht] at he
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ t ^ (d + 1) / (d + 1).factorial)] using hh

end FreezingGrowth.PWIT
