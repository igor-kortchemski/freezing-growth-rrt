module

public import FreezingGrowth.PWIT.GenerationCount
public import FreezingGrowth.PWIT.GoodPaths

/-!
# Counts without an excess-rank cutoff

Counts are initially extended nonnegative real numbers. Their real projections
are used only after domination by the actual finite-mean generation count.
The barrier count omits the rank window and bad-rank event; it is distinct
from the finite count in `GoodPaths`.
-/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical ENNReal

noncomputable def pathEventCount (d : ℕ) (E : Vertex → Set Sample) (ω : Sample) : ℝ≥0∞ :=
  ∑' k : ℕ, ∑ v ∈ rankClass d k, (E v).indicator (fun _ => (1 : ℝ≥0∞)) ω

@[fun_prop] theorem measurable_pathEventCount (d : ℕ) {E : Vertex → Set Sample}
    (hE : ∀ v, MeasurableSet (E v)) : Measurable (pathEventCount d E) := by
  unfold pathEventCount
  exact Measurable.tsum fun k => Finset.measurable_sum _ fun v _ =>
    measurable_const.indicator (hE v)

theorem pathEventCount_mono (d : ℕ) {E F : Vertex → Set Sample}
    (hEF : ∀ v, v.length = d → E v ⊆ F v) (ω : Sample) :
    pathEventCount d E ω ≤ pathEventCount d F ω := by
  apply ENNReal.tsum_le_tsum
  intro k
  apply Finset.sum_le_sum
  intro v hv
  by_cases he : ω ∈ E v
  · simp [he, hEF v (mem_rankClass.mp hv).1 he]
  · simp [he]

theorem pathEventCount_union (d : ℕ) {E F : Vertex → Set Sample}
    (hEF : ∀ v, Disjoint (E v) (F v)) (ω : Sample) :
    pathEventCount d (fun v => E v ∪ F v) ω =
      pathEventCount d E ω + pathEventCount d F ω := by
  unfold pathEventCount
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro k
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hn : ¬ (ω ∈ E v ∧ ω ∈ F v) := fun hh => Set.disjoint_left.mp (hEF v) hh.1 hh.2
  by_cases he : ω ∈ E v <;> by_cases hf : ω ∈ F v <;> simp_all

theorem generationCount_eq_pathEventCount (d : ℕ) (t : ℝ) (ω : Sample) :
    generationCount d t ω = pathEventCount d (fun v => {ω | birth ω v ≤ t}) ω := by
  unfold generationCount pathEventCount
  apply tsum_congr
  intro k
  unfold rankBirthCount
  rw [ENNReal.ofReal_sum_of_nonneg (fun v _ =>
    Set.indicator_nonneg (fun _ _ => by norm_num) ω)]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : birth ω v ≤ t <;> simp [hv]

theorem pathEventCount_le_generationCount (d : ℕ) {E : Vertex → Set Sample} {t : ℝ}
    (hE : ∀ v, v.length = d → E v ⊆ {ω | birth ω v ≤ t}) (ω : Sample) :
    pathEventCount d E ω ≤ generationCount d t ω := by
  rw [generationCount_eq_pathEventCount]
  exact pathEventCount_mono d hE ω

theorem one_le_pathEventCount_of_mem {d : ℕ} {E : Vertex → Set Sample}
    {v : Vertex} {ω : Sample} (hv : v.length = d) (hE : ω ∈ E v) :
    (1 : ℝ≥0∞) ≤ pathEventCount d E ω := by
  have hm : v ∈ rankClass d v.sum := mem_rankClass.mpr ⟨hv, rfl⟩
  have hs := Finset.single_le_sum (s := rankClass d v.sum)
    (f := fun v => (E v).indicator (fun _ => (1 : ℝ≥0∞)) ω) (fun _ _ => zero_le) hm
  rw [Set.indicator_of_mem hE] at hs
  exact hs.trans (ENNReal.le_tsum
    (f := fun k => ∑ v ∈ rankClass d k, (E v).indicator (fun _ => (1 : ℝ≥0∞)) ω) v.sum)

theorem pathEventCount_pos_iff (d : ℕ) (E : Vertex → Set Sample) (ω : Sample) :
    0 < pathEventCount d E ω ↔ ∃ v, v.length = d ∧ ω ∈ E v := by
  constructor
  · intro hh
    by_contra hn
    have hz (k : ℕ) : (∑ v ∈ rankClass d k, (E v).indicator (fun _ => (1 : ℝ≥0∞)) ω) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      exact Set.indicator_of_notMem (fun he => hn ⟨v, (mem_rankClass.mp hv).1, he⟩) _
    simp only [pathEventCount, hz, tsum_zero, lt_self_iff_false] at hh
  · rintro ⟨v, hv, he⟩
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) (one_le_pathEventCount_of_mem hv he)

theorem lintegral_pathEventCount (d : ℕ) {E : Vertex → Set Sample}
    (hE : ∀ v, MeasurableSet (E v)) :
    (∫⁻ ω, pathEventCount d E ω ∂law) = ∑' k : ℕ, ∑ v ∈ rankClass d k, law (E v) := by
  unfold pathEventCount
  rw [lintegral_tsum (fun k => (Finset.measurable_sum _ fun v _ =>
    measurable_const.indicator (hE v)).aemeasurable)]
  apply tsum_congr
  intro k
  rw [lintegral_finsetSum _ (fun v _ => measurable_const.indicator (hE v))]
  apply Finset.sum_congr rfl
  intro v _
  exact lintegral_indicator_one (hE v)

theorem ae_pathEventCount_finite (d : ℕ) {E : Vertex → Set Sample} {t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ v, v.length = d + 1 → E v ⊆ {ω | birth ω v ≤ t}) :
    ∀ᵐ ω ∂law, pathEventCount (d + 1) E ω < ∞ := by
  filter_upwards [ae_generationCount_finite d ht] with ω hω
  exact (pathEventCount_le_generationCount _ hE ω).trans_lt hω

theorem integrable_pathEventCount_toReal (d : ℕ) {E : Vertex → Set Sample}
    (hEm : ∀ v, MeasurableSet (E v)) {t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ v, v.length = d + 1 → E v ⊆ {ω | birth ω v ≤ t}) :
    Integrable (fun ω => (pathEventCount (d + 1) E ω).toReal) law := by
  apply integrable_toReal_of_lintegral_ne_top (measurable_pathEventCount _ hEm).aemeasurable
  apply ne_of_lt
  calc
    (∫⁻ ω, pathEventCount (d + 1) E ω ∂law) ≤ ∫⁻ ω, generationCount (d + 1) t ω ∂law :=
      lintegral_mono (pathEventCount_le_generationCount _ hE)
    _ < ∞ := by rw [lintegral_generationCount d ht]; exact ENNReal.ofReal_lt_top

theorem integral_pathEventCount_toReal (d : ℕ) {E : Vertex → Set Sample}
    (hEm : ∀ v, MeasurableSet (E v)) {t : ℝ} (ht : 0 ≤ t)
    (hE : ∀ v, v.length = d + 1 → E v ⊆ {ω | birth ω v ≤ t}) :
    (∫ ω, (pathEventCount (d + 1) E ω).toReal ∂law) =
      (∑' k : ℕ, ∑ v ∈ rankClass (d + 1) k, law (E v)).toReal := by
  rw [integral_toReal (measurable_pathEventCount _ hEm).aemeasurable
    (ae_pathEventCount_finite d ht hE), lintegral_pathEventCount _ hEm]

def allRankGoodEvent (d : ℕ) (a : ℝ) (v : Vertex) : Set Sample :=
  {ω | timeCenter d - 1 ≤ birth ω v ∧ birth ω v ≤ timeCenter d ∧
    leading a v ω ∧ ¬ badInterior a v ω}

theorem measurableSet_allRankGoodEvent (d : ℕ) (a : ℝ) (v : Vertex) :
    MeasurableSet (allRankGoodEvent d a v) :=
  (measurableSet_le measurable_const (measurable_birth v)).inter
    ((measurableSet_le (measurable_birth v) measurable_const).inter
      ((measurableSet_leading a v).inter (measurableSet_badInterior a v).compl))

noncomputable def allRankGoodCount (d : ℕ) (a : ℝ) (ω : Sample) : ℝ :=
  (pathEventCount d (allRankGoodEvent d a) ω).toReal

theorem ae_allRankGoodCount_finite (d : ℕ) (a : ℝ) :
    ∀ᵐ ω ∂law, pathEventCount (d + 1) (allRankGoodEvent (d + 1) a) ω < ∞ := by
  apply ae_pathEventCount_finite d (t := timeCenter (d + 1))
    (by unfold timeCenter; positivity)
  intro v _ ω hω
  exact hω.2.1

theorem integrable_allRankGoodCount (d : ℕ) (a : ℝ) :
    Integrable (allRankGoodCount (d + 1) a) law := by
  apply integrable_pathEventCount_toReal d (measurableSet_allRankGoodEvent _ _)
    (t := timeCenter (d + 1)) (by unfold timeCenter; positivity)
  intro v _ ω hω
  exact hω.2.1

theorem allRankGoodCount_pos_subset_reaches (d : ℕ) (a : ℝ) :
    {ω | 0 < allRankGoodCount d a ω} ⊆ reaches d (timeCenter d) := by
  intro ω hω
  have hh : 0 < pathEventCount d (allRankGoodEvent d a) ω :=
    (ENNReal.toReal_pos_iff.mp hω).1
  obtain ⟨v, hv, he⟩ := (pathEventCount_pos_iff _ _ _).mp hh
  exact ⟨v, hv, he.2.1⟩

end FreezingGrowth.PWIT
