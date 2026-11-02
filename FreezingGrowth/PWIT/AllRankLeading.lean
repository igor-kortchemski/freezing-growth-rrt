module

public import FreezingGrowth.PWIT.AllRankCount
public import FreezingGrowth.PWIT.Leading
public import FreezingGrowth.PWIT.CriticalWindow

/-! Exact leading-path intensities on the actual all-rank count.
The cyclic factor is used only after summing a complete finite rank class. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical ENNReal

def endpointLeadingEvent (J : Set ℝ) (v : Vertex) : Set Sample :=
  {ω | birth ω v ∈ J ∧ leading 0 v ω}

theorem measurableSet_endpointLeadingEvent {J : Set ℝ} (hJ : MeasurableSet J) (v : Vertex) :
    MeasurableSet (endpointLeadingEvent J v) :=
  (hJ.preimage (measurable_birth v)).inter (measurableSet_leading 0 v)

theorem rank_leading_probability {d : ℕ} [NeZero d] (k : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) :
    (d : ℝ) * (∑ v ∈ rankClass d k, law.real (endpointLeadingEvent J v)) =
      ∑ v ∈ rankClass d k, law.real {ω | birth ω v ∈ J} := by
  let f : ℝ → ℝ := J.indicator (fun _ => 1)
  have hf : Integrable (fun x : Fin d → ℝ => f (∑ i, x i)) (rankIncrementMeasure d k) := by
    have hm : Measurable (fun x : Fin d → ℝ => ∑ i, x i) := by fun_prop
    exact (integrable_const (1 : ℝ)).indicator (hJ.preimage hm)
  have h := integral_leading_rankClass k f hf
  have he (v : Vertex) :
      (∫ ω, {ω | leading 0 v ω}.indicator (fun ω => f (birth ω v)) ω ∂law) =
        law.real (endpointLeadingEvent J v) := by
    have hfun : {ω | leading 0 v ω}.indicator (fun ω => f (birth ω v)) =
        (endpointLeadingEvent J v).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hl : leading 0 v ω <;> by_cases hb : birth ω v ∈ J <;>
        simp [f, endpointLeadingEvent, hl, hb]
    rw [hfun]
    exact integral_indicator_one (measurableSet_endpointLeadingEvent hJ v)
  have ht (v : Vertex) : (∫ ω, f (birth ω v) ∂law) = law.real {ω | birth ω v ∈ J} := by
    exact integral_indicator_one (hJ.preimage (measurable_birth v))
  simp_rw [he, ht] at h
  simpa only [rankClass, Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h)] using h

theorem rank_leading_measure {d : ℕ} [NeZero d] (k : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) :
    (d : ℝ≥0∞) * (∑ v ∈ rankClass d k, law (endpointLeadingEvent J v)) =
      ∑ v ∈ rankClass d k, law {ω | birth ω v ∈ J} := by
  have h := congrArg ENNReal.ofReal (rank_leading_probability (d := d) k hJ)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)] at h
  simp only [ENNReal.ofReal_natCast] at h
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => measureReal_nonneg)] at h
  have hm (s : Set Sample) : ENNReal.ofReal (law.real s) = law s :=
    ofReal_measureReal (measure_ne_top law s)
  simp_rw [hm] at h
  exact h

/-- Exact cyclic factor for the true extended all-rank count, with arbitrary
measurable endpoint selection and no assumption of finite total mass. -/
theorem lintegral_pathEventCount_leading {d : ℕ} [NeZero d] {J : Set ℝ}
    (hJ : MeasurableSet J) :
    (d : ℝ≥0∞) * (∫⁻ ω, pathEventCount d (endpointLeadingEvent J) ω ∂law) =
      ∫⁻ ω, pathEventCount d (fun v => {ω | birth ω v ∈ J}) ω ∂law := by
  rw [lintegral_pathEventCount _ (measurableSet_endpointLeadingEvent hJ),
    lintegral_pathEventCount d (E := fun v => {ω | birth ω v ∈ J})
      (fun v => hJ.preimage (measurable_birth v)),
    ← ENNReal.tsum_mul_left]
  exact tsum_congr (fun k => rank_leading_measure k hJ)

theorem lintegral_leadingCount_le {d : ℕ} [NeZero d] {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ ω, pathEventCount d (endpointLeadingEvent (Set.Iic t)) ω ∂law) =
      ENNReal.ofReal (t ^ d / ((d.factorial : ℝ) * (d : ℝ))) := by
  have h := lintegral_pathEventCount_leading (d := d) (J := Set.Iic t) measurableSet_Iic
  have hn : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have he : (∫⁻ ω, pathEventCount d (fun v => {ω | birth ω v ∈ Set.Iic t}) ω ∂law) =
      ENNReal.ofReal (t ^ d / d.factorial) := by
    simp only [Set.mem_Iic]
    simp_rw [← generationCount_eq_pathEventCount]
    rw [hm, lintegral_generationCount m ht]
  rw [he] at h
  apply (ENNReal.mul_right_inj (a := (d : ℝ≥0∞)) (by exact_mod_cast hn.ne') (by finiteness)).mp
  rw [h, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
  congr 1
  field_simp [show (d : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hn.ne']

theorem integral_leadingCount_le (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, (pathEventCount (d + 1) (endpointLeadingEvent (Set.Iic t)) ω).toReal ∂law) =
      t ^ (d + 1) / (((d + 1).factorial : ℝ) * (d + 1 : ℕ)) := by
  rw [integral_toReal (measurable_pathEventCount _
    (measurableSet_endpointLeadingEvent measurableSet_Iic)).aemeasurable
      (ae_pathEventCount_finite d ht (fun _ _ _ hh => hh.1)),
    lintegral_leadingCount_le ht, ENNReal.toReal_ofReal (by positivity)]

/-- The actual leading-path endpoint-window count has the expected difference
of intensities. A nonnegative lower endpoint is explicitly required. -/
theorem integral_leadingCount_Ioc (d : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ ω, (pathEventCount (d + 1) (endpointLeadingEvent (Set.Ioc s t)) ω).toReal ∂law) =
      (t ^ (d + 1) - s ^ (d + 1)) / (((d + 1).factorial : ℝ) * (d + 1 : ℕ)) := by
  have ht : 0 ≤ t := hs.trans hst
  let S := endpointLeadingEvent (Set.Iic s)
  let T := endpointLeadingEvent (Set.Iic t)
  let W := endpointLeadingEvent (Set.Ioc s t)
  have hsplit : T = fun v => S v ∪ W v := by
    funext v
    ext ω
    change (birth ω v ≤ t ∧ leading 0 v ω) ↔
      (birth ω v ≤ s ∧ leading 0 v ω) ∨ ((s < birth ω v ∧ birth ω v ≤ t) ∧ leading 0 v ω)
    constructor
    · rintro ⟨hb, hl⟩
      by_cases hh : birth ω v ≤ s
      · exact Or.inl ⟨hh, hl⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hh, hb⟩, hl⟩
    · rintro (⟨hb, hl⟩ | ⟨⟨_, hb⟩, hl⟩)
      · exact ⟨hb.trans hst, hl⟩
      · exact ⟨hb, hl⟩
  have hdis (v : Vertex) : Disjoint (S v) (W v) := by
    rw [Set.disjoint_left]
    intro ω hs' hw'
    exact (not_lt_of_ge hs'.1) hw'.1.1
  have hS := ae_pathEventCount_finite d hs
    (E := S) (fun _ _ _ hh => hh.1)
  have hW := ae_pathEventCount_finite d ht
    (E := W) (fun _ _ _ hh => hh.1.2)
  have hid : (fun ω => (pathEventCount (d + 1) T ω).toReal) =ᵐ[law]
      fun ω => (pathEventCount (d + 1) S ω).toReal +
        (pathEventCount (d + 1) W ω).toReal := by
    filter_upwards [hS, hW] with ω hs' hw'
    rw [hsplit, pathEventCount_union _ hdis, ENNReal.toReal_add hs'.ne hw'.ne]
  have hiS : Integrable (fun ω => (pathEventCount (d + 1) S ω).toReal) law :=
    integrable_pathEventCount_toReal d
      (measurableSet_endpointLeadingEvent measurableSet_Iic) hs (fun _ _ _ hh => hh.1)
  have hiW : Integrable (fun ω => (pathEventCount (d + 1) W ω).toReal) law :=
    integrable_pathEventCount_toReal d
      (measurableSet_endpointLeadingEvent measurableSet_Ioc) ht (fun _ _ _ hh => hh.1.2)
  have hi := integral_congr_ae hid
  rw [integral_add hiS hiW] at hi
  change (∫ ω, (pathEventCount (d + 1) (endpointLeadingEvent (Set.Iic t)) ω).toReal ∂law) =
    (∫ ω, (pathEventCount (d + 1) (endpointLeadingEvent (Set.Iic s)) ω).toReal ∂law) +
      (∫ ω, (pathEventCount (d + 1) (endpointLeadingEvent (Set.Ioc s t)) ω).toReal ∂law) at hi
  rw [integral_leadingCount_le d ht, integral_leadingCount_le d hs] at hi
  rw [sub_div]
  linarith

noncomputable def exactLeadingWindowCount (d : ℕ) (ω : Sample) : ℝ :=
  (pathEventCount d
    (endpointLeadingEvent (Set.Ioc (timeCenter d - 1) (timeCenter d))) ω).toReal

/-- A positive mean for actual exactly-leading endpoint-window paths. The
interior-barrier exclusion and the success probability are not asserted. -/
theorem eventually_exactLeadingWindowCount_mean_pos :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ d : ℕ in Filter.atTop,
      c ≤ ∫ ω, exactLeadingWindowCount d ω ∂law := by
  obtain ⟨c, hc, hevent⟩ := eventually_leadingWindowIntensity_pos
  refine ⟨c, hc, ?_⟩
  filter_upwards [hevent, tendsto_timeCenter.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop 1] with d hd ht hd1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  unfold exactLeadingWindowCount
  rw [integral_leadingCount_Ioc m (by linarith) (by linarith)]
  exact hd

end FreezingGrowth.PWIT
