module

public import FreezingGrowth.PWIT.ManyToTwo
public import FreezingGrowth.PWIT.AllRankLeading
public import FreezingGrowth.PWIT.VectorLeading
public import FreezingGrowth.PWIT.SimplexBridge

/-! Actual all-rank count moments as generation intensity measures.
All identities are extended nonnegative real identities, before any finiteness
or real-integral conversion. Ordered pairs include the diagonal exactly once. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped ENNReal Classical

noncomputable def vectorEventCount (d : ℕ) (E : Set (Fin d → ℝ)) (ω : Sample) : ℝ≥0∞ :=
  ∑' r : Fin d → ℕ, E.indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω)

@[fun_prop] theorem measurable_vectorEventCount (d : ℕ) {E : Set (Fin d → ℝ)}
    (hE : MeasurableSet E) : Measurable (vectorEventCount d E) := by
  unfold vectorEventCount
  exact Measurable.tsum fun r =>
    (measurable_const.indicator hE).comp (measurable_tupleIncrement r)

theorem lintegral_vectorEventCount (d : ℕ) {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    (∫⁻ ω, vectorEventCount d E ω ∂law) = generationIncrementIntensity d E := by
  unfold vectorEventCount generationIncrementIntensity
  have hm (r : Fin d → ℕ) : AEMeasurable
      (fun ω : Sample => E.indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω)) law :=
    ((measurable_const.indicator hE).comp (measurable_tupleIncrement r)).aemeasurable
  rw [lintegral_tsum hm, Measure.sum_apply _ hE]
  apply tsum_congr
  intro r
  rw [Measure.map_apply (measurable_tupleIncrement r) hE]
  have hf : (fun ω => E.indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω)) =
      ((tupleIncrement r) ⁻¹' E).indicator (fun _ => 1) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_preimage]
  rw [hf, lintegral_indicator (hE.preimage (measurable_tupleIncrement r))]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]

theorem vectorEventCount_sq (d : ℕ) (E : Set (Fin d → ℝ)) (ω : Sample) :
    vectorEventCount d E ω ^ 2 =
      ∑' r : Fin d → ℕ, ∑' s : Fin d → ℕ,
        (E ×ˢ E).indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω, tupleIncrement s ω) := by
  unfold vectorEventCount
  rw [pow_two, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro r
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hr : tupleIncrement r ω ∈ E <;> by_cases hs : tupleIncrement s ω ∈ E <;>
    simp [hr, hs]

theorem lintegral_vectorEventCount_sq (d : ℕ) {E : Set (Fin d → ℝ)} (hE : MeasurableSet E) :
    (∫⁻ ω, vectorEventCount d E ω ^ 2 ∂law) = generationPairIntensity d (E ×ˢ E) := by
  simp_rw [vectorEventCount_sq]
  let F (r s : Fin d → ℕ) (ω : Sample) : ℝ≥0∞ :=
    (E ×ˢ E).indicator (fun _ => 1) (tupleIncrement r ω, tupleIncrement s ω)
  have hF (r s : Fin d → ℕ) : Measurable (F r s) :=
    (measurable_const.indicator (hE.prod hE)).comp (by fun_prop)
  change (∫⁻ ω, ∑' r, ∑' s, F r s ω ∂law) = _
  rw [lintegral_tsum (fun r => (Measurable.tsum (hF r)).aemeasurable)]
  unfold generationPairIntensity
  rw [Measure.sum_apply _ (hE.prod hE)]
  apply tsum_congr
  intro r
  rw [lintegral_tsum (fun s => (hF r s).aemeasurable), Measure.sum_apply _ (hE.prod hE)]
  apply tsum_congr
  intro s
  rw [Measure.map_apply (by fun_prop) (hE.prod hE)]
  have hf : F r s =
      {ω | (tupleIncrement r ω, tupleIncrement s ω) ∈ E ×ˢ E}.indicator (fun _ => 1) := by
    funext ω
    simp only [F, Set.indicator_apply, Set.mem_ofPred_eq]
  have hset : MeasurableSet {ω : Sample | (tupleIncrement r ω, tupleIncrement s ω) ∈ E ×ˢ E} :=
    (hE.prod hE).preimage (by fun_prop)
  rw [hf, lintegral_indicator hset]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
  congr 1

/-- A finite actual pair intensity supplies genuine square integrability. -/
theorem integrable_vectorEventCount_toReal_sq (d : ℕ) {E : Set (Fin d → ℝ)}
    (hE : MeasurableSet E) (hfinite : generationPairIntensity d (E ×ˢ E) ≠ ∞) :
    Integrable (fun ω => (vectorEventCount d E ω).toReal ^ 2) law := by
  have hm := (measurable_vectorEventCount d hE).pow_const 2
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (show (∫⁻ ω, vectorEventCount d E ω ^ 2 ∂law) ≠ ∞ by
      rw [lintegral_vectorEventCount_sq d hE]; exact hfinite)
  simpa only [ENNReal.toReal_pow] using hi

theorem integral_vectorEventCount_toReal_sq (d : ℕ) {E : Set (Fin d → ℝ)}
    (hE : MeasurableSet E) (hfinite : generationPairIntensity d (E ×ˢ E) ≠ ∞) :
    (∫ ω, (vectorEventCount d E ω).toReal ^ 2 ∂law) =
      (generationPairIntensity d (E ×ˢ E)).toReal := by
  have hm := (measurable_vectorEventCount d hE).pow_const 2
  have ha : ∀ᵐ ω ∂law, vectorEventCount d E ω ^ 2 < ∞ := by
    apply ae_lt_top hm
    rw [lintegral_vectorEventCount_sq d hE]
    exact hfinite
  simpa only [ENNReal.toReal_pow, lintegral_vectorEventCount_sq d hE] using
    integral_toReal hm.aemeasurable ha

def endpointLeadingVectorEvent (d : ℕ) (J : Set ℝ) : Set (Fin d → ℝ) :=
  {x | totalWait x ∈ J ∧ vectorLeading 0 x}

theorem measurableSet_endpointLeadingVectorEvent (d : ℕ) {J : Set ℝ}
    (hJ : MeasurableSet J) : MeasurableSet (endpointLeadingVectorEvent d J) :=
  (hJ.preimage (measurable_totalWait d)).inter (measurableSet_vectorLeading d 0)

theorem vectorEventCount_endpointLeading (d : ℕ) (J : Set ℝ) (ω : Sample) :
    vectorEventCount d (endpointLeadingVectorEvent d J) ω =
      pathEventCount d (endpointLeadingEvent J) ω := by
  unfold vectorEventCount pathEventCount
  rw [← (Finset.Nat.sigmaAntidiagonalTupleEquivTuple d).tsum_eq
    (fun r => (endpointLeadingVectorEvent d J).indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω)),
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  change (∑' r : Finset.Nat.antidiagonalTuple d k,
    (endpointLeadingVectorEvent d J).indicator (fun _ => (1 : ℝ≥0∞)) (tupleIncrement r ω)) = _
  rw [tsum_fintype]
  rw [rankClass, Finset.sum_image (fun _ _ _ _ h => List.ofFn_injective h)]
  conv_rhs => rw [← Finset.sum_finset_coe]
  apply Finset.sum_congr rfl
  intro r _
  have he : tupleIncrement r.val ω ∈ endpointLeadingVectorEvent d J ↔
      ω ∈ endpointLeadingEvent J (List.ofFn r.val) := by
    simp only [endpointLeadingVectorEvent, endpointLeadingEvent, Set.mem_ofPred_eq, totalWait,
      ← birth_ofFn_eq_sum_tupleIncrement, vectorLeading_tupleIncrement_iff]
  simp only [Set.indicator_apply, he]

end FreezingGrowth.PWIT
