module

public import FreezingGrowth.PWIT.BallotIntensityUniform
public import FreezingGrowth.PWIT.PairCount
public import FreezingGrowth.PWIT.LeadingSplit

/-!
# Actual overlap intensities as three ballot factors

The angular/endpoint transport is performed under the unnormalized generation
measure. All integrations are nonnegative and need no preliminary finiteness.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem positiveOrthantVolume_eq_scaled_simplex (d : ℕ) [NeZero d] :
    positiveOrthantVolume d =
      ((simplexLaw d).prod (generationEndpointMeasure d)).map (fun z => z.2 • z.1) := by
  rw [← generationSpacing_eq_scaled_simplex, radialSpacingMeasure_one_eq_pi]
  rfl

theorem ofReal_nearLeadingProbability (d : ℕ) (A s : ℝ) :
    ENNReal.ofReal (nearLeadingProbability d A s) =
      simplexLaw d {p | vectorLeading A (s • p)} := by
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem ofReal_nearLeadingIntensityDensity (d : ℕ) (A s : ℝ) :
    ENNReal.ofReal (nearLeadingIntensityDensity d A s) =
      ENNReal.ofReal (nearLeadingProbability d A s) * generationEndpointDensity d s := by
  unfold nearLeadingIntensityDensity
  rw [ENNReal.ofReal_mul (by unfold nearLeadingProbability; positivity),
    ENNReal.ofReal_toReal]
  unfold generationEndpointDensity
  split_ifs <;> simp

/-- The allowance and weight may depend measurably on the endpoint. -/
theorem lintegral_generation_leading_weighted (d : ℕ) [NeZero d]
    (A : ℝ → ℝ) (hA : Measurable A) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, {x : Fin d → ℝ | vectorLeading (A (totalWait x)) x}.indicator
      (fun x => w (totalWait x)) x ∂positiveOrthantVolume d) =
      ∫⁻ s, ENNReal.ofReal (nearLeadingIntensityDensity d (A s) s) * w s := by
  let F : (Fin d → ℝ) → ℝ≥0∞ :=
    {x | vectorLeading (A (totalWait x)) x}.indicator (fun x => w (totalWait x))
  have hset : MeasurableSet {x : Fin d → ℝ | vectorLeading (A (totalWait x)) x} :=
    (measurableSet_vectorLeading_joint d).preimage ((hA.comp (measurable_totalWait d)).prodMk measurable_id)
  have hF : Measurable F := (hw.comp (measurable_totalWait d)).indicator hset
  change (∫⁻ x, F x ∂positiveOrthantVolume d) = _
  rw [positiveOrthantVolume_eq_scaled_simplex, lintegral_map hF (by fun_prop),
    lintegral_prod_symm (fun a : (Fin d → ℝ) × ℝ => F (a.2 • a.1)) (by fun_prop)]
  have hinner (s : ℝ) : (∫⁻ p, F (s • p) ∂simplexLaw d) =
      ENNReal.ofReal (nearLeadingProbability d (A s) s) * w s := by
    have he : (fun p => F (s • p)) =ᵐ[simplexLaw d]
        {p | vectorLeading (A s) (s • p)}.indicator (fun _ => w s) := by
      filter_upwards [simplexLaw_ae_nonnegative_sum_one d] with p hp
      have ht : totalWait (s • p) = s := by
        rw [totalWait_smul]
        change s * (∑ i, p i) = s
        rw [hp.2, mul_one]
      dsimp only [F]
      by_cases hv : vectorLeading (A s) (s • p)
      · have h₁ : s • p ∈ {x : Fin d → ℝ | vectorLeading (A (totalWait x)) x} := by
          change vectorLeading (A (totalWait (s • p))) (s • p)
          rwa [ht]
        have h₂ : p ∈ {p : Fin d → ℝ | vectorLeading (A s) (s • p)} := hv
        rw [Set.indicator_of_mem h₁, Set.indicator_of_mem h₂, ht]
      · have h₁ : s • p ∉ {x : Fin d → ℝ | vectorLeading (A (totalWait x)) x} := by
          change ¬vectorLeading (A (totalWait (s • p))) (s • p)
          rwa [ht]
        have h₂ : p ∉ {p : Fin d → ℝ | vectorLeading (A s) (s • p)} := hv
        rw [Set.indicator_of_notMem h₁, Set.indicator_of_notMem h₂]
    have hm : MeasurableSet {p : Fin d → ℝ | vectorLeading (A s) (s • p)} :=
      (measurableSet_vectorLeading d (A s)).preimage
        (show Measurable (fun p : Fin d → ℝ => s • p) by fun_prop)
    rw [lintegral_congr_ae he, lintegral_indicator_const hm,
      ofReal_nearLeadingProbability, mul_comm]
  simp_rw [hinner]
  unfold generationEndpointMeasure
  have hprob : Measurable (fun s => ENNReal.ofReal (nearLeadingProbability d (A s) s) * w s) :=
    (((measurable_nearLeadingProbability_joint d).comp
      (hA.prodMk measurable_id)).ennreal_ofReal).mul hw
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_generationEndpointDensity d)
    hprob]
  apply lintegral_congr
  intro s
  rw [ofReal_nearLeadingIntensityDensity]
  change generationEndpointDensity d s *
      (ENNReal.ofReal (nearLeadingProbability d (A s) s) * w s) = _
  ac_rfl

def ballotVectorEvent (d : ℕ) (A : ℝ) (J : Set ℝ) : Set (Fin d → ℝ) :=
  {x | totalWait x ∈ J ∧ vectorLeading A x}

theorem measurableSet_ballotVectorEvent (d : ℕ) (A : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (ballotVectorEvent d A J) :=
  (hJ.preimage (measurable_totalWait d)).inter (measurableSet_vectorLeading d A)

/-- The actual endpoint-window and near-leading intensity, without conditioning
on a null endpoint or assuming a density formula for a fixed path. -/
theorem positiveOrthantVolume_ballotVectorEvent (d : ℕ) [NeZero d]
    (A : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    positiveOrthantVolume d (ballotVectorEvent d A J) =
      ∫⁻ s in J, ENNReal.ofReal (nearLeadingIntensityDensity d A s) := by
  have h := lintegral_generation_leading_weighted d (fun _ => A) measurable_const
    (J.indicator 1) (measurable_const.indicator hJ)
  have he : (fun x : Fin d → ℝ => {x | vectorLeading A x}.indicator
      (fun x => J.indicator (1 : ℝ → ℝ≥0∞) (totalWait x)) x) =
        (ballotVectorEvent d A J).indicator 1 := by
    funext x
    by_cases h₁ : vectorLeading A x <;> by_cases h₂ : totalWait x ∈ J <;>
      simp [ballotVectorEvent, h₁, h₂]
  change (∫⁻ x, {x : Fin d → ℝ | vectorLeading A x}.indicator
      (fun x => J.indicator 1 (totalWait x)) x ∂positiveOrthantVolume d) = _ at h
  rw [he, lintegral_indicator_one (measurableSet_ballotVectorEvent d A hJ)] at h
  rw [h, ← lintegral_indicator hJ]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ J <;> simp [hs]

noncomputable def overlapAllowance (j q : ℕ) (m S : ℝ) : ℝ := S - (j : ℝ) / (j + q : ℕ) * m + 1

@[fun_prop] theorem measurable_overlapAllowance (j q : ℕ) (m : ℝ) :
    Measurable (overlapAllowance j q m) := by unfold overlapAllowance; fun_prop

noncomputable def suffixBallotMass (q : ℕ) (m A S : ℝ) : ℝ≥0∞ :=
  positiveOrthantVolume q (ballotVectorEvent q A (Ioc (m - 1 - S) (m - S)))

theorem suffixBallotMass_eq_lintegral (q : ℕ) [NeZero q] (m A S : ℝ) :
    suffixBallotMass q m A S =
      ∫⁻ U in Ioc (m - 1 - S) (m - S),
        ENNReal.ofReal (nearLeadingIntensityDensity q A U) :=
  positiveOrthantVolume_ballotVectorEvent q A measurableSet_Ioc

@[fun_prop] theorem measurable_suffixBallotMass_joint (q : ℕ) (m : ℝ) :
    Measurable (fun z : ℝ × ℝ => suffixBallotMass q m z.1 z.2) := by
  have hset : MeasurableSet {p : (ℝ × ℝ) × (Fin q → ℝ) |
      totalWait p.2 ∈ Ioc (m - 1 - p.1.2) (m - p.1.2) ∧ vectorLeading p.1.1 p.2} := by
    have h₁ : Measurable (fun p : (ℝ × ℝ) × (Fin q → ℝ) => m - 1 - p.1.2) := by fun_prop
    have h₂ : Measurable (fun p : (ℝ × ℝ) × (Fin q → ℝ) => totalWait p.2) := by fun_prop
    have h₃ : Measurable (fun p : (ℝ × ℝ) × (Fin q → ℝ) => m - p.1.2) := by fun_prop
    exact ((measurableSet_lt h₁ h₂).inter (measurableSet_le h₂ h₃)).inter
      ((measurableSet_vectorLeading_joint q).preimage
        (show Measurable (fun p : (ℝ × ℝ) × (Fin q → ℝ) => (p.1.1, p.2)) by fun_prop))
  exact measurable_measure_prodMk_left (ν := positiveOrthantVolume q) hset

def overlapBallotEnvelope (j q : ℕ) (m : ℝ) :
    Set ((Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ))) :=
  {p | let S := totalWait p.1
       let A := overlapAllowance j q m S
       0 ≤ A ∧ vectorLeading A p.1 ∧
         p.2.1 ∈ ballotVectorEvent q A (Ioc (m - 1 - S) (m - S)) ∧
         p.2.2 ∈ ballotVectorEvent q A (Ioc (m - 1 - S) (m - S))}

theorem measurableSet_overlapBallotEnvelope (j q : ℕ) (m : ℝ) :
    MeasurableSet (overlapBallotEnvelope j q m) := by
  have hA : Measurable (fun p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) =>
      overlapAllowance j q m (totalWait p.1)) := by fun_prop
  have hlo : Measurable (fun p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) =>
      m - 1 - totalWait p.1) := by fun_prop
  have hhi : Measurable (fun p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) =>
      m - totalWait p.1) := by fun_prop
  have hy : Measurable (fun p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) => totalWait p.2.1) := by fun_prop
  have hz : Measurable (fun p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ)) => totalWait p.2.2) := by fun_prop
  exact (measurableSet_le measurable_const hA).inter
    (((measurableSet_vectorLeading_joint j).preimage (hA.prodMk measurable_fst)).inter
      ((((measurableSet_lt hlo hy).inter (measurableSet_le hy hhi)).inter
        ((measurableSet_vectorLeading_joint q).preimage (hA.prodMk (measurable_fst.comp measurable_snd)))).inter
        (((measurableSet_lt hlo hz).inter (measurableSet_le hz hhi)).inter
          ((measurableSet_vectorLeading_joint q).preimage (hA.prodMk (measurable_snd.comp measurable_snd))))))

theorem overlap_event_subset_envelope {j q : ℕ} (hj : 0 < j) (hq : 0 < q) (m : ℝ) :
    (@appendShared j q) ⁻¹'
      (endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m) ×ˢ
        endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m)) ⊆
      overlapBallotEnvelope j q m := by
  rintro ⟨x, y, z⟩ ⟨hy, hz⟩
  change (totalWait (Fin.append x y) ∈ Ioc (m - 1) m ∧ vectorLeading 0 (Fin.append x y)) at hy
  change (totalWait (Fin.append x z) ∈ Ioc (m - 1) m ∧ vectorLeading 0 (Fin.append x z)) at hz
  have hsumy : totalWait (Fin.append x y) = totalWait x + totalWait y := sum_append_vector x y
  have hsumz : totalWait (Fin.append x z) = totalWait x + totalWait z := sum_append_vector x z
  rw [hsumy] at hy
  rw [hsumz] at hz
  have hsy := vectorLeading_split_window hj hq hy.2 (le_of_lt hy.1.1)
  have hsz := vectorLeading_split_window hj hq hz.2 (le_of_lt hz.1.1)
  change 0 ≤ overlapAllowance j q m (totalWait x) ∧
    vectorLeading (overlapAllowance j q m (totalWait x)) x ∧
    (totalWait y ∈ Ioc (m - 1 - totalWait x) (m - totalWait x) ∧
      vectorLeading (overlapAllowance j q m (totalWait x)) y) ∧
    (totalWait z ∈ Ioc (m - 1 - totalWait x) (m - totalWait x) ∧
      vectorLeading (overlapAllowance j q m (totalWait x)) z)
  refine ⟨hsy.1, hsy.2.1, ⟨?_, hsy.2.2⟩, ⟨?_, hsz.2.2⟩⟩
  · exact ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  · exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩

theorem measure_overlapBallotEnvelope (j q : ℕ) (m : ℝ) :
    ((positiveOrthantVolume j).prod
      ((positiveOrthantVolume q).prod (positiveOrthantVolume q))) (overlapBallotEnvelope j q m) =
      ∫⁻ x, {x : Fin j → ℝ | 0 ≤ overlapAllowance j q m (totalWait x) ∧
        vectorLeading (overlapAllowance j q m (totalWait x)) x}.indicator
          (fun x => suffixBallotMass q m (overlapAllowance j q m (totalWait x)) (totalWait x) ^ 2) x
          ∂positiveOrthantVolume j := by
  rw [Measure.prod_apply (measurableSet_overlapBallotEnvelope j q m)]
  apply lintegral_congr
  intro x
  let S := totalWait x
  let A := overlapAllowance j q m S
  by_cases hp : 0 ≤ A ∧ vectorLeading A x
  · have he : Prod.mk x ⁻¹' overlapBallotEnvelope j q m =
        ballotVectorEvent q A (Ioc (m - 1 - S) (m - S)) ×ˢ
          ballotVectorEvent q A (Ioc (m - 1 - S) (m - S)) := by
      ext p
      simp only [Set.mem_preimage, overlapBallotEnvelope, Set.mem_ofPred_eq, S, A,
        hp.1, hp.2, true_and, Set.mem_prod]
    rw [he, Measure.prod_prod]
    have hmem : x ∈ {x : Fin j → ℝ | 0 ≤ overlapAllowance j q m (totalWait x) ∧
        vectorLeading (overlapAllowance j q m (totalWait x)) x} := hp
    rw [Set.indicator_of_mem hmem]
    change suffixBallotMass q m A S * suffixBallotMass q m A S = suffixBallotMass q m A S ^ 2
    exact (pow_two _).symm
  · have he : Prod.mk x ⁻¹' overlapBallotEnvelope j q m = ∅ := by
      ext p
      simp only [Set.mem_preimage, overlapBallotEnvelope, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      change (0 ≤ A ∧ vectorLeading A x ∧ _) ↔ False
      tauto
    rw [he, measure_empty]
    have hmem : x ∉ {x : Fin j → ℝ | 0 ≤ overlapAllowance j q m (totalWait x) ∧
        vectorLeading (overlapAllowance j q m (totalWait x)) x} := hp
    exact (Set.indicator_of_notMem hmem _).symm

/-- An actual shared-prefix overlap is bounded by three near-leading factors,
with both descendant endpoint windows retained exactly. -/
theorem overlapIntensity_endpointLeading_le {j q : ℕ} (hj : 0 < j) (hq : 0 < q) (m : ℝ) :
    overlapIntensity j q
      (endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m) ×ˢ
        endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m)) ≤
      ∫⁻ S in {S : ℝ | 0 ≤ S ∧ 0 ≤ overlapAllowance j q m S},
        ENNReal.ofReal (nearLeadingIntensityDensity j (overlapAllowance j q m S) S) *
          (∫⁻ U in Ioc (m - 1 - S) (m - S),
            ENNReal.ofReal (nearLeadingIntensityDensity q (overlapAllowance j q m S) U)) ^ 2 := by
  let : NeZero j := ⟨hj.ne'⟩
  let : NeZero q := ⟨hq.ne'⟩
  have hE := measurableSet_endpointLeadingVectorEvent (j + q) (J := Ioc (m - 1) m) measurableSet_Ioc
  have hfirst : overlapIntensity j q
      (endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m) ×ˢ
        endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m)) ≤
      ((positiveOrthantVolume j).prod
        ((positiveOrthantVolume q).prod (positiveOrthantVolume q))) (overlapBallotEnvelope j q m) := by
    unfold overlapIntensity
    rw [Measure.map_apply (measurable_appendShared j q) (hE.prod hE)]
    exact measure_mono (overlap_event_subset_envelope hj hq m)
  apply hfirst.trans_eq
  rw [measure_overlapBallotEnvelope]
  let A := overlapAllowance j q m
  let w : ℝ → ℝ≥0∞ := {S | 0 ≤ A S}.indicator (fun S => suffixBallotMass q m (A S) S ^ 2)
  have hmass : Measurable (fun S => suffixBallotMass q m (A S) S) :=
    (measurable_suffixBallotMass_joint q m).comp ((measurable_overlapAllowance j q m).prodMk measurable_id)
  have hw : Measurable w := (hmass.pow_const 2).indicator
    (measurableSet_le measurable_const (measurable_overlapAllowance j q m))
  have he : (fun x : Fin j → ℝ => {x | 0 ≤ A (totalWait x) ∧ vectorLeading (A (totalWait x)) x}.indicator
      (fun x => suffixBallotMass q m (A (totalWait x)) (totalWait x) ^ 2) x) =
      (fun x => {x | vectorLeading (A (totalWait x)) x}.indicator (fun x => w (totalWait x)) x) := by
    funext x
    by_cases h₁ : 0 ≤ A (totalWait x) <;> by_cases h₂ : vectorLeading (A (totalWait x)) x <;>
      simp [w, h₁, h₂]
  change (∫⁻ x, {x : Fin j → ℝ | 0 ≤ A (totalWait x) ∧ vectorLeading (A (totalWait x)) x}.indicator
      (fun x => suffixBallotMass q m (A (totalWait x)) (totalWait x) ^ 2) x ∂positiveOrthantVolume j) = _
  rw [he, lintegral_generation_leading_weighted j A (measurable_overlapAllowance j q m) w hw,
    ← lintegral_indicator (show MeasurableSet {S : ℝ | 0 ≤ S ∧ 0 ≤ overlapAllowance j q m S} from
      measurableSet_Ici.inter (measurableSet_le measurable_const (measurable_overlapAllowance j q m)))]
  apply lintegral_congr
  intro S
  by_cases hS : 0 ≤ S
  · by_cases hA : 0 ≤ A S <;>
      simp [w, A, hS, hA, suffixBallotMass_eq_lintegral]
  · have hz := nearLeadingIntensityDensity_eq_zero_of_neg j (A S) (lt_of_not_ge hS)
    simp [w, A, hS, hz]

theorem extendedOverlapIntensity_preimage_restrict (j q : ℕ)
    {E : Set (Fin (j + q) → ℝ)} (hE : MeasurableSet E) :
    extendedOverlapIntensity j q
      (((restrictSequence (j + q)) ⁻¹' E) ×ˢ ((restrictSequence (j + q)) ⁻¹' E)) =
      overlapIntensity j q (E ×ˢ E) := by
  rw [extendedOverlapIntensity_eq_map, Measure.map_apply (measurable_extendPair (j + q))
    ((hE.preimage (measurable_restrictSequence (j + q))).prod
      (hE.preimage (measurable_restrictSequence (j + q))))]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, extendPair]
  change ((fun i : Fin (j + q) => extendVector p.1 i) ∈ E ∧
    (fun i : Fin (j + q) => extendVector p.2 i) ∈ E) ↔ _
  rw [restrict_extendVector, restrict_extendVector]

theorem extendedOverlapIntensity_endpointLeading_le {j q : ℕ}
    (hj : 0 < j) (hq : 0 < q) (m : ℝ) :
    extendedOverlapIntensity j q
      (((restrictSequence (j + q)) ⁻¹'
        endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m)) ×ˢ
       ((restrictSequence (j + q)) ⁻¹'
        endpointLeadingVectorEvent (j + q) (Ioc (m - 1) m))) ≤
      ∫⁻ S in {S : ℝ | 0 ≤ S ∧ 0 ≤ overlapAllowance j q m S},
        ENNReal.ofReal (nearLeadingIntensityDensity j (overlapAllowance j q m S) S) *
          (∫⁻ U in Ioc (m - 1 - S) (m - S),
            ENNReal.ofReal (nearLeadingIntensityDensity q (overlapAllowance j q m S) U)) ^ 2 := by
  rw [extendedOverlapIntensity_preimage_restrict j q
    (measurableSet_endpointLeadingVectorEvent _ measurableSet_Ioc)]
  exact overlapIntensity_endpointLeading_le hj hq m

end FreezingGrowth.PWIT
