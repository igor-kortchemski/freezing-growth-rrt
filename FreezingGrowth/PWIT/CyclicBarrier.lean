module

public import FreezingGrowth.PWIT.CyclicMinimum
import Mathlib.Tactic

/-! A soft cyclic barrier is controlled by visits near the global minimum.
This generic finite-rotation lemma does not assume a bridge law for any fixed
labelled PWIT path. Its probabilistic hypotheses must be supplied separately. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical BigOperators

section FiniteBridge

variable {d : ℕ} [NeZero d]

def softBridge (w b : Fin d → ℝ) : Prop := ∀ j, -w j ≤ b j - b 0

noncomputable def goodRotationCount (w b : Fin d → ℝ) : ℝ :=
  ∑ r : Fin d, if softBridge w (bridgeRotate r b) then 1 else 0

noncomputable def nearMinimumCount (w b : Fin d → ℝ) : ℝ :=
  ∑ r : Fin d, if b r - b 0 ≤ w r then 1 else 0

theorem bridgeRotate_comp (r s : Fin d) (b : Fin d → ℝ) :
    bridgeRotate r (bridgeRotate s b) = bridgeRotate (s + r) b := by
  funext j
  simp only [bridgeRotate]
  rw [add_assoc]
  ring

theorem softBridge_rotate_zero (w b : Fin d → ℝ) :
    softBridge w (bridgeRotate 0 b) ↔ softBridge w b := by
  simp [softBridge, bridgeRotate]

theorem goodRotationCount_rotate (w b : Fin d → ℝ) (s : Fin d) :
    goodRotationCount w (bridgeRotate s b) = goodRotationCount w b := by
  unfold goodRotationCount
  simp_rw [bridgeRotate_comp]
  exact Equiv.sum_comp (Equiv.addLeft s)
    (fun r : Fin d => if softBridge w (bridgeRotate r b) then (1 : ℝ) else 0)

theorem goodRotationCount_le_nearMinimumCount (w b : Fin d → ℝ)
    (hw : ∀ r, w (-r) = w r) : goodRotationCount w b ≤ nearMinimumCount w b := by
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : softBridge w (bridgeRotate r b)
  · have hh := hr (-r)
    simp only [bridgeRotate, add_neg_cancel, add_zero] at hh
    rw [hw] at hh
    have hn : b r - b 0 ≤ w r := by linarith
    simp [hr, hn]
  · simp only [ite_eq_right hr]
    split_ifs <;> norm_num

theorem measurableSet_softBridge {Ω : Type*} [MeasurableSpace Ω]
    (w : Fin d → ℝ) {b : Ω → Fin d → ℝ} (hb : Measurable b) :
    MeasurableSet {ω | softBridge w (b ω)} := by
  unfold softBridge
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le measurable_const
    (((measurable_pi_apply j).comp hb).sub ((measurable_pi_apply 0).comp hb))

theorem measurable_bridgeRotate (r : Fin d) :
    Measurable (bridgeRotate r : (Fin d → ℝ) → Fin d → ℝ) := by
  unfold bridgeRotate
  fun_prop

theorem goodRotationCount_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Fin d → ℝ)
    {b : Ω → Fin d → ℝ} (hb : Measurable b) :
    Integrable (fun ω => goodRotationCount w (b ω)) μ := by
  apply integrable_finsetSum
  intro r _
  have hh := (integrable_const (μ := μ) (1 : ℝ)).indicator
    (measurableSet_softBridge w ((measurable_bridgeRotate r).comp hb))
  change Integrable (fun ω => {ω | softBridge w (bridgeRotate r (b ω))}.indicator
    (fun _ => (1 : ℝ)) ω) μ at hh
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hh

theorem nearMinimumCount_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (w : Fin d → ℝ)
    {b : Ω → Fin d → ℝ} (hb : Measurable b) :
    Integrable (fun ω => nearMinimumCount w (b ω)) μ := by
  apply integrable_finsetSum
  intro r _
  have hE : MeasurableSet {ω | b ω r - b ω 0 ≤ w r} :=
    measurableSet_le (((measurable_pi_apply r).comp hb).sub
      ((measurable_pi_apply 0).comp hb)) measurable_const
  have hh := (integrable_const (μ := μ) (1 : ℝ)).indicator hE
  change Integrable (fun ω => {ω | b ω r - b ω 0 ≤ w r}.indicator
    (fun _ => (1 : ℝ)) ω) μ at hh
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hh

end FiniteBridge

theorem integral_minimum_nearMinimumCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {d : ℕ} [NeZero d]
    (b : Ω → Fin d → ℝ) (w : Fin d → ℝ) (hb : Measurable b) :
    (∫ ω, {ω | minimumAt (b ω) 0}.indicator
      (fun ω => nearMinimumCount w (b ω)) ω ∂μ) =
        ∑ r : Fin d, μ.real {ω | minimumAt (b ω) 0 ∧ b ω r - b ω 0 ≤ w r} := by
  let E (r : Fin d) : Set Ω := {ω | minimumAt (b ω) 0 ∧ b ω r - b ω 0 ≤ w r}
  have hE (r : Fin d) : MeasurableSet (E r) :=
    (measurableSet_minimumAt hb 0).inter (measurableSet_le
      (((measurable_pi_apply r).comp hb).sub ((measurable_pi_apply 0).comp hb)) measurable_const)
  have he : (fun ω => {ω | minimumAt (b ω) 0}.indicator
      (fun ω => nearMinimumCount w (b ω)) ω) =
        fun ω => ∑ r : Fin d, (E r).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases hh : minimumAt (b ω) 0
    · simp [E, nearMinimumCount, Set.indicator_apply, hh]
    · simp [E, hh]
  rw [he, integral_finsetSum _ (fun r _ => (integrable_const (μ := μ) (1 : ℝ)).indicator (hE r))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_indicator_const _ (hE r), smul_eq_mul, mul_one]

/-- The rotation-count normalization. The right side retains its leading
indicator; omitting it would lose the factor needed for a sharp ballot bound. -/
theorem softBridge_probability_le_occupancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (b : Ω → Fin d → ℝ) (w : Fin d → ℝ) (T : Fin d → Ω → Ω)
    (hb : Measurable b) (hw : ∀ r, w (-r) = w r)
    (hT : ∀ r, MeasurePreserving (T r) μ μ)
    (hbridge : ∀ r, ∀ᵐ ω ∂μ, b (T r ω) = bridgeRotate r (b ω))
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (b ω)) :
    μ.real {ω | softBridge w (b ω)} ≤
      ∫ ω, {ω | minimumAt (b ω) 0}.indicator
        (fun ω => nearMinimumCount w (b ω)) ω ∂μ := by
  let E : Set Ω := {ω | softBridge w (b ω)}
  have hE : MeasurableSet E := measurableSet_softBridge w hb
  have hrot (r : Fin d) :
      (∫ ω, (if softBridge w (bridgeRotate r (b ω)) then (1 : ℝ) else 0) ∂μ) = μ.real E := by
    have hcongr : (fun ω => if softBridge w (bridgeRotate r (b ω)) then (1 : ℝ) else 0) =ᵐ[μ]
        (fun ω => E.indicator (fun _ => (1 : ℝ)) (T r ω)) := by
      filter_upwards [hbridge r] with ω hω
      simp only [E, Set.indicator_apply, Set.mem_ofPred_eq, hω]
    rw [integral_congr_ae hcongr]
    have hm := integral_map (hT r).measurable.aemeasurable
      (show AEStronglyMeasurable (E.indicator (fun _ => (1 : ℝ))) (μ.map (T r)) from
        (hT r).map_eq.symm ▸ ((integrable_const (μ := μ) (1 : ℝ)).indicator hE).aestronglyMeasurable)
    rw [(hT r).map_eq] at hm
    have hI : (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real E := by
      rw [integral_indicator_const _ hE, smul_eq_mul, mul_one]
    exact hm.symm.trans hI
  have hcount : (∫ ω, goodRotationCount w (b ω) ∂μ) = (d : ℝ) * μ.real E := by
    unfold goodRotationCount
    rw [integral_finsetSum _ (fun r _ => by
      have hi := (integrable_const (μ := μ) (1 : ℝ)).indicator
        (measurableSet_softBridge w ((measurable_bridgeRotate r).comp hb))
      change Integrable (fun ω => {ω | softBridge w (bridgeRotate r (b ω))}.indicator
        (fun _ => (1 : ℝ)) ω) μ at hi
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hi)]
    simp only [hrot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcyclic := integral_weighted_cyclic_minimum μ b
    (fun ω => goodRotationCount w (b ω)) T hb
    (goodRotationCount_integrable μ w hb) hT
    (fun r => by
      filter_upwards [hbridge r] with ω hω
      rw [hω, goodRotationCount_rotate]) hbridge hdistinct
  have heq : μ.real E = ∫ ω, {ω | minimumAt (b ω) 0}.indicator
      (fun ω => goodRotationCount w (b ω)) ω ∂μ := by
    rw [hcount] at hcyclic
    exact (mul_left_cancel₀ (by exact_mod_cast (NeZero.ne d) : (d : ℝ) ≠ 0) hcyclic).symm
  rw [heq]
  apply integral_mono
    ((goodRotationCount_integrable μ w hb).indicator (measurableSet_minimumAt hb 0))
    ((nearMinimumCount_integrable μ w hb).indicator (measurableSet_minimumAt hb 0))
  intro ω
  by_cases hh : minimumAt (b ω) 0
  · simp only [Set.indicator_of_mem (show ω ∈ {ω | minimumAt (b ω) 0} from hh)]
    exact goodRotationCount_le_nearMinimumCount w (b ω) hw
  · simp only [Set.indicator_of_notMem (show ω ∉ {ω | minimumAt (b ω) 0} from hh), le_refl]

end FreezingGrowth.PWIT
