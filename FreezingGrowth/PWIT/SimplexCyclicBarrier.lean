module

public import FreezingGrowth.PWIT.CyclicBarrier
public import FreezingGrowth.PWIT.SimplexLeading
public import FreezingGrowth.PWIT.SimplexLinear

/-! Rotation and no-tie hypotheses for the actual normalized exponential
bridge. No ambient absolute continuity of the singular simplex law is used:
no ties transfer from the raw clock vector by its positive total scaling. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Filter

variable {d : ℕ} [NeZero d]

theorem centeredBridge_smul (c : ℝ) (x : Fin d → ℝ) :
    centeredBridge (c • x) = c • centeredBridge x := by
  funext i
  exact (centeredBridgeLinear i).map_smul c x

theorem totalWait_rotateIncrements (r : Fin d) (x : Fin d → ℝ) :
    totalWait (rotateIncrements r x) = totalWait x := sum_rotateIncrements r x

theorem normalizedSpacings_rotateIncrements (r : Fin d) (x : Fin d → ℝ) :
    normalizedSpacings (rotateIncrements r x) = rotateIncrements r (normalizedSpacings x) := by
  funext i
  simp only [normalizedSpacings, totalWait_rotateIncrements, rotateIncrements]

theorem simplexLaw_rotateIncrements (r : Fin d) :
    (simplexLaw d).map (rotateIncrements r) = simplexLaw d := by
  have hp : MeasurePreserving (rotateIncrements r) (finiteClockLaw d) (finiteClockLaw d) := by
    simpa only [rankIncrementMeasure_zero_eq_finiteClockLaw] using rotateIncrements_preserving 0 r
  have he : rotateIncrements r ∘ normalizedSpacings =
      normalizedSpacings ∘ rotateIncrements r := by
    funext x
    exact (normalizedSpacings_rotateIncrements r x).symm
  unfold simplexLaw
  rw [Measure.map_map (measurable_rotateIncrements r) (measurable_normalizedSpacings d), he,
    ← Measure.map_map (measurable_normalizedSpacings d) (measurable_rotateIncrements r), hp.map_eq]

theorem simplexLaw_rotateIncrements_preserving (r : Fin d) :
    MeasurePreserving (rotateIncrements r) (simplexLaw d) (simplexLaw d) :=
  ⟨measurable_rotateIncrements r, simplexLaw_rotateIncrements r⟩

theorem simplexLaw_ae_centeredBridge_injective :
    ∀ᵐ p ∂simplexLaw d, Function.Injective (centeredBridge p) := by
  have hP : MeasurableSet {x : Fin d → ℝ | Function.Injective (centeredBridge x)} := by
    simp only [Function.Injective, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp [hij]
    · convert (measurableSet_eq_fun
        ((measurable_pi_apply i).comp measurable_centeredBridge)
        ((measurable_pi_apply j).comp measurable_centeredBridge)).compl using 1
      ext x
      simp [hij]
  unfold simplexLaw
  rw [ae_map_iff (measurable_normalizedSpacings d).aemeasurable hP]
  have hraw : ∀ᵐ x ∂finiteClockLaw d, Function.Injective (centeredBridge x) := by
    simpa only [rankIncrementMeasure_zero_eq_finiteClockLaw] using ae_centeredBridge_injective (d := d) 0
  filter_upwards [hraw, finiteClockLaw_ae_total_pos d] with x hx ht
  rw [normalizedSpacings_eq_inv_smul, centeredBridge_smul]
  intro i j hij
  apply hx
  exact mul_left_cancel₀ (inv_ne_zero ht.ne') hij

/-- Centered partial sums for the canonical bridge with total equal to its
number of increments. On the simplex support its value at `k` is `d*S_k-k`. -/
noncomputable def simplexCenteredBridge (p : Fin d → ℝ) : Fin d → ℝ :=
  centeredBridge ((d : ℝ) • p)

@[fun_prop] theorem measurable_simplexCenteredBridge :
    Measurable (@simplexCenteredBridge d _) :=
  measurable_centeredBridge.comp (by fun_prop)

theorem simplexCenteredBridge_rotate (r : Fin d) (p : Fin d → ℝ) :
    simplexCenteredBridge (rotateIncrements r p) = bridgeRotate r (simplexCenteredBridge p) := by
  have hs : (d : ℝ) • rotateIncrements r p = rotateIncrements r ((d : ℝ) • p) := by
    funext i
    rfl
  unfold simplexCenteredBridge
  rw [hs, centeredBridge_rotate]

theorem simplexLaw_ae_simplexCenteredBridge_injective :
    ∀ᵐ p ∂simplexLaw d, Function.Injective (simplexCenteredBridge p) := by
  filter_upwards [simplexLaw_ae_centeredBridge_injective (d := d)] with p hp
  unfold simplexCenteredBridge
  rw [centeredBridge_smul]
  intro i j hij
  apply hp
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d) : (d : ℝ) ≠ 0) hij

/-- The generic occupancy reduction on the actual canonical simplex law. -/
theorem simplex_softBridge_probability_le_occupancy (w : Fin d → ℝ)
    (hw : ∀ r, w (-r) = w r) :
    (simplexLaw d).real {p | softBridge w (simplexCenteredBridge p)} ≤
      ∫ p, {p | minimumAt (simplexCenteredBridge p) 0}.indicator
        (fun p => nearMinimumCount w (simplexCenteredBridge p)) p ∂simplexLaw d := by
  apply softBridge_probability_le_occupancy (simplexLaw d) simplexCenteredBridge w rotateIncrements
    measurable_simplexCenteredBridge hw simplexLaw_rotateIncrements_preserving
    (fun r => Eventually.of_forall (simplexCenteredBridge_rotate r))
  exact simplexLaw_ae_simplexCenteredBridge_injective

theorem simplex_softBridge_probability_le_sum (w : Fin d → ℝ)
    (hw : ∀ r, w (-r) = w r) :
    (simplexLaw d).real {p | softBridge w (simplexCenteredBridge p)} ≤
      ∑ r : Fin d, (simplexLaw d).real
        {p | minimumAt (simplexCenteredBridge p) 0 ∧
          simplexCenteredBridge p r - simplexCenteredBridge p 0 ≤ w r} := by
  apply (simplex_softBridge_probability_le_occupancy w hw).trans_eq
  exact integral_minimum_nearMinimumCount (simplexLaw d) simplexCenteredBridge w
    measurable_simplexCenteredBridge

end FreezingGrowth.PWIT
