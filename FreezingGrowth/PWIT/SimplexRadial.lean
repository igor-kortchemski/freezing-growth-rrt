module

public import FreezingGrowth.PWIT.SimplexBridge

/-!
# The common normalized bridge of every radial spacing density

No probability normalization is required here. A density supported on the
nonnegative orthant and depending only on the total has the same normalized
bridge as iid exponentials. Its endpoint marginal retains its actual mass.
This is the interface used after summing a whole rank class, not for a fixed
rank tuple whose angular density is nonconstant.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def radialSpacingMeasure (m : ℕ) (B : ℝ → ℝ≥0∞) : Measure (Fin m → ℝ) :=
  volume.withDensity (fun x => if ∀ i, 0 ≤ x i then B (totalWait x) else 0)

instance radialSpacingMeasure_sfinite (m : ℕ) (B : ℝ → ℝ≥0∞) :
    SFinite (radialSpacingMeasure m B) := by
  unfold radialSpacingMeasure
  infer_instance

noncomputable def radialEndpointFactor (m : ℕ) (B : ℝ → ℝ≥0∞) : Measure ℝ :=
  ((Measure.volumeIoiPow (Module.finrank ℝ (SpacingSpace m) - 1)).withDensity
    (fun r => B r.val)).map Subtype.val

instance radialEndpointFactor_sfinite (m : ℕ) (B : ℝ → ℝ≥0∞) :
    SFinite (radialEndpointFactor m B) := by
  unfold radialEndpointFactor
  infer_instance

theorem radialSpacingMeasure_ae_nonnegative (m : ℕ) {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    ∀ᵐ x ∂radialSpacingMeasure m B, ∀ i, 0 ≤ x i := by
  have hD : Measurable (fun x : Fin m → ℝ => if ∀ i, 0 ≤ x i then B (totalWait x) else 0) :=
    Measurable.ite (by measurability) (by fun_prop) measurable_const
  rw [radialSpacingMeasure, ae_withDensity_iff hD]
  exact Filter.Eventually.of_forall fun x hx => by
    by_contra hn
    simp only [ite_eq_right hn, ne_eq, not_true_eq_false] at hx

theorem map_radialSpacingMeasure_spacingSpace (m : ℕ) {B : ℝ → ℝ≥0∞}
    (hB : Measurable B) :
    (radialSpacingMeasure m B).map (WithLp.toLp 1) = (spacingHaar m).withDensity
      (fun x => (nonnegativeSpacings m).indicator (fun _ => (1 : ℝ≥0∞)) x * B ‖x‖) := by
  have hD : Measurable (fun x : Fin m → ℝ => if ∀ i, 0 ≤ x i then B (totalWait x) else 0) :=
    Measurable.ite (by measurability) (by fun_prop) measurable_const
  rw [radialSpacingMeasure, ← MeasurableEquiv.coe_toLp 1 (Fin m → ℝ),
    map_withDensity_equiv _ (MeasurableEquiv.toLp 1 (Fin m → ℝ)) hD]
  change (spacingHaar m).withDensity
    (fun x => if ∀ i, 0 ≤ x.ofLp i then B (totalWait x.ofLp) else 0) = _
  congr 1
  funext x
  by_cases hx : x ∈ nonnegativeSpacings m
  · rw [Set.indicator_of_mem hx, one_mul, norm_spacing_eq_sum x hx]
    rw [ite_eq_left (show ∀ i, 0 ≤ x.ofLp i from hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, zero_mul]
    simp [nonnegativeSpacings] at hx
    simp [hx]

theorem radialSpacingMeasure_joint_factorization (m : ℕ) [NeZero m]
    {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    (radialSpacingMeasure m B).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexConeMeasure m).prod (radialEndpointFactor m B) := by
  classical
  let A : SpacingSpace m → ℝ≥0∞ := (nonnegativeSpacings m).indicator (fun _ => 1)
  have hA : Measurable A := measurable_const.indicator (measurableSet_nonnegativeSpacings m)
  have hhom (x : SpacingSpace m) (r : ℝ) (hr : 0 < r) : A (r • x) = A x := by
    have hp : r • x ∈ nonnegativeSpacings m ↔ x ∈ nonnegativeSpacings m := by
      change (∀ i, 0 ≤ r * x i) ↔ ∀ i, 0 ≤ x i
      simp only [mul_nonneg_iff_of_pos_left hr]
    change (if r • x ∈ nonnegativeSpacings m then 1 else 0) =
      if x ∈ nonnegativeSpacings m then 1 else 0
    exact if_congr hp rfl rfl
  have hp := map_polarCoordinates_radialDensity (spacingHaar m) hA hB hhom
  let U : SpacingSpace m × ℝ → (Fin m → ℝ) × ℝ := Prod.map WithLp.ofLp id
  have hU : Measurable U := by unfold U; fun_prop
  have hraw : (radialSpacingMeasure m B).map (fun x => (normalizedSpacings x, totalWait x)) =
      (((radialSpacingMeasure m B).map (WithLp.toLp 1)).map polarCoordinates).map U := by
    rw [Measure.map_map hU measurable_polarCoordinates,
      Measure.map_map (hU.comp measurable_polarCoordinates) (WithLp.measurable_toLp 1 _)]
    apply Measure.map_congr
    filter_upwards [radialSpacingMeasure_ae_nonnegative m hB] with x hx
    have hn : ‖WithLp.toLp 1 x‖ = totalWait x := norm_spacing_eq_sum _ hx
    apply Prod.ext
    · funext i
      simp [U, polarCoordinates, hn, normalizedSpacings, div_eq_mul_inv, mul_comm]
    · exact hn.symm
  rw [hraw, map_radialSpacingMeasure_spacingSpace m hB]
  change (((spacingHaar m).withDensity (fun x => A x * B ‖x‖)).map
      polarCoordinates).map U = _
  rw [hp, ← Measure.map_prod_map _ _ (WithLp.measurable_ofLp 1 _) measurable_id,
    Measure.map_map (WithLp.measurable_ofLp 1 _) measurable_subtype_coe, Measure.map_id]
  congr 1
  change ((spacingHaar m).toSphere.withDensity
      (({p | p.val ∈ nonnegativeSpacings m} : Set (Metric.sphere (0 : SpacingSpace m) 1)).indicator
        (fun _ => 1))).map (fun p => WithLp.ofLp p.val) = _
  have hset : MeasurableSet {p : Metric.sphere (0 : SpacingSpace m) 1 |
      p.val ∈ nonnegativeSpacings m} :=
    (measurableSet_nonnegativeSpacings m).preimage measurable_subtype_coe
  rw [withDensity_indicator hset]
  change (((spacingHaar m).toSphere.restrict _).withDensity 1).map _ = _
  rw [withDensity_one]
  rfl

theorem simplexLaw_eq_scaled_cone (m : ℕ) [NeZero m] :
    simplexLaw m = (spacingRadiusMeasure m) univ • simplexConeMeasure m := by
  have h := congrArg (fun ν => ν.map Prod.fst) (normalizedSpacings_joint_factorization m)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod] at h
  exact h

theorem simplexCone_radius_mass (m : ℕ) [NeZero m] :
    (spacingRadiusMeasure m) univ * (simplexConeMeasure m) univ = 1 := by
  have h := congrArg (fun ν : Measure (Fin m → ℝ) => ν univ) (simplexLaw_eq_scaled_cone m)
  simpa only [measure_univ, Measure.smul_apply, smul_eq_mul] using h.symm

/-- A complete measure-level endpoint disintegration, valid also for
unnormalized or infinite radial measures. -/
theorem radialSpacingMeasure_joint_law (m : ℕ) [NeZero m]
    {B : ℝ → ℝ≥0∞} (hB : Measurable B) :
    (radialSpacingMeasure m B).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexLaw m).prod ((radialSpacingMeasure m B).map totalWait) := by
  have hs : (radialSpacingMeasure m B).map totalWait =
      (simplexConeMeasure m) univ • radialEndpointFactor m B := by
    have h := congrArg (fun ν => ν.map Prod.snd) (radialSpacingMeasure_joint_factorization m hB)
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod] at h
    exact h
  rw [radialSpacingMeasure_joint_factorization m hB, hs, simplexLaw_eq_scaled_cone,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    simplexCone_radius_mass, one_smul]

end FreezingGrowth.PWIT
