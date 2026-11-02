module

public import FreezingGrowth.PWIT.Erlang
public import FreezingGrowth.PWIT.SimplexPolar
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Normalized exponential spacings and their endpoint

The simplex law is the actual normalized finite product of exponential clocks.
The total is almost surely positive in positive dimension. Polar coordinates
in the `ℓ¹` norm separate the normalized vector from its Gamma endpoint; this
avoids conditioning on a singleton of measure zero.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

abbrev SpacingSpace (m : ℕ) := PiLp 1 (fun _ : Fin m => ℝ)

noncomputable def spacingHaar (m : ℕ) : Measure (SpacingSpace m) :=
  (volume : Measure (Fin m → ℝ)).map (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin m => ℝ)).symm

instance spacingHaar_isAddHaarMeasure (m : ℕ) : (spacingHaar m).IsAddHaarMeasure := by
  unfold spacingHaar
  infer_instance

def nonnegativeSpacings (m : ℕ) : Set (SpacingSpace m) := {x | ∀ i, 0 ≤ x i}

theorem measurableSet_nonnegativeSpacings (m : ℕ) : MeasurableSet (nonnegativeSpacings m) := by
  unfold nonnegativeSpacings
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 1 _))

theorem norm_spacing_eq_sum {m : ℕ} (x : SpacingSpace m) (hx : x ∈ nonnegativeSpacings m) :
    ‖x‖ = ∑ i, x i := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
  exact Finset.sum_congr rfl fun i _ => Real.norm_of_nonneg (hx i)

noncomputable def finiteClockLaw (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ => clockLaw

instance finiteClockLaw_isProbabilityMeasure (m : ℕ) : IsProbabilityMeasure (finiteClockLaw m) := by
  unfold finiteClockLaw
  infer_instance

def totalWait {m : ℕ} (x : Fin m → ℝ) : ℝ := ∑ i, x i

noncomputable def normalizedSpacings {m : ℕ} (x : Fin m → ℝ) : Fin m → ℝ :=
  fun i => x i / totalWait x

@[fun_prop] theorem measurable_totalWait (m : ℕ) : Measurable (@totalWait m) := by
  unfold totalWait
  fun_prop

@[fun_prop] theorem measurable_normalizedSpacings (m : ℕ) :
    Measurable (@normalizedSpacings m) := by
  unfold normalizedSpacings
  fun_prop

theorem totalWait_smul {m : ℕ} (c : ℝ) (x : Fin m → ℝ) :
    totalWait (c • x) = c * totalWait x := by
  simp only [totalWait, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem normalizedSpacings_smul {m : ℕ} {c : ℝ} (hc : c ≠ 0) (x : Fin m → ℝ) :
    normalizedSpacings (c • x) = normalizedSpacings x := by
  funext i
  simp only [normalizedSpacings, totalWait_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left (x i) (totalWait x) hc

theorem reconstruct_normalizedSpacings {m : ℕ} (x : Fin m → ℝ) (hx : totalWait x ≠ 0) :
    totalWait x • normalizedSpacings x = x := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, normalizedSpacings]
  field_simp

noncomputable def simplexLaw (m : ℕ) : Measure (Fin m → ℝ) :=
  (finiteClockLaw m).map normalizedSpacings

instance simplexLaw_isProbabilityMeasure (m : ℕ) : IsProbabilityMeasure (simplexLaw m) := by
  unfold simplexLaw
  infer_instance

theorem finiteClockLaw_ae_pos (m : ℕ) : ∀ᵐ x ∂finiteClockLaw m, ∀ i, 0 < x i := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin m => clockLaw) i).quasiMeasurePreserving.ae
    clockLaw_ae_pos

theorem finiteClockLaw_ae_total_pos (m : ℕ) [NeZero m] :
    ∀ᵐ x ∂finiteClockLaw m, 0 < totalWait x := by
  filter_upwards [finiteClockLaw_ae_pos m] with x hx
  exact Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty

theorem simplexLaw_ae_nonnegative_sum_one (m : ℕ) [NeZero m] :
    ∀ᵐ p ∂simplexLaw m, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
  rw [simplexLaw, ae_map_iff (measurable_normalizedSpacings m).aemeasurable
    (by measurability)]
  filter_upwards [finiteClockLaw_ae_pos m, finiteClockLaw_ae_total_pos m] with x hx hs
  constructor
  · exact fun i => div_nonneg (hx i).le hs.le
  · change (∑ i, x i / totalWait x) = 1
    rw [← Finset.sum_div]
    exact div_self hs.ne'

theorem map_totalWait_gamma (m : ℕ) [NeZero m] :
    (finiteClockLaw m).map totalWait = gammaMeasure (m : ℝ) 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  unfold finiteClockLaw totalWait
  rw [← map_clockSum_finite_sum, map_clockSum_succ]
  norm_num

private theorem product_erlang_zero {m : ℕ} (x : Fin m → ℝ) :
    (∏ i, erlangPDF 0 (x i)) =
      if ∀ i, 0 ≤ x i then ENNReal.ofReal (Real.exp (-totalWait x)) else 0 := by
  classical
  split_ifs with hx
  · simp only [erlangPDF, hx, ite_true, pow_zero, one_mul, Nat.factorial_zero,
      Nat.cast_one, div_one]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← Real.exp_sum]
    simp only [totalWait, Finset.sum_neg_distrib]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [erlangPDF, hi]

theorem finiteClockLaw_density (m : ℕ) :
    finiteClockLaw m = (volume : Measure (Fin m → ℝ)).withDensity
      (fun x => if ∀ i, 0 ≤ x i then ENNReal.ofReal (Real.exp (-totalWait x)) else 0) := by
  have he : clockLaw = volume.withDensity (erlangPDF 0) := by
    unfold clockLaw expMeasure gammaMeasure
    congr 1
    funext x
    simpa using gammaPDF_nat_succ 0 x
  simp only [finiteClockLaw, he]
  rw [finitePi_withDensity (fun _ => volume) (fun _ => erlangPDF 0)
    (fun _ => measurable_erlangPDF 0) (by intro i x; simp [erlangPDF]; split <;> simp)]
  congr 1
  funext x
  exact product_erlang_zero x

theorem map_finiteClockLaw_spacingSpace (m : ℕ) :
    (finiteClockLaw m).map (WithLp.toLp 1) = (spacingHaar m).withDensity
      (fun x => (nonnegativeSpacings m).indicator (fun _ => (1 : ℝ≥0∞)) x *
        ENNReal.ofReal (Real.exp (-‖x‖))) := by
  rw [finiteClockLaw_density, ← MeasurableEquiv.coe_toLp 1 (Fin m → ℝ),
    map_withDensity_equiv _ (MeasurableEquiv.toLp 1 (Fin m → ℝ))
      (Measurable.ite (by measurability) (by fun_prop) measurable_const)]
  change (spacingHaar m).withDensity
    (fun x => if ∀ i, 0 ≤ x.ofLp i then ENNReal.ofReal (Real.exp (-totalWait x.ofLp)) else 0) = _
  congr 1
  funext x
  by_cases hx : x ∈ nonnegativeSpacings m
  · rw [Set.indicator_of_mem hx, one_mul, norm_spacing_eq_sum x hx]
    rw [ite_eq_left (show ∀ i, 0 ≤ x.ofLp i from hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, zero_mul]
    simp [nonnegativeSpacings] at hx
    simp [hx]

/-- The unnormalized angular factor; its normalization is fixed by the actual
exponential probability law, rather than an assumed simplex-volume formula. -/
noncomputable def simplexConeMeasure (m : ℕ) : Measure (Fin m → ℝ) :=
  (((spacingHaar m).toSphere).restrict
    {p | p.val ∈ nonnegativeSpacings m}).map (fun p => WithLp.ofLp p.val)

noncomputable def spacingRadiusMeasure (m : ℕ) : Measure ℝ :=
  ((Measure.volumeIoiPow (Module.finrank ℝ (SpacingSpace m) - 1)).withDensity
    (fun r => ENNReal.ofReal (Real.exp (-r.val)))).map Subtype.val

instance simplexConeMeasure_isFiniteMeasure (m : ℕ) : IsFiniteMeasure (simplexConeMeasure m) := by
  unfold simplexConeMeasure
  infer_instance

instance spacingRadiusMeasure_sfinite (m : ℕ) : SFinite (spacingRadiusMeasure m) := by
  unfold spacingRadiusMeasure
  infer_instance

theorem normalizedSpacings_joint_factorization (m : ℕ) [NeZero m] :
    (finiteClockLaw m).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexConeMeasure m).prod (spacingRadiusMeasure m) := by
  classical
  let A : SpacingSpace m → ℝ≥0∞ := (nonnegativeSpacings m).indicator (fun _ => 1)
  let B : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-r))
  have hA : Measurable A := measurable_const.indicator (measurableSet_nonnegativeSpacings m)
  have hB : Measurable B := by unfold B; fun_prop
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
  have hraw : (finiteClockLaw m).map (fun x => (normalizedSpacings x, totalWait x)) =
      (((finiteClockLaw m).map (WithLp.toLp 1)).map polarCoordinates).map U := by
    rw [Measure.map_map hU measurable_polarCoordinates,
      Measure.map_map (hU.comp measurable_polarCoordinates) (WithLp.measurable_toLp 1 _)]
    apply Measure.map_congr
    filter_upwards [finiteClockLaw_ae_pos m] with x hx
    have hn : ‖WithLp.toLp 1 x‖ = totalWait x :=
      norm_spacing_eq_sum _ (fun i => (hx i).le)
    apply Prod.ext
    · funext i
      simp [U, polarCoordinates, hn, normalizedSpacings, div_eq_mul_inv, mul_comm]
    · exact hn.symm
  rw [hraw, map_finiteClockLaw_spacingSpace]
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

/-- Exact endpoint disintegration of iid exponential spacings. -/
theorem normalizedSpacings_joint_law (m : ℕ) [NeZero m] :
    (finiteClockLaw m).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexLaw m).prod (gammaMeasure (m : ℝ) 1) := by
  let J := (finiteClockLaw m).map (fun x => (normalizedSpacings x, totalWait x))
  have hJ : J = (simplexConeMeasure m).prod (spacingRadiusMeasure m) :=
    normalizedSpacings_joint_factorization m
  have : IsProbabilityMeasure J := by dsimp only [J]; infer_instance
  have : IsProbabilityMeasure ((simplexConeMeasure m).prod (spacingRadiusMeasure m)) := by
    rw [← hJ]
    infer_instance
  have hf : J.map Prod.fst = simplexLaw m := by
    dsimp only [J]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    rfl
  have hs : J.map Prod.snd = gammaMeasure (m : ℝ) 1 := by
    dsimp only [J]
    rw [Measure.map_map measurable_snd (by fun_prop)]
    exact map_totalWait_gamma m
  change J = _
  calc
    J = (J.map Prod.fst).prod (J.map Prod.snd) := by
      rw [hJ]
      exact prod_eq_prod_marginals _ _
    _ = _ := by rw [hf, hs]

theorem normalizedSpacings_independent_total (m : ℕ) [NeZero m] :
    IndepFun (@normalizedSpacings m) totalWait (finiteClockLaw m) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_normalizedSpacings m).aemeasurable
    (measurable_totalWait m).aemeasurable).mpr
  rw [map_totalWait_gamma]
  exact normalizedSpacings_joint_law m

/-- Sampling an independent simplex vector and Gamma endpoint, then scaling,
recovers the actual iid exponential product law. -/
theorem finiteClockLaw_eq_scaled_simplex_gamma (m : ℕ) [NeZero m] :
    finiteClockLaw m = ((simplexLaw m).prod (gammaMeasure (m : ℝ) 1)).map
      (fun z => z.2 • z.1) := by
  have hrec : (fun x : Fin m → ℝ => totalWait x • normalizedSpacings x) =ᵐ[finiteClockLaw m] id := by
    filter_upwards [finiteClockLaw_ae_total_pos m] with x hx
    exact reconstruct_normalizedSpacings x hx.ne'
  rw [← normalizedSpacings_joint_law m,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact (Measure.map_congr hrec).trans (Measure.map_id) |>.symm

end FreezingGrowth.PWIT
