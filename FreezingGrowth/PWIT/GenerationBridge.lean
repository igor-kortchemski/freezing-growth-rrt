module

public import FreezingGrowth.PWIT.SimplexRadial
public import FreezingGrowth.PWIT.Erlang

/-! Exact normalized-vector/endpoint disintegration of Lebesgue generation
intensity. Positive dimension is essential; the root has endpoint Dirac zero. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable def generationEndpointDensity (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  if 0 ≤ s then ENNReal.ofReal (s ^ (d - 1) / (d - 1).factorial) else 0

@[fun_prop] theorem measurable_generationEndpointDensity (d : ℕ) :
    Measurable (generationEndpointDensity d) := by
  unfold generationEndpointDensity
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

noncomputable def generationEndpointMeasure (d : ℕ) : Measure ℝ :=
  volume.withDensity (generationEndpointDensity d)

instance generationEndpointMeasure_sfinite (d : ℕ) : SFinite (generationEndpointMeasure d) := by
  unfold generationEndpointMeasure
  infer_instance

instance generationEndpointMeasure_nullSingleton (d : ℕ) :
    NullSingletonClass (generationEndpointMeasure d) := by
  unfold generationEndpointMeasure
  infer_instance

theorem radialSpacingMeasure_one_eq_restrict (d : ℕ) :
    radialSpacingMeasure d (fun _ => 1) = volume.restrict {x | ∀ i, 0 ≤ x i} := by
  unfold radialSpacingMeasure
  calc
    _ = volume.withDensity ({x : Fin d → ℝ | ∀ i, 0 ≤ x i}.indicator 1) := by
      congr 1
      funext x
      by_cases hx : ∀ i, 0 ≤ x i <;> simp [hx]
    _ = _ := withDensity_indicator_one (by measurability)

theorem radialSpacingMeasure_one_eq_pi (d : ℕ) :
    radialSpacingMeasure d (fun _ => 1) =
      Measure.pi (fun _ : Fin d => volume.restrict (Ici (0 : ℝ))) := by
  rw [radialSpacingMeasure_one_eq_restrict]
  have hset : {x : Fin d → ℝ | ∀ i, 0 ≤ x i} =
      Set.univ.pi (fun _ : Fin d => Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_pi.mpr (fun i _ => hx i)
    · intro hx i
      exact Set.mem_pi.mp hx i (Set.mem_univ i)
  rw [hset, volume_pi, Measure.restrict_pi_pi]

/-- Tilting the actual iid exponential law recovers unnormalized Lebesgue
intensity. This identity is valid also in dimension zero. -/
theorem finiteClockLaw_tilt_total (d : ℕ) :
    (finiteClockLaw d).withDensity (fun x => ENNReal.ofReal (Real.exp (totalWait x))) =
      radialSpacingMeasure d (fun _ => 1) := by
  have hD : Measurable (fun x : Fin d → ℝ =>
      if ∀ i, 0 ≤ x i then ENNReal.ofReal (Real.exp (-totalWait x)) else 0) := by
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  rw [finiteClockLaw_density, ← withDensity_mul volume hD (by fun_prop)]
  unfold radialSpacingMeasure
  congr 1
  funext x
  change (if ∀ i, 0 ≤ x i then ENNReal.ofReal (Real.exp (-totalWait x)) else 0) *
    ENNReal.ofReal (Real.exp (totalWait x)) = if ∀ i, 0 ≤ x i then 1 else 0
  by_cases hx : ∀ i, 0 ≤ x i
  · rw [ite_eq_left hx, ite_eq_left hx, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    simp
  · simp [hx]

theorem gammaMeasure_tilt_exp (d : ℕ) [NeZero d] :
    (gammaMeasure (d : ℝ) 1).withDensity (fun s => ENNReal.ofReal (Real.exp s)) =
      generationEndpointMeasure d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hpdf : Measurable (gammaPDF ((k + 1 : ℕ) : ℝ) 1) :=
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [gammaMeasure, ← withDensity_mul volume hpdf (by fun_prop)]
  unfold generationEndpointMeasure
  congr 1
  funext s
  change gammaPDF ((k + 1 : ℕ) : ℝ) 1 s * ENNReal.ofReal (Real.exp s) =
    generationEndpointDensity (k + 1) s
  rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring, gammaPDF_nat_succ]
  by_cases hs : 0 ≤ s
  · simp only [erlangPDF, generationEndpointDensity, ite_eq_left hs, Nat.add_sub_cancel]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have he : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
    calc
      _ = (s ^ k / (k.factorial : ℝ)) * (Real.exp (-s) * Real.exp s) := by ring
      _ = _ := by rw [he, mul_one]
  · simp [erlangPDF, generationEndpointDensity, hs]

theorem radialSpacingMeasure_one_endpoint (d : ℕ) [NeZero d] :
    (radialSpacingMeasure d (fun _ => 1)).map totalWait = generationEndpointMeasure d := by
  rw [← finiteClockLaw_tilt_total]
  rw [map_withDensity_comp (finiteClockLaw d) (T := @totalWait d) (measurable_totalWait d)
    (f := fun s : ℝ => ENNReal.ofReal (Real.exp s)) (by fun_prop),
    map_totalWait_gamma, gammaMeasure_tilt_exp]

/-- Complete endpoint disintegration of the actual generation intensity,
without normalizing its infinite total mass. -/
theorem generationSpacing_joint_law (d : ℕ) [NeZero d] :
    (radialSpacingMeasure d (fun _ => 1)).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexLaw d).prod (generationEndpointMeasure d) := by
  rw [radialSpacingMeasure_joint_law d measurable_const, radialSpacingMeasure_one_endpoint]

theorem radialSpacingMeasure_one_ae_total_ne_zero (d : ℕ) [NeZero d] :
    ∀ᵐ x ∂radialSpacingMeasure d (fun _ => 1), totalWait x ≠ 0 := by
  have ha : ∀ᵐ s ∂(radialSpacingMeasure d (fun _ => 1)).map totalWait, s ≠ 0 := by
    rw [radialSpacingMeasure_one_endpoint]
    exact (generationEndpointMeasure d).ae_ne 0
  exact ae_of_ae_map (measurable_totalWait d).aemeasurable ha

/-- Reconstructing from independent simplex angle and the actual unnormalized
endpoint measure recovers the entire generation intensity. -/
theorem generationSpacing_eq_scaled_simplex (d : ℕ) [NeZero d] :
    radialSpacingMeasure d (fun _ => 1) =
      ((simplexLaw d).prod (generationEndpointMeasure d)).map (fun z => z.2 • z.1) := by
  have hrec : (fun x : Fin d → ℝ => totalWait x • normalizedSpacings x)
      =ᵐ[radialSpacingMeasure d (fun _ => 1)] id := by
    filter_upwards [radialSpacingMeasure_one_ae_total_ne_zero d] with x hx
    exact reconstruct_normalizedSpacings x hx
  rw [← generationSpacing_joint_law d,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact (Measure.map_congr hrec).trans Measure.map_id |>.symm

end FreezingGrowth.PWIT
