module

public import FreezingGrowth.PWIT.SimplexDensity
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Separating homogeneous angular weights from radial densities

The generalized polar-coordinate theorem applies to every finite-dimensional
norm. In the positive orthant of the `ℓ¹` space its radius is the sum of the
coordinates, hence the endpoint of an exponential path. The angular measure
retains the Haar normalization; no sphere-volume constant is discarded.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

noncomputable def polarCoordinates (x : E) : E × ℝ := (‖x‖⁻¹ • x, ‖x‖)

omit [Nontrivial E] in
@[fun_prop] theorem measurable_polarCoordinates : Measurable (polarCoordinates (E := E)) := by
  unfold polarCoordinates
  fun_prop

set_option backward.isDefEq.respectTransparency false in
theorem map_polarCoordinates_radialDensity (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : E → ℝ≥0∞} {B : ℝ → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B)
    (hhom : ∀ (x : E) (r : ℝ), 0 < r → A (r • x) = A x) :
    (μ.withDensity (fun x => A x * B ‖x‖)).map polarCoordinates =
      ((μ.toSphere.withDensity (fun x => A x.val)).map Subtype.val).prod
        (((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (fun r => B r.val)).map Subtype.val) := by
  let e := homeomorphUnitSphereProd E
  let μ₀ : Measure ({0}ᶜ : Set E) := μ.comap Subtype.val
  let T : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) → E × ℝ :=
    Prod.map Subtype.val Subtype.val
  have hT : Measurable T := by unfold T; fun_prop
  have hbase : μ₀.map Subtype.val = μ := by
    dsimp only [μ₀]
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl,
      restrict_compl_singleton]
  have hcoord : (fun x : ({0}ᶜ : Set E) => polarCoordinates x.val) = T ∘ e := by
    funext x
    apply Prod.ext
    · exact (homeomorphUnitSphereProd_apply_fst_coe E x).symm
    · exact (homeomorphUnitSphereProd_apply_snd_coe E x).symm
  have hweight : (fun x : ({0}ᶜ : Set E) => A x.val * B ‖x.val‖) =
      (fun x => A (e x).1.val * B (e x).2.val) := by
    funext x
    have hx : (x : E) ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
    simp only [e, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe]
    rw [hhom _ _ (inv_pos.mpr (norm_pos_iff.mpr hx))]
  calc
    _ = ((μ₀.withDensity (fun x => A x.val * B ‖x.val‖)).map Subtype.val).map
        polarCoordinates := by
          rw [map_withDensity_comp μ₀ measurable_subtype_coe
            (f := fun x : E => A x * B ‖x‖) (by fun_prop),
            hbase]
    _ = (μ₀.withDensity (fun x => A (e x).1.val * B (e x).2.val)).map (T ∘ e) := by
          rw [Measure.map_map measurable_polarCoordinates measurable_subtype_coe, hweight]
          rw [show polarCoordinates ∘ (Subtype.val : ({0}ᶜ : Set E) → E) = T ∘ e from hcoord]
    _ = (((μ.toSphere).prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).withDensity
        (fun z => A z.1.val * B z.2.val)).map T := by
          rw [← Measure.map_map hT e.measurable,
            map_withDensity_comp μ₀ e.measurable
              (f := fun z => A z.1.val * B z.2.val) (by fun_prop),
            μ.measurePreserving_homeomorphUnitSphereProd.map_eq]
    _ = _ := by
          rw [← prod_withDensity (μ := μ.toSphere)
            (ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1))
            (f := fun x : Metric.sphere (0 : E) 1 => A x.val)
            (g := fun r : Ioi (0 : ℝ) => B r.val) (by fun_prop) (by fun_prop)]
          exact (Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe).symm

end FreezingGrowth.PWIT
