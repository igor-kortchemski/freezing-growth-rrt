module

public import FreezingGrowth.PWIT.HeightEquation
public import FreezingGrowth.RRTGeometricRenewal
public import FreezingGrowth.RenewalUniqueness

/-! Identification of actual clock birth events with the geometric RRT mixture. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set
open scoped NNReal

/-- The two actual height CDFs satisfy the same first-birth equation.
This is a law identity, without constructing a chronological infinite tree. -/
theorem heightCDF_eq_geometricCdf (h : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    heightCDF h t = RRT.geometricCdf h t := by
  induction h generalizing t with
  | zero => rw [heightCDF_zero_height ht, RRT.geometricCdf_zero]
  | succ h ih =>
    have he : EqOn (heightCDF (h + 1)) (RRT.geometricCdf (h + 1)) (Ici 0) := by
      apply scalar_renewal_unique
        ((measurable_heightCDF (h + 1)).aestronglyMeasurable.restrict)
        ((RRT.geometricCdf_continuousOn (h + 1)).aestronglyMeasurable measurableSet_Ici)
        ((RRT.geometricCdf_continuousOn h).aestronglyMeasurable measurableSet_Ici)
        (fun u _ => ⟨heightCDF_nonneg _ _, heightCDF_le_one _ _⟩)
        (fun u hu => ⟨RRT.geometricCdf_nonneg _ hu, RRT.geometricCdf_le_one _ hu⟩)
        (fun u hu => ⟨RRT.geometricCdf_nonneg _ hu, RRT.geometricCdf_le_one _ hu⟩)
      · intro u hu
        rw [heightCDF_renewal_integratingFactor h hu]
        have hint :
            (∫ v in (0 : ℝ)..u, Real.exp v * heightCDF (h + 1) v * heightCDF h v) =
              ∫ v in (0 : ℝ)..u,
                Real.exp v * heightCDF (h + 1) v * RRT.geometricCdf h v := by
          apply intervalIntegral.integral_congr
          intro v hv
          have hv0 : 0 ≤ v := (show v ∈ Icc 0 u by
            simpa only [uIcc_of_le hu] using hv).1
          dsimp only
          rw [ih hv0]
        rw [hint]
        ring
      · intro u hu
        rw [RRT.geometricCdf_renewal_integratingFactor h hu]
        ring
    exact he ht

/-- A path of length `d` born by time `t` is exactly the geometric-mixture
height upper-tail event in distribution. The geometric index counts edges. -/
theorem reaches_probability_eq_geometric_tail (t : ℝ≥0) (d : ℕ) (hd : 0 < d) :
    law.real (reaches d (t : ℝ)) =
      (RRT.geometricHeightLaw t).real {h | d ≤ h} := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [RRT.geometricHeightLaw_tail_eq_one_sub_cdf,
    ← heightCDF_eq_geometricCdf h t.coe_nonneg, heightCDF,
    measureReal_compl (measurableSet_reaches _ _), probReal_univ]
  ring

end FreezingGrowth.PWIT
