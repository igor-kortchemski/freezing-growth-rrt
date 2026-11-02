module

public import FreezingGrowth.PWIT.SimplexBridge

/-!
# Grouping normalized exponential waits

A sum-preserving linear grouping of the individual waits preserves endpoint
independence. In particular, grouping the waits into child-rank blocks gives
the normalized edge-increment bridge of a fixed path.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory

theorem normalizedSpacings_eq_inv_smul {m : ℕ} (x : Fin m → ℝ) :
    normalizedSpacings x = (totalWait x)⁻¹ • x := by
  funext i
  simp only [normalizedSpacings, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem normalizedSpacings_linear {N d : ℕ}
    (G : (Fin N → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hG : ∀ x, totalWait (G x) = totalWait x) (x : Fin N → ℝ) :
    normalizedSpacings (G x) = G (normalizedSpacings x) := by
  rw [normalizedSpacings_eq_inv_smul, hG, normalizedSpacings_eq_inv_smul, G.map_smul]

theorem normalizedSpacings_linear_joint_law (N d : ℕ) [NeZero N]
    (G : (Fin N → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hG : ∀ x, totalWait (G x) = totalWait x) :
    (finiteClockLaw N).map (fun x => (normalizedSpacings (G x), totalWait x)) =
      ((simplexLaw N).map G).prod (gammaMeasure (N : ℝ) 1) := by
  have : IsProbabilityMeasure (gammaMeasure (N : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos N)) (by norm_num)
  have hm : Measurable G := G.continuous_of_finiteDimensional.measurable
  calc
    _ = ((finiteClockLaw N).map (fun x => (normalizedSpacings x, totalWait x))).map
        (Prod.map G id) := by
      rw [Measure.map_map (hm.prodMap measurable_id) (by fun_prop)]
      congr 1
      funext x
      apply Prod.ext
      · exact normalizedSpacings_linear G hG x
      · rfl
    _ = _ := by
      rw [normalizedSpacings_joint_law,
        ← Measure.map_prod_map _ _ hm measurable_id, Measure.map_id]

end FreezingGrowth.PWIT
