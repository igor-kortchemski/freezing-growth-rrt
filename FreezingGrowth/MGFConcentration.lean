module

/- Adapted from the local freezing1 companion project (Apache-2.0).
   The source and snapshot hash are recorded in NOTICE. -/

public import FreezingGrowth.BernoulliConcentration

/-!
# Bennett tails from a proved moment-generating-function estimate

This analytic lemma applies to the actual forward law once its exponential
integrability and MGF estimate have been proved. It assumes no tree limit or
Bernoulli representation.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {m : ℝ}

/-- Both Bennett tails follow from the full Poisson-type MGF upper bound. -/
theorem bennett_tails_of_mgf_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (h_mgf : ∀ θ, mgf X μ θ ≤ Real.exp (m * (Real.exp θ - 1)))
    (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | m + t < X ω} ≤ Real.exp (-m * bennettRate (t / m)) ∧
    μ.real {ω | X ω < m - t} ≤ Real.exp (-m * bennettRate (t / m)) := by
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by have := div_pos ht hm; linarith)
  constructor
  · calc
      μ.real {ω | m + t < X ω} ≤ μ.real {ω | m + t ≤ X ω} :=
        measureReal_mono (by
          intro ω hω
          change m + t < X ω at hω
          change m + t ≤ X ω
          exact hω.le) (measure_ne_top μ _)
      _ ≤ Real.exp (-θ * (m + t)) * mgf X μ θ :=
        measure_ge_le_exp_mul_mgf (m + t) hθ (h_int θ)
      _ ≤ Real.exp (-θ * (m + t)) * Real.exp (m * (Real.exp θ - 1)) :=
        mul_le_mul_of_nonneg_left (h_mgf θ) (Real.exp_pos _).le
      _ = Real.exp (-m * bennettRate (t / m)) := by
        rw [← Real.exp_add]
        congr 1
        exact bennett_exponent_identity hm ht
  · calc
      μ.real {ω | X ω < m - t} ≤ μ.real {ω | X ω ≤ m - t} :=
        measureReal_mono (by
          intro ω hω
          change X ω < m - t at hω
          change X ω ≤ m - t
          exact hω.le) (measure_ne_top μ _)
      _ ≤ Real.exp (-(-θ) * (m - t)) * mgf X μ (-θ) :=
        measure_le_le_exp_mul_mgf (m - t) (neg_nonpos.mpr hθ) (h_int (-θ))
      _ ≤ Real.exp (-(-θ) * (m - t)) * Real.exp (m * (Real.exp (-θ) - 1)) :=
        mul_le_mul_of_nonneg_left (h_mgf (-θ)) (Real.exp_pos _).le
      _ ≤ Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le hθ) hm.le
        nlinarith
      _ = Real.exp (-m * bennettRate (t / m)) := by
        congr 1
        exact bennett_exponent_identity hm ht

end FreezingGrowth
