module

public import FreezingGrowth.ForwardHeight
public import FreezingGrowth.BernoulliProductLaw
public import FreezingGrowth.ScheduleBernoulli
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Independent Bernoulli representation of the genuine active-height law

This proves the distributional identity cited in `main.tex`, lines 917–919,
directly from the forward transition recursion. The product coordinates have
parameters `1 / S_(i+1)` at every step, and only attachment coordinates are
summed. The hypothesis excludes extinction, where a uniform active vertex
does not exist; the separate finite-word endpoint reduction preserves the
maximum height when the last vertex freezes.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private theorem shiftedBernoulli_probability (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (p : unitInterval) :
    IsProbabilityMeasure (μ.bind (fun k => bernoulliMeasure (k + 1) k p)) :=
  isProbabilityMeasure_bind (by fun_prop) (Filter.Eventually.of_forall fun _ => inferInstance)

private theorem integrable_bounded_nat (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall fun k => by simpa only [Real.norm_eq_abs] using hf k

/-- Integrating a bounded test function against one independent Bernoulli
increment gives its exact two-term average. -/
theorem integral_bind_shiftedBernoulli (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (p : unitInterval) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    (∫ j, f j ∂μ.bind (fun k => bernoulliMeasure (k + 1) k p)) =
      (1 - (p : ℝ)) * (∫ k, f k ∂μ) + (p : ℝ) * (∫ k, f (k + 1) ∂μ) := by
  let K : Kernel ℕ ℕ := ⟨fun k => bernoulliMeasure (k + 1) k p, measurable_from_top⟩
  let := shiftedBernoulli_probability μ p
  have hi := integrable_bounded_nat (μ.bind (fun k => bernoulliMeasure (k + 1) k p)) f hf
  have hi' : Integrable f ((K ∘ₖ Kernel.const Unit μ) ()) := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hi
  have hh := Kernel.integral_comp hi'
  have hcomp : (∫ j, f j ∂μ.bind (fun k => bernoulliMeasure (k + 1) k p)) =
      ∫ k, (∫ j, f j ∂bernoulliMeasure (k + 1) k p) ∂μ := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hh
  rw [hcomp]
  simp_rw [integral_bernoulliMeasure, smul_eq_mul]
  rw [integral_add ((integrable_bounded_nat μ _ (fun k => hf (k + 1))).const_mul _)
    ((integrable_bounded_nat μ f hf).const_mul _), integral_const_mul, integral_const_mul]
  ring

namespace Forward

/-- The integral recursion determines the complete measure, not only its moments. -/
theorem uniformActiveHeightLaw_succ_eq_bind (x : SignSequence) (n : ℕ)
    (hτ : ((n + 1 : ℕ) : ℕ∞) < extinctionTime x) (p : unitInterval)
    (hp : (p : ℝ) = if x (n + 1) then 1 / (activeCount x (n + 1) : ℝ) else 0) :
    uniformActiveHeightLaw x (n + 1) =
      (uniformActiveHeightLaw x n).bind (fun k => bernoulliMeasure (k + 1) k p) := by
  let := shiftedBernoulli_probability (uniformActiveHeightLaw x n) p
  apply Measure.ext_of_measureReal_singleton
  intro k
  let f : ℕ → ℝ := ({k} : Set ℕ).indicator (fun _ => 1)
  have hf : ∀ j, |f j| ≤ 1 := by
    intro j
    by_cases hj : j = k <;> simp [f, hj]
  have hleft : (∫ j, f j ∂uniformActiveHeightLaw x (n + 1)) =
      (uniformActiveHeightLaw x (n + 1)).real {k} :=
    integral_indicator_one (measurableSet_singleton k)
  have hright : (∫ j, f j ∂(uniformActiveHeightLaw x n).bind
      (fun k => bernoulliMeasure (k + 1) k p)) =
      ((uniformActiveHeightLaw x n).bind (fun k => bernoulliMeasure (k + 1) k p)).real {k} :=
    integral_indicator_one (measurableSet_singleton k)
  rw [← hleft, ← hright, uniformActiveHeightLaw_integral_succ x n hτ,
    integral_bind_shiftedBernoulli _ p f hf, hp]
  cases x (n + 1) <;> simp

@[simp] theorem uniformActiveHeightLaw_zero (x : SignSequence) :
    uniformActiveHeightLaw x 0 = Measure.dirac 0 := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  have hτ : (0 : ℕ∞) < extinctionTime x :=
    (lt_extinctionTime_iff x 0).mpr (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst j
      simp)
  rw [← integral_indicator_one (μ := uniformActiveHeightLaw x 0) (measurableSet_singleton k)]
  rw [uniformActiveHeightLaw_integral x 0 hτ]
  simp [treeLaw, activeMean, activeSum, initial]

/-- At every prefix of a fixed admissible horizon, the active-height law is
the law of the sum of the attachment coordinates already encountered. -/
theorem uniformActiveHeightLaw_eq_partialSum (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) {k : ℕ} (hk : k ≤ n) :
    uniformActiveHeightLaw x k = bernoulliPartialSumLaw
      (populationBernoulliParameter x n h) (attachmentIndices x n k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hkτ : ((k + 1 : ℕ) : ℕ∞) < extinctionTime x :=
      (lt_extinctionTime_iff x (k + 1)).mpr (h.mono hk)
    have hi := ih (by omega)
    cases hx : x (k + 1)
    · have hrec := uniformActiveHeightLaw_succ_eq_bind x k hkτ 0 (by simp [hx])
      rw [hrec, attachmentIndices_succ_freeze x n k hx]
      simpa only [bernoulliMeasure_zero, Measure.bind_dirac] using hi
    · rw [attachmentIndices_succ_attach x hkn hx,
        bernoulliPartialSumLaw_insert _ _ (not_mem_attachmentIndices x hkn)]
      rw [← hi]
      exact uniformActiveHeightLaw_succ_eq_bind x k hkτ
        (populationBernoulliParameter x n h ⟨k, hkn⟩) (by simp [hx])

/-- The complete independent-Bernoulli distributional representation cited in
the paper, with the actual forward uniform-active-height law on the left. -/
theorem uniformActiveHeightLaw_eq_bernoulliSum (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    uniformActiveHeightLaw x n = bernoulliPartialSumLaw
      (populationBernoulliParameter x n h)
      (Finset.univ.filter (fun i : Fin n => x (i.val + 1) = true)) := by
  simpa only [attachmentIndices_horizon] using
    uniformActiveHeightLaw_eq_partialSum x n h (k := n) le_rfl

/-- A concrete product probability space realizes the cited sum with the
genuine active-height law. Coordinate laws and independence are provided by
`bernoulliProductLaw_coordinate` and `bernoulliProductLaw_independent`. -/
theorem uniformActiveHeightLaw_sum_hasLaw (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    HasLaw (fun ω : Fin n → ℕ =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => x (i.val + 1) = true), ω i)
      (uniformActiveHeightLaw x n)
      (bernoulliProductLaw (populationBernoulliParameter x n h)) := by
  rw [uniformActiveHeightLaw_eq_bernoulliSum x n h]
  exact bernoulliPartialSumLaw_hasLaw _ _

end Forward
end FreezingGrowth
