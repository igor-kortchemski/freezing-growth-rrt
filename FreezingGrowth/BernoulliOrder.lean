module

public import FreezingGrowth.ActiveHeightBernoulli

/-!
# Stochastic monotonicity of finite independent Bernoulli sums

This is the finite probability comparison used in the low-population binomial
argument. It compares the actual independent product measures. The proof uses
the two-term Bernoulli recursion and monotonicity of bounded test functions.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem integrable_unit_bounded (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun k => by simpa only [Real.norm_eq_abs] using hf k

/-- Increasing any Bernoulli parameters increases every bounded increasing
observable of the sum; parameters outside the selected coordinates are irrelevant. -/
theorem integral_bernoulliPartialSumLaw_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → unitInterval) (s : Finset ι)
    (hpq : ∀ i ∈ s, p i ≤ q i) (f : ℕ → ℝ) (hf : Monotone f)
    (hb : ∀ k, |f k| ≤ 1) :
    (∫ k, f k ∂bernoulliPartialSumLaw p s) ≤
      ∫ k, f k ∂bernoulliPartialSumLaw q s := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    have hrest : ∀ j ∈ s, p j ≤ q j := fun j hj => hpq j (Finset.mem_insert_of_mem hj)
    have hparam : (p i : ℝ) ≤ (q i : ℝ) := hpq i (Finset.mem_insert_self i s)
    have hshift : Monotone (fun k => f (k + 1)) := fun a b hab => hf (by omega)
    have hbase := ih hrest f hf hb
    have hnext := ih hrest (fun k => f (k + 1)) hshift (fun k => hb (k + 1))
    have hstep : (∫ k, f k ∂bernoulliPartialSumLaw q s) ≤
        ∫ k, f (k + 1) ∂bernoulliPartialSumLaw q s :=
      integral_mono (integrable_unit_bounded _ f hb)
        (integrable_unit_bounded _ _ (fun k => hb (k + 1)))
        (fun k => hf (Nat.le_succ k))
    rw [bernoulliPartialSumLaw_insert p s hi, bernoulliPartialSumLaw_insert q s hi,
      integral_bind_shiftedBernoulli _ _ f hb, integral_bind_shiftedBernoulli _ _ f hb]
    have hp0 : 0 ≤ (p i : ℝ) := (p i).property.1
    have hp1 : (p i : ℝ) ≤ 1 := (p i).property.2
    calc
      _ ≤ (1 - (p i : ℝ)) * (∫ k, f k ∂bernoulliPartialSumLaw q s) +
          (p i : ℝ) * (∫ k, f (k + 1) ∂bernoulliPartialSumLaw q s) :=
        add_le_add (mul_le_mul_of_nonneg_left hbase (by linarith))
          (mul_le_mul_of_nonneg_left hnext hp0)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hparam) (sub_nonneg.mpr hstep)]

/-- Upper-tail form of the comparison, with all empty-set and zero-threshold
boundary cases included. -/
theorem bernoulliPartialSumLaw_real_tail_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → unitInterval) (s : Finset ι)
    (hpq : ∀ i ∈ s, p i ≤ q i) (h : ℕ) :
    (bernoulliPartialSumLaw p s).real {k | h ≤ k} ≤
      (bernoulliPartialSumLaw q s).real {k | h ≤ k} := by
  let f : ℕ → ℝ := {k | h ≤ k}.indicator (fun _ => 1)
  have hf : Monotone f := by
    intro a b hab
    by_cases ha : h ≤ a
    · have hh : h ≤ b := ha.trans hab
      simp [f, ha, hh]
    · by_cases hh : h ≤ b <;> simp [f, ha, hh]
  have hb : ∀ k, |f k| ≤ 1 := by
    intro k
    by_cases hk : h ≤ k <;> simp [f, hk]
  have hh := integral_bernoulliPartialSumLaw_mono p q s hpq f hf hb
  simpa only [f, integral_indicator_const (1 : ℝ)
    (show MeasurableSet {k : ℕ | h ≤ k} from by trivial), smul_eq_mul, mul_one] using hh

/-- The ENNReal upper-tail comparison, independent of taking real-valued mass. -/
theorem bernoulliPartialSumLaw_tail_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → unitInterval) (s : Finset ι)
    (hpq : ∀ i ∈ s, p i ≤ q i) (h : ℕ) :
    bernoulliPartialSumLaw p s {k | h ≤ k} ≤
      bernoulliPartialSumLaw q s {k | h ≤ k} := by
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    (bernoulliPartialSumLaw_real_tail_mono p q s hpq h)

end FreezingGrowth
