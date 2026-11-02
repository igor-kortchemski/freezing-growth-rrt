module

public import FreezingGrowth.BernoulliOrder
public import Mathlib.Probability.Distributions.Binomial

/-! Identifying constant-parameter independent sums with Mathlib's binomial law. -/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem shiftedBernoulli_probability' (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (p : unitInterval) :
    IsProbabilityMeasure (μ.bind (fun k => bernoulliMeasure (k + 1) k p)) :=
  isProbabilityMeasure_bind measurable_from_top.aemeasurable (Filter.Eventually.of_forall fun _ => inferInstance)

/-- A Bernoulli increment has zero mass at zero from its positive branch. -/
theorem bind_shiftedBernoulli_real_zero (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (p : unitInterval) :
    (μ.bind (fun k => bernoulliMeasure (k + 1) k p)).real {0} =
      (1 - (p : ℝ)) * μ.real {0} := by
  let f : ℕ → ℝ := ({0} : Set ℕ).indicator (fun _ => 1)
  have hb : ∀ k, |f k| ≤ 1 := by intro k; by_cases hk : k = 0 <;> simp [f, hk]
  have hf : (fun k => f (k + 1)) = fun _ => 0 := by funext k; simp [f]
  have hh := integral_bind_shiftedBernoulli μ p f hb
  rw [hf] at hh
  simpa only [f, integral_indicator_const (1 : ℝ) (measurableSet_singleton 0),
    integral_zero, mul_zero, add_zero, smul_eq_mul, mul_one] using hh

/-- Singleton recurrence for one independent Bernoulli increment. -/
theorem bind_shiftedBernoulli_real_succ (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (p : unitInterval) (k : ℕ) :
    (μ.bind (fun d => bernoulliMeasure (d + 1) d p)).real {k + 1} =
      (1 - (p : ℝ)) * μ.real {k + 1} + (p : ℝ) * μ.real {k} := by
  let f : ℕ → ℝ := ({k + 1} : Set ℕ).indicator (fun _ => 1)
  have hb : ∀ d, |f d| ≤ 1 := by
    intro d; by_cases hd : d = k + 1 <;> simp [f, hd]
  have hf : (fun d => f (d + 1)) = ({k} : Set ℕ).indicator (fun _ => 1) := by
    funext d
    simp only [f, Set.indicator_apply, Set.mem_singleton_iff, Nat.add_right_cancel_iff]
  have hh := integral_bind_shiftedBernoulli μ p f hb
  rw [hf] at hh
  simpa only [f, integral_indicator_const (1 : ℝ) (measurableSet_singleton (k + 1)),
    integral_indicator_const (1 : ℝ) (measurableSet_singleton k),
    smul_eq_mul, mul_one] using hh

/-- The binomial distribution satisfies the independent-increment recursion. -/
theorem binomial_succ_eq_bind (n : ℕ) (p : unitInterval) :
    binomial (n + 1) p =
      (binomial n p).bind (fun k => bernoulliMeasure (k + 1) k p) := by
  let := shiftedBernoulli_probability' (binomial n p) p
  apply Measure.ext_of_measureReal_singleton
  intro k
  cases k with
  | zero =>
    rw [bind_shiftedBernoulli_real_zero]
    simp [pow_succ, mul_comm]
  | succ k =>
    rw [bind_shiftedBernoulli_real_succ]
    simp only [binomial_real_singleton]
    by_cases hkn : k < n
    · have hd : n - k = n - (k + 1) + 1 := by omega
      rw [Nat.choose_succ_succ, Nat.cast_add,
        show n + 1 - (k + 1) = n - k by omega, hd]
      simp only [pow_succ]
      ring
    · rcases eq_or_lt_of_le (Nat.le_of_not_gt hkn) with he | he
      · subst k
        simp [pow_succ, mul_comm]
      · have hk : n < k := he
        have hk' : n + 1 < k + 1 := by omega
        simp [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt hk',
          Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]

/-- A sum over `s.card` independent Bernoulli variables with common parameter
is exactly the binomial measure, including the zero-coordinate case. -/
theorem bernoulliPartialSumLaw_const_eq_binomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : unitInterval) (s : Finset ι) :
    bernoulliPartialSumLaw (fun _ : ι => p) s = binomial s.card p := by
  induction s using Finset.induction_on with
  | empty => simp [binomial_zero]
  | @insert i s hi ih =>
    rw [bernoulliPartialSumLaw_insert _ _ hi, ih, Finset.card_insert_of_notMem hi,
      binomial_succ_eq_bind]

end FreezingGrowth
