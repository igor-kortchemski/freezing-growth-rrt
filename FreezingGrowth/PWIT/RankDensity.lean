module

public import FreezingGrowth.PWIT.SampledPath
public import FreezingGrowth.PWIT.SimplexDensity
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The radial density of the rank-class increment mixture

The measure is unnormalized: summing all rank words gives the density
`exp (-sum x) * (sum x)^k / k!` on the nonnegative orthant. There is no
class-cardinality divisor here. The identity forgets rank tags and therefore
does not by itself control the rank barrier.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

theorem sum_divided_monomials (d k : ℕ) (x : Fin d → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple d k, ∏ i, x i ^ r i / (r i).factorial) =
      (∑ i, x i) ^ k / k.factorial := by
  have hm := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin d)) x k
  rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple] at hm
  rw [hm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hs : ∑ i, r i = k := Finset.Nat.mem_antidiagonalTuple.mp hr
  have hspec : (∏ i, ((r i).factorial : ℝ)) *
      (Nat.multinomial Finset.univ r : ℝ) = (k.factorial : ℝ) := by
    have hn := Nat.multinomial_spec Finset.univ r
    rw [hs] at hn
    exact_mod_cast hn
  have hp : (∏ i, ((r i).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [Finset.prod_div_distrib]
  field_simp
  linear_combination -(∏ i, x i ^ r i) * hspec

noncomputable def incrementPDF {d : ℕ} (r : Fin d → ℕ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ i, erlangPDF (r i) (x i)

@[fun_prop] theorem measurable_incrementPDF {d : ℕ} (r : Fin d → ℕ) :
    Measurable (incrementPDF r) := by
  unfold incrementPDF
  exact Finset.measurable_prod _ fun i _ => (measurable_erlangPDF (r i)).comp (measurable_pi_apply i)

theorem incrementLaw_eq_withDensity {d : ℕ} (r : Fin d → ℕ) :
    incrementLaw r = volume.withDensity (incrementPDF r) := by
  have he (i : Fin d) : gammaMeasure ((r i : ℝ) + 1) 1 =
      volume.withDensity (erlangPDF (r i)) := by
    unfold gammaMeasure
    congr 1
    exact funext (gammaPDF_nat_succ (r i))
  simp only [incrementLaw, he]
  exact finitePi_withDensity (fun _ : Fin d => (volume : Measure ℝ))
    (fun i => erlangPDF (r i)) (fun i => measurable_erlangPDF (r i))
    (fun i y => by unfold erlangPDF; split_ifs <;> simp)

theorem incrementPDF_nonneg_orthant {d : ℕ} (r : Fin d → ℕ) (x : Fin d → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    incrementPDF r x = ENNReal.ofReal
      (Real.exp (-(∑ i, x i)) * ∏ i, x i ^ r i / (r i).factorial) := by
  simp only [incrementPDF, erlangPDF, hx, ite_true]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by
    exact div_nonneg (mul_nonneg (pow_nonneg (hx i) _) (Real.exp_pos _).le) (Nat.cast_nonneg _))]
  congr 1
  have he : (∏ i, Real.exp (-x i)) = Real.exp (-(∑ i, x i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  calc
    _ = (∏ i, x i ^ r i / (r i).factorial) * ∏ i, Real.exp (-x i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = _ := by rw [he]; ring

theorem incrementPDF_eq_zero_of_negative {d : ℕ} (r : Fin d → ℕ) (x : Fin d → ℝ)
    (hx : ¬∀ i, 0 ≤ x i) : incrementPDF r x = 0 := by
  unfold incrementPDF
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [erlangPDF, hi])

noncomputable def rankIncrementPDF (d k : ℕ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  if ∀ i, 0 ≤ x i then
    ENNReal.ofReal (Real.exp (-(∑ i, x i)) * (∑ i, x i) ^ k / k.factorial)
  else 0

theorem sum_incrementPDF (d k : ℕ) (x : Fin d → ℝ) :
    (∑ r ∈ Finset.Nat.antidiagonalTuple d k, incrementPDF r x) = rankIncrementPDF d k x := by
  by_cases hx : ∀ i, 0 ≤ x i
  · simp only [incrementPDF_nonneg_orthant _ _ hx, rankIncrementPDF, ite_eq_left hx]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ =>
      mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ =>
        div_nonneg (pow_nonneg (hx i) _) (Nat.cast_nonneg _)))]
    congr 1
    rw [← Finset.mul_sum, sum_divided_monomials]
    ring
  · simp only [incrementPDF_eq_zero_of_negative _ _ hx, Finset.sum_const_zero,
      rankIncrementPDF, ite_eq_right hx]

private theorem withDensity_finsetSum {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.withDensity (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    change μ.withDensity (f i + (fun x => ∑ j ∈ s, f j x)) =
      μ.withDensity (f i) + ∑ j ∈ s, μ.withDensity (f j)
    rw [withDensity_add_left (hf i), ih]

/-- Actual finite rank-mixture law, with all boundary cases retained. -/
theorem rankIncrementMeasure_eq_withDensity (d k : ℕ) :
    rankIncrementMeasure d k = volume.withDensity (rankIncrementPDF d k) := by
  unfold rankIncrementMeasure
  simp only [incrementLaw_eq_withDensity]
  rw [← withDensity_finsetSum volume _ _ (fun r => measurable_incrementPDF r)]
  congr 1
  exact funext (sum_incrementPDF d k)

end FreezingGrowth.PWIT
