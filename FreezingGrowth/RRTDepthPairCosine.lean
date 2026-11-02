module

public import FreezingGrowth.RRTDepthPairDistinct
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A scalar characteristic-function comparison for the actual depth difference.
The comparator is a product of symmetric Bernoulli-difference factors. Its
asymptotic agreement with the actual law follows from summable reset errors. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory Filter
open scoped Topology

noncomputable def depthDifferenceCosine (n : ℕ) (t : ℝ) : ℝ :=
  ∫ z : ℤ, Real.cos (t * z) ∂depthDifferenceLaw n

noncomputable def depthDifferenceIdealFactor (n : ℕ) (t : ℝ) : ℝ :=
  1 + 2 * depthBernoulliParameter n * (1 - depthBernoulliParameter n) * (Real.cos t - 1)

noncomputable def depthDifferenceIdealProduct (n : ℕ) (t : ℝ) : ℝ :=
  ∏ k ∈ Finset.range n, depthDifferenceIdealFactor k t

theorem depthDifferenceCosine_abs_le (n : ℕ) (t : ℝ) : |depthDifferenceCosine n t| ≤ 1 := by
  unfold depthDifferenceCosine
  calc
    _ ≤ ∫ z : ℤ, |Real.cos (t * z)| ∂depthDifferenceLaw n := abs_integral_le_integral_abs
    _ ≤ ∫ _z : ℤ, (1 : ℝ) ∂depthDifferenceLaw n :=
      integral_mono (depthDifferenceLaw_integrable n _) (integrable_const 1)
        (fun _ => Real.abs_cos_le_one _)
    _ = 1 := by simp

@[simp] theorem depthDifferenceCosine_zero (t : ℝ) : depthDifferenceCosine 0 t = 1 := by
  unfold depthDifferenceCosine
  calc
    _ = ∫ _z : ℤ, (1 : ℝ) ∂depthDifferenceLaw 0 := by
      apply integral_congr_ae
      filter_upwards [depthDifferenceLaw_support 0] with z hz
      have hz0 : z = 0 := by simpa using hz
      simp [hz0]
    _ = 1 := by simp

theorem depthDifferenceCosine_succ (n : ℕ) (t : ℝ) :
    depthDifferenceCosine (n + 1) t =
      depthDifferenceIdealFactor n t * depthDifferenceCosine n t +
        depthBernoulliParameter n ^ 2 * (1 - depthDifferenceCosine n t) := by
  have hsum :
      (∫ z : ℤ, Real.cos (t * (z + 1 : ℤ)) ∂depthDifferenceLaw n) +
        (∫ z : ℤ, Real.cos (t * (z - 1 : ℤ)) ∂depthDifferenceLaw n) =
          2 * Real.cos t * depthDifferenceCosine n t := by
    rw [← integral_add (depthDifferenceLaw_integrable n _) (depthDifferenceLaw_integrable n _)]
    calc
      _ = ∫ z : ℤ, (2 * Real.cos t) * Real.cos (t * z) ∂depthDifferenceLaw n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          push_cast
          rw [mul_add, mul_sub, mul_one, Real.cos_add, Real.cos_sub]
          ring
      _ = _ := by rw [integral_const_mul]; rfl
  have hrec := depthDifferenceLaw_integral_succ n (fun z => Real.cos (t * z))
  simp only [Int.cast_zero, mul_zero, Real.cos_zero] at hrec
  change depthDifferenceCosine (n + 1) t = _ at hrec
  unfold depthDifferenceIdealFactor
  change depthDifferenceCosine (n + 1) t = _
  rw [hrec]
  change (1 - depthBernoulliParameter n) ^ 2 * depthDifferenceCosine n t +
    depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
      (∫ z : ℤ, Real.cos (t * (z + 1 : ℤ)) ∂depthDifferenceLaw n) +
    depthBernoulliParameter n * (1 - depthBernoulliParameter n) *
      (∫ z : ℤ, Real.cos (t * (z - 1 : ℤ)) ∂depthDifferenceLaw n) +
    depthBernoulliParameter n ^ 2 * 1 = _
  linear_combination depthBernoulliParameter n * (1 - depthBernoulliParameter n) * hsum

theorem depthDifferenceIdealFactor_bounds (n : ℕ) (t : ℝ) :
    0 ≤ depthDifferenceIdealFactor n t ∧ depthDifferenceIdealFactor n t ≤ 1 := by
  have hp := (depthBernoulliParameter_pos n).le
  have hp' := depthBernoulliParameter_le_half n
  have hv : 0 ≤ depthBernoulliParameter n * (1 - depthBernoulliParameter n) :=
    mul_nonneg hp (by linarith)
  have hv' : depthBernoulliParameter n * (1 - depthBernoulliParameter n) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (depthBernoulliParameter n - 1 / 2)]
  have hc := Real.cos_le_one t
  have hc' := Real.neg_one_le_cos t
  unfold depthDifferenceIdealFactor
  constructor
  · nlinarith [mul_nonneg hv (show 0 ≤ Real.cos t + 1 by linarith)]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hv (show Real.cos t - 1 ≤ 0 by linarith)]

@[simp] theorem depthDifferenceIdealProduct_zero (t : ℝ) :
    depthDifferenceIdealProduct 0 t = 1 := by simp [depthDifferenceIdealProduct]

theorem depthDifferenceIdealProduct_succ (n : ℕ) (t : ℝ) :
    depthDifferenceIdealProduct (n + 1) t =
      depthDifferenceIdealFactor n t * depthDifferenceIdealProduct n t := by
  rw [depthDifferenceIdealProduct, Finset.prod_range_succ]
  exact mul_comm _ _

theorem depthDifferenceCosine_product_error (n : ℕ) (t : ℝ) :
    |depthDifferenceCosine n t - depthDifferenceIdealProduct n t| ≤
      ∑ k ∈ Finset.range n,
        depthBernoulliParameter k ^ 2 * |1 - depthDifferenceCosine k t| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [depthDifferenceCosine_succ, depthDifferenceIdealProduct_succ, Finset.sum_range_succ]
    have hid :
        depthDifferenceIdealFactor n t * depthDifferenceCosine n t +
          depthBernoulliParameter n ^ 2 * (1 - depthDifferenceCosine n t) -
          depthDifferenceIdealFactor n t * depthDifferenceIdealProduct n t =
        depthDifferenceIdealFactor n t *
          (depthDifferenceCosine n t - depthDifferenceIdealProduct n t) +
          depthBernoulliParameter n ^ 2 * (1 - depthDifferenceCosine n t) := by ring
    rw [hid]
    calc
      _ ≤ |depthDifferenceIdealFactor n t *
          (depthDifferenceCosine n t - depthDifferenceIdealProduct n t)| +
          |depthBernoulliParameter n ^ 2 * (1 - depthDifferenceCosine n t)| := abs_add_le _ _
      _ = depthDifferenceIdealFactor n t *
          |depthDifferenceCosine n t - depthDifferenceIdealProduct n t| +
          depthBernoulliParameter n ^ 2 * |1 - depthDifferenceCosine n t| := by
        simp only [abs_mul, abs_of_nonneg (depthDifferenceIdealFactor_bounds n t).1,
          abs_of_nonneg (sq_nonneg (depthBernoulliParameter n))]
      _ ≤ |depthDifferenceCosine n t - depthDifferenceIdealProduct n t| +
          depthBernoulliParameter n ^ 2 * |1 - depthDifferenceCosine n t| := by
        apply add_le_add _ le_rfl
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (depthDifferenceIdealFactor_bounds n t).2
          (abs_nonneg (depthDifferenceCosine n t - depthDifferenceIdealProduct n t))
      _ ≤ _ := add_le_add ih le_rfl

theorem tendsto_depthDifferenceCosine_at_zero (k : ℕ) {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => depthDifferenceCosine k (t n)) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := depthDifferenceLaw k) (F := fun (n : ℕ) (z : ℤ) => Real.cos (t n * z))
    (f := fun _z : ℤ => (1 : ℝ)) (fun _z => (1 : ℝ))
    (fun _ => by fun_prop) (integrable_const 1)
    (fun n => Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t n * z))
    (Filter.Eventually.of_forall fun z => by
      simpa only [Function.comp_def, zero_mul, Real.cos_zero] using
        (Real.continuous_cos.tendsto (0 * (z : ℝ))).comp (ht.mul_const (z : ℝ)))
  simpa only [depthDifferenceCosine, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem summable_depthBernoulliParameter_sq :
    Summable (fun k => depthBernoulliParameter k ^ 2) := by
  have h := (summable_nat_add_iff 2).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa only [depthBernoulliParameter, Nat.cast_add, Nat.cast_ofNat, div_pow, one_pow] using h

/-- Every fixed reset disappears at a frequency tending to zero; summability
then removes all resets at once. No independent random-variable construction is used. -/
theorem tendsto_depthDifferenceCosine_sub_product {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => depthDifferenceCosine n (t n) - depthDifferenceIdealProduct n (t n))
      atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun n k =>
    depthBernoulliParameter k ^ 2 * |1 - depthDifferenceCosine k (t n)|
  have hF0 (n k : ℕ) : 0 ≤ F n k := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hF (n k : ℕ) : ‖F n k‖ ≤ 2 * depthBernoulliParameter k ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n k)]
    dsimp only [F]
    have habs : |1 - depthDifferenceCosine k (t n)| ≤ 2 := by
      have hh := abs_sub (1 : ℝ) (depthDifferenceCosine k (t n))
      simp only [abs_one] at hh
      linarith [depthDifferenceCosine_abs_le k (t n)]
    nlinarith [sq_nonneg (depthBernoulliParameter k)]
  have hsum := summable_depthBernoulliParameter_sq.mul_left 2
  have hlim : Tendsto (fun n => ∑' k, F n k) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hsum
      (g := fun _k => (0 : ℝ))
      (fun k => by
        simpa only [F, sub_self, abs_zero, mul_zero] using
          (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
            (tendsto_depthDifferenceCosine_at_zero k ht)).abs).const_mul
            (depthBernoulliParameter k ^ 2))
      (Filter.Eventually.of_forall fun n k => hF n k)
    simpa only [tsum_zero] using h
  apply squeeze_zero_norm' _ hlim
  exact Filter.Eventually.of_forall fun n => by
    rw [Real.norm_eq_abs]
    apply (depthDifferenceCosine_product_error n (t n)).trans
    exact (hsum.of_norm_bounded (hF n)).sum_le_tsum (Finset.range n)
      (fun k _ => hF0 n k)

end FreezingGrowth.RRT
