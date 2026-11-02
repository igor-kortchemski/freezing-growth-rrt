module

public import FreezingGrowth.PWIT.OverlapEstimates
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.PSeries

/-! Analytic constants for the three near-leading factors in a pair bound.
No actual pair-moment estimate is asserted in this file. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set

theorem integrableOn_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-c * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := 1)
    (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (-1 : ℝ) < (k : ℝ)) (by norm_num) hc
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

theorem integrableOn_three_ballot_polynomial {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (1 + u ^ 6) ^ 3 * Real.exp (-c * u)) (Ioi 0) := by
  have h0 := integrableOn_pow_mul_exp_neg 0 hc
  have h6 := (integrableOn_pow_mul_exp_neg 6 hc).const_mul 3
  have h12 := (integrableOn_pow_mul_exp_neg 12 hc).const_mul 3
  have h18 := integrableOn_pow_mul_exp_neg 18 hc
  have hsum := ((h0.add h6).add h12).add h18
  apply hsum.congr_fun _ measurableSet_Ioi
  intro u _
  change u ^ 0 * Real.exp (-c * u) + 3 * (u ^ 6 * Real.exp (-c * u)) +
      3 * (u ^ 12 * Real.exp (-c * u)) + u ^ 18 * Real.exp (-c * u) =
    (1 + u ^ 6) ^ 3 * Real.exp (-c * u)
  ring

/-- A finite, positive choice for a constant absorbing the translated
three-factor integral. Its value need not be evaluated numerically. -/
noncomputable def threeBallotIntegralConstant : ℝ :=
  1 + Real.exp (Real.exp 1) *
    ∫ u in Ioi 0, (1 + u ^ 6) ^ 3 * Real.exp (-Real.exp 1 * u)

theorem threeBallotIntegralConstant_pos : 0 < threeBallotIntegralConstant := by
  have hi : 0 ≤ ∫ u in Ioi 0, (1 + u ^ 6) ^ 3 * Real.exp (-Real.exp 1 * u) := by
    apply integral_nonneg
    intro u
    positivity
  unfold threeBallotIntegralConstant
  positivity

noncomputable def threeFactorDepthWeight (j q : ℝ) : ℝ :=
  ((j + q) ^ (3 / 2 : ℝ) * (j + q) ^ (3 * q / (2 * (j + q)))) /
    (j ^ (3 / 2 : ℝ) * q ^ 3)

theorem threeFactorDepthWeight_le_left {j q : ℝ} (hj : 1 ≤ j) (hq : 1 ≤ q)
    (hjq : j ≤ q) :
    threeFactorDepthWeight j q ≤ 8 / j ^ (3 / 2 : ℝ) := by
  let n : ℝ := j + q
  have hjp : 0 < j := by linarith
  have hqp : 0 < q := by linarith
  have hnp : 0 < n := by dsimp [n]; linarith
  have hn1 : 1 ≤ n := by dsimp [n]; linarith
  have hqn : q ≤ n := by dsimp [n]; linarith
  have hpow : n ^ (3 / 2 : ℝ) * n ^ (3 * q / (2 * n)) ≤ n ^ (3 : ℝ) := by
    rw [← Real.rpow_add hnp]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hfrac : q / n ≤ 1 := (div_le_one hnp).mpr hqn
    have he : (3 / 2 : ℝ) + 3 * q / (2 * n) = (3 / 2 : ℝ) + (3 / 2 : ℝ) * (q / n) := by field_simp
    rw [he]
    linarith
  have hnq : n ≤ 2 * q := by dsimp [n]; linarith
  have hcube : n ^ (3 : ℝ) ≤ 8 * q ^ 3 := by
    have hh := Real.rpow_le_rpow hnp.le hnq (by norm_num : (0 : ℝ) ≤ 3)
    norm_num only [Real.rpow_ofNat, mul_pow] at hh
    simpa only [Real.rpow_ofNat] using hh
  have hden : 0 < j ^ (3 / 2 : ℝ) * q ^ 3 := by positivity
  unfold threeFactorDepthWeight
  change (n ^ (3 / 2 : ℝ) * n ^ (3 * q / (2 * n))) / _ ≤ _
  calc
    _ ≤ (8 * q ^ 3) / (j ^ (3 / 2 : ℝ) * q ^ 3) :=
      div_le_div_of_nonneg_right (hpow.trans hcube) hden.le
    _ = _ := by field_simp

theorem threeFactorDepthWeight_le_right {j q : ℝ} (hj : 1 ≤ j) (hq : 1 ≤ q)
    (hqj : q ≤ j) :
    threeFactorDepthWeight j q ≤
      ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)) / q ^ (3 / 2 : ℝ) := by
  let n : ℝ := j + q
  have hjp : 0 < j := by linarith
  have hqp : 0 < q := by linarith
  have hnp : 0 < n := by dsimp [n]; linarith
  have hqpow : q ^ (3 / 2 : ℝ) * q ^ (3 / 2 : ℝ) = q ^ 3 := by
    rw [← Real.rpow_add hqp]
    norm_num
  have hratio : (n / j) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply (div_le_iff₀ hjp).mpr
    dsimp [n]
    linarith
  have hover := overlap_factor_le (d := n) hq (by dsimp [n]; linarith : q ≤ n)
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hqp.le] at hover
  have he : threeFactorDepthWeight j q =
      ((n / j) ^ (3 / 2 : ℝ) *
        ((q ^ (3 / 2 : ℝ))⁻¹ * n ^ (3 * q / (2 * n)))) / q ^ (3 / 2 : ℝ) := by
    unfold threeFactorDepthWeight
    change (n ^ (3 / 2 : ℝ) * n ^ (3 * q / (2 * n))) / _ = _
    rw [Real.div_rpow hnp.le hjp.le, ← hqpow]
    field_simp
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hqp.le _)
  exact mul_le_mul hratio hover (by positivity) (by positivity)

/-- The central splitting depths are dominated by two summable p-series.
The finitely many short-prefix/suffix cases are handled separately. -/
theorem threeFactorDepthWeight_le {j q : ℝ} (hj : 1 ≤ j) (hq : 1 ≤ q) :
    threeFactorDepthWeight j q ≤ 8 / j ^ (3 / 2 : ℝ) +
      ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)) / q ^ (3 / 2 : ℝ) := by
  by_cases hh : j ≤ q
  · exact (threeFactorDepthWeight_le_left hj hq hh).trans (le_add_of_nonneg_right (by positivity))
  · exact (threeFactorDepthWeight_le_right hj hq (le_of_not_ge hh)).trans
      (le_add_of_nonneg_left (by positivity))

/-- The full finite depth sum has a bound independent of the total generation. -/
theorem sum_threeFactorDepthWeight_le (d : ℕ) :
    (∑ j ∈ Finset.Icc 1 (d - 1), threeFactorDepthWeight j (d - j : ℕ)) ≤
      (8 + (2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)) *
        ∑' k : ℕ, 1 / (k : ℝ) ^ (3 / 2 : ℝ) := by
  classical
  let S := Finset.Icc 1 (d - 1)
  let K : ℝ := (2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (3 / 2 : ℝ)
  let f (k : ℕ) : ℝ := 1 / (k : ℝ) ^ (3 / 2 : ℝ)
  have hf : Summable f := Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hfn (k : ℕ) : 0 ≤ f k := by dsimp [f]; positivity
  have hleft : (∑ j ∈ S, f j) ≤ ∑' k : ℕ, f k :=
    Summable.sum_le_tsum S (fun k _ => hfn k) hf
  have hinj : ∀ a ∈ S, ∀ b ∈ S, d - a = d - b → a = b := by
    intro a ha b hb hab
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    omega
  have hright : (∑ j ∈ S, f (d - j)) ≤ ∑' k : ℕ, f k := by
    rw [← Finset.sum_image hinj]
    exact Summable.sum_le_tsum _ (fun k _ => hfn k) hf
  have hterm (j : ℕ) (hj : j ∈ S) :
      threeFactorDepthWeight j (d - j : ℕ) ≤ 8 * f j + K * f (d - j) := by
    have hmem := Finset.mem_Icc.mp hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hmem.1
    have hq' : (1 : ℝ) ≤ (d - j : ℕ) := by exact_mod_cast (by omega : 1 ≤ d - j)
    simpa only [f, K, div_eq_mul_inv, one_mul] using threeFactorDepthWeight_le hj' hq'
  calc
    _ ≤ ∑ j ∈ S, (8 * f j + K * f (d - j)) := Finset.sum_le_sum hterm
    _ = 8 * (∑ j ∈ S, f j) + K * ∑ j ∈ S, f (d - j) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 8 * (∑' k : ℕ, f k) + K * ∑' k : ℕ, f k :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (by norm_num))
        (mul_le_mul_of_nonneg_left hright (by dsimp [K]; positivity))
    _ = _ := by dsimp [K, f]; ring

end FreezingGrowth.PWIT
