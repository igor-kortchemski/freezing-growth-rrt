module

public import FreezingGrowth.PWIT.ThreeFactorOverlap
public import FreezingGrowth.PWIT.GoodPaths

/-!
# Product and integral of the three ballot envelopes

The common-prefix envelope and two suffix-window envelopes combine into
an exponentially integrable excess and the summable splitting-depth weight.
These statements are analytic and do not assert an actual stochastic bound.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory Set

noncomputable def ballotExponentialEnvelope (U l A y : ℝ) : ℝ :=
  U * (1 + A ^ 6) / (l * Real.sqrt l) * Real.exp (Real.exp 1 * y - l)

noncomputable def threeBallotKernel (δ : ℝ) : ℝ :=
  (1 + (δ + 1) ^ 6) ^ 3 * Real.exp (-Real.exp 1 * δ)

theorem ballotExponentialEnvelope_nonneg {U l : ℝ} (hU : 0 ≤ U) (hl : 0 ≤ l)
    (A y : ℝ) : 0 ≤ ballotExponentialEnvelope U l A y := by
  unfold ballotExponentialEnvelope
  positivity

theorem threeBallotKernel_nonneg (δ : ℝ) : 0 ≤ threeBallotKernel δ := by
  unfold threeBallotKernel
  positivity

theorem threeFactorDepthWeight_nonneg {j q : ℝ} (hj : 0 ≤ j) (hq : 0 ≤ q) :
    0 ≤ threeFactorDepthWeight j q := by
  unfold threeFactorDepthWeight
  positivity

theorem mul_sqrt_eq_rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x * Real.sqrt x = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add hx, Real.rpow_one]

theorem exp_mul_timeCenter (n : ℕ) :
    Real.exp 1 * timeCenter n = (n : ℝ) + (3 / 2 : ℝ) * Real.log n := by
  unfold timeCenter
  field_simp

theorem three_ballot_exponential_factor {j q m : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (δ : ℝ) :
    Real.exp (Real.exp 1 * (j * m / (j + q) + δ) - j) *
        Real.exp (Real.exp 1 * (m - (j * m / (j + q) + δ)) - q) ^ 2 =
      (j + q) ^ (3 / 2 : ℝ) * (j + q) ^ (3 * q / (2 * (j + q))) *
        Real.exp (-Real.exp 1 * δ) := by
  have hn : 0 < j + q := add_pos hj hq
  have he₁ : Real.exp 1 * (j * m / (j + q) + δ) =
      (j / (j + q)) * (Real.exp 1 * m) + Real.exp 1 * δ := by ring
  have he₂ : Real.exp 1 * (m - (j * m / (j + q) + δ)) =
      (1 - j / (j + q)) * (Real.exp 1 * m) - Real.exp 1 * δ := by ring
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [he₁, he₂, hm]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

/-- Exact algebraic separation of the excess and splitting-depth factors. -/
theorem three_ballot_product_identity {j q m : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (U δ : ℝ) :
    ballotExponentialEnvelope U j (δ + 1) (j * m / (j + q) + δ) *
        ballotExponentialEnvelope U q (δ + 1) (m - (j * m / (j + q) + δ)) ^ 2 =
      U ^ 3 * threeFactorDepthWeight j q * threeBallotKernel δ := by
  have hqroot : (q * Real.sqrt q) ^ 2 = q ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hq.le]
    ring
  unfold ballotExponentialEnvelope
  rw [mul_pow, div_pow]
  have he := three_ballot_exponential_factor hj hq hm δ
  calc
    _ = (U ^ 3 * (1 + (δ + 1) ^ 6) ^ 3 /
          ((j * Real.sqrt j) * (q * Real.sqrt q) ^ 2)) *
        (Real.exp (Real.exp 1 * (j * m / (j + q) + δ) - j) *
          Real.exp (Real.exp 1 * (m - (j * m / (j + q) + δ)) - q) ^ 2) := by ring
    _ = _ := by
      rw [he, hqroot, mul_sqrt_eq_rpow_three_halves hj]
      unfold threeFactorDepthWeight threeBallotKernel
      ring

theorem three_ballot_product_at_split {j q m : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (U S : ℝ) :
    ballotExponentialEnvelope U j (S - j * m / (j + q) + 1) S *
        ballotExponentialEnvelope U q (S - j * m / (j + q) + 1) (m - S) ^ 2 =
      U ^ 3 * threeFactorDepthWeight j q * threeBallotKernel (S - j * m / (j + q)) := by
  simpa only [show j * m / (j + q) + (S - j * m / (j + q)) = S by ring] using
    three_ballot_product_identity hj hq hm U (S - j * m / (j + q))

theorem overlap_integrableOn_translate {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (c : ℝ) :
    IntegrableOn (fun s => f (s - c)) (Ioi c) := by
  have hpres := measurePreserving_add_right (volume : Measure ℝ) (-c)
  have hemb := (Homeomorph.addRight (-c)).isClosedEmbedding.measurableEmbedding
  have hset : (fun s : ℝ => s + -c) ⁻¹' Ioi 0 = Ioi c := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have h := (hpres.integrableOn_comp_preimage hemb).mpr hf
  simpa only [hset, Function.comp_def, sub_eq_add_neg] using h

theorem overlap_integral_translate (f : ℝ → ℝ) (c : ℝ) :
    (∫ s in Ioi c, f (s - c)) = ∫ u in Ioi 0, f u := by
  have hpres := measurePreserving_add_right (volume : Measure ℝ) (-c)
  have hemb := (Homeomorph.addRight (-c)).isClosedEmbedding.measurableEmbedding
  have hset : (fun s : ℝ => s + -c) ⁻¹' Ioi 0 = Ioi c := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hset, sub_eq_add_neg] using hpres.setIntegral_preimage_emb hemb f (Ioi 0)

theorem threeBallotKernel_translate (c s : ℝ) :
    threeBallotKernel (s - c) = Real.exp (Real.exp 1) *
      ((1 + (s - (c - 1)) ^ 6) ^ 3 * Real.exp (-Real.exp 1 * (s - (c - 1)))) := by
  unfold threeBallotKernel
  rw [show s - c + 1 = s - (c - 1) by ring]
  have he : Real.exp (-Real.exp 1 * (s - c)) =
      Real.exp (Real.exp 1) * Real.exp (-Real.exp 1 * (s - (c - 1))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem integrableOn_threeBallotKernel_translate (c : ℝ) :
    IntegrableOn (fun s => threeBallotKernel (s - c)) (Ioi (c - 1)) := by
  have h := overlap_integrableOn_translate
    (integrableOn_three_ballot_polynomial (Real.exp_pos 1)) (c - 1)
  have hscaled : IntegrableOn (fun s => Real.exp (Real.exp 1) *
      ((1 + (s - (c - 1)) ^ 6) ^ 3 * Real.exp (-Real.exp 1 * (s - (c - 1)))))
      (Ioi (c - 1)) := h.const_mul (Real.exp (Real.exp 1))
  apply hscaled.congr_fun _ measurableSet_Ioi
  intro s _
  exact (threeBallotKernel_translate c s).symm

theorem integral_threeBallotKernel_translate (c : ℝ) :
    (∫ s in Ioi (c - 1), threeBallotKernel (s - c)) = Real.exp (Real.exp 1) *
      ∫ u in Ioi 0, (1 + u ^ 6) ^ 3 * Real.exp (-Real.exp 1 * u) := by
  simp_rw [threeBallotKernel_translate c]
  rw [integral_const_mul]
  congr 1
  exact overlap_integral_translate
    (fun u : ℝ => (1 + u ^ 6) ^ 3 * Real.exp (-Real.exp 1 * u)) (c - 1)

theorem integrableOn_three_ballot_product {j q m : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (U : ℝ) :
    IntegrableOn (fun S =>
      ballotExponentialEnvelope U j (S - j * m / (j + q) + 1) S *
        ballotExponentialEnvelope U q (S - j * m / (j + q) + 1) (m - S) ^ 2)
      (Ioi (j * m / (j + q) - 1)) := by
  have h : IntegrableOn (fun S => U ^ 3 * threeFactorDepthWeight j q *
      threeBallotKernel (S - j * m / (j + q))) (Ioi (j * m / (j + q) - 1)) :=
    (integrableOn_threeBallotKernel_translate (j * m / (j + q))).const_mul
      (U ^ 3 * threeFactorDepthWeight j q)
  apply h.congr_fun _ measurableSet_Ioi
  intro S _
  exact (three_ballot_product_at_split hj hq hm U S).symm

/-- Uniform integration in the common-prefix excess. -/
theorem integral_three_ballot_product_le {j q m U : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (hU : 0 ≤ U) :
    (∫ S in Ioi (j * m / (j + q) - 1),
      ballotExponentialEnvelope U j (S - j * m / (j + q) + 1) S *
        ballotExponentialEnvelope U q (S - j * m / (j + q) + 1) (m - S) ^ 2) ≤
      U ^ 3 * threeFactorDepthWeight j q * threeBallotIntegralConstant := by
  simp_rw [three_ballot_product_at_split hj hq hm U]
  rw [integral_const_mul, integral_threeBallotKernel_translate]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (pow_nonneg hU 3) (threeFactorDepthWeight_nonneg hj.le hq.le))
  unfold threeBallotIntegralConstant
  linarith

theorem integral_three_ballot_product_timeCenter_le {j q : ℕ} (hj : 0 < j) (hq : 0 < q)
    {U : ℝ} (hU : 0 ≤ U) :
    (∫ S in Ioi ((j : ℝ) * timeCenter (j + q) / (j + q : ℕ) - 1),
      ballotExponentialEnvelope U j (S - (j : ℝ) * timeCenter (j + q) / (j + q : ℕ) + 1) S *
        ballotExponentialEnvelope U q (S - (j : ℝ) * timeCenter (j + q) / (j + q : ℕ) + 1)
          (timeCenter (j + q) - S) ^ 2) ≤
      U ^ 3 * threeFactorDepthWeight j q * threeBallotIntegralConstant := by
  have hm : Real.exp 1 * timeCenter (j + q) =
      (j : ℝ) + q + (3 / 2 : ℝ) * Real.log ((j : ℝ) + q) := by
    simpa only [Nat.cast_add] using exp_mul_timeCenter (j + q)
  simpa only [Nat.cast_add] using integral_three_ballot_product_le
    (Nat.cast_pos.mpr hj) (Nat.cast_pos.mpr hq) hm hU

/-- The boundary singleton has zero Lebesgue measure, giving the closed
half-line form used by the actual pair-overlap transport. -/
theorem integral_three_ballot_product_timeCenter_Ici_le {j q : ℕ} (hj : 0 < j) (hq : 0 < q)
    {U : ℝ} (hU : 0 ≤ U) :
    (∫ S in Ici ((j : ℝ) * timeCenter (j + q) / (j + q : ℕ) - 1),
      ballotExponentialEnvelope U j (S - (j : ℝ) * timeCenter (j + q) / (j + q : ℕ) + 1) S *
        ballotExponentialEnvelope U q (S - (j : ℝ) * timeCenter (j + q) / (j + q : ℕ) + 1)
          (timeCenter (j + q) - S) ^ 2) ≤
      U ^ 3 * threeFactorDepthWeight j q * threeBallotIntegralConstant := by
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_three_ballot_product_timeCenter_le hj hq hU

theorem integrableOn_three_ballot_product_Ici {j q m : ℝ} (hj : 0 < j) (hq : 0 < q)
    (hm : Real.exp 1 * m = j + q + (3 / 2 : ℝ) * Real.log (j + q)) (U : ℝ) :
    IntegrableOn (fun S =>
      ballotExponentialEnvelope U j (S - j * m / (j + q) + 1) S *
        ballotExponentialEnvelope U q (S - j * m / (j + q) + 1) (m - S) ^ 2)
      (Ici (j * m / (j + q) - 1)) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
    (integrableOn_three_ballot_product hj hq hm U)

end FreezingGrowth.PWIT
