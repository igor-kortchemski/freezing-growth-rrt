module

public import FreezingGrowth.PWIT.CriticalCrossingProbability
public import FreezingGrowth.PWIT.CriticalDepthWeights

/-! Analytic separation of the critical first-crossing envelopes. The
parameter choices and finite sums are explicit; no probabilistic estimate
is supplied as a premise in these algebraic lemmas. -/

@[expose] public section
namespace FreezingGrowth.PWIT

noncomputable def criticalCrossingPolynomialConstant (A₀ : ℝ) : ℝ :=
  (1 + A₀ + 2 / Real.exp 1) ^ 14

theorem criticalCrossingPolynomialConstant_pos {A₀ : ℝ} (hA : 0 ≤ A₀) :
    0 < criticalCrossingPolynomialConstant A₀ := by
  unfold criticalCrossingPolynomialConstant
  positivity

theorem critical_crossing_exponential_identity {d : ℕ} (hd : 0 < d)
    (j : ℕ) (x A₀ : ℝ) :
    Real.exp (Real.exp 1 * criticalCrossingBarrier d j (x / Real.exp 1 + A₀)
      (2 / Real.exp 1) - j) =
      Real.exp (-x - Real.exp 1 * A₀) * (d : ℝ) ^ (3 * (j : ℝ) / (2 * d)) /
        ((((min j (d - j) : ℕ) : ℝ) + 1) ^ 2) := by
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let M : ℝ := ((min j (d - j) : ℕ) : ℝ) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have he : Real.exp 1 * criticalCrossingBarrier d j (x / Real.exp 1 + A₀)
      (2 / Real.exp 1) - j =
      (-x - Real.exp 1 * A₀) + Real.log (d : ℝ) * (3 * (j : ℝ) / (2 * d)) -
        2 * Real.log M := by
    unfold criticalCrossingBarrier timeCenter
    dsimp [M]
    field_simp
    ring
  have hpow : Real.exp (2 * Real.log M) = M ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hM] using Real.exp_nat_mul (Real.log M) 2
  rw [he, Real.exp_sub, Real.exp_add, hpow, Real.rpow_def_of_pos hdp]

/-- A single polynomial envelope for every possible first-crossing depth. -/
theorem critical_crossing_allowance_polynomial {A₀ x : ℝ} (hA : 0 ≤ A₀) (hx : 0 ≤ x)
    (d j : ℕ) :
    1 + (crossingAllowance d j (x / Real.exp 1 + A₀) (2 / Real.exp 1) +
      2 / Real.exp 1) ^ 14 ≤ criticalCrossingPolynomialConstant A₀ * (1 + x) ^ 14 *
        (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ 14 := by
  let L := Real.log (((min j (d - j) : ℕ) : ℝ) + 1)
  let B := 1 + A₀ + 2 / Real.exp 1
  let z := crossingAllowance d j (x / Real.exp 1 + A₀) (2 / Real.exp 1) + 2 / Real.exp 1
  have hL : 0 ≤ L := Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) (min j (d - j))
    linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hz : 0 ≤ z := by dsimp [z, crossingAllowance]; change 0 ≤ x / Real.exp 1 + A₀ + (2 / Real.exp 1) * L + 2 / Real.exp 1; positivity
  have hBx : 0 ≤ B - 1 / Real.exp 1 := by
    have he : B - 1 / Real.exp 1 = 1 + A₀ + 1 / Real.exp 1 := by dsimp [B]; ring
    rw [he]
    positivity
  have hBc : 0 ≤ B - 2 / Real.exp 1 := by dsimp [B]; linarith
  have hlinear : 1 + z ≤ B * (1 + x) * (1 + L) := by
    have h₁ := mul_nonneg hBx hx
    have h₂ := mul_nonneg hBc hL
    have h₃ := mul_nonneg (mul_nonneg hB hx) hL
    have he : B * (1 + x) * (1 + L) - (1 + z) =
        (B - 1 / Real.exp 1) * x + (B - 2 / Real.exp 1) * L + B * x * L := by
      dsimp [z, crossingAllowance, B, L]
      ring
    have hh := add_nonneg (add_nonneg h₁ h₂) h₃
    rw [← he] at hh
    linarith
  have hp := pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hz (by decide : (14 : ℕ) ≠ 0)
  simp only [one_pow] at hp
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + z by linarith) hlinear 14
  rw [mul_pow, mul_pow] at hpow
  change 1 + z ^ 14 ≤ B ^ 14 * (1 + x) ^ 14 * (1 + L) ^ 14
  exact hp.trans hpow

noncomputable def criticalCrossingEnvelope (d j : ℕ) (A₀ x : ℝ) : ℝ :=
  (1 + (crossingAllowance d j (x / Real.exp 1 + A₀) (2 / Real.exp 1) +
    2 / Real.exp 1) ^ 14) / ((j : ℝ) * Real.sqrt j) *
      Real.exp (Real.exp 1 * criticalCrossingBarrier d j (x / Real.exp 1 + A₀)
        (2 / Real.exp 1) - j)

theorem criticalCrossingEnvelope_nonneg (d j : ℕ) (A₀ x : ℝ) :
    0 ≤ criticalCrossingEnvelope d j A₀ x := by
  unfold criticalCrossingEnvelope
  positivity

theorem criticalCrossingEnvelope_le {d j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    {A₀ x : ℝ} (hA : 0 ≤ A₀) (hx : 0 ≤ x) :
    criticalCrossingEnvelope d j A₀ x ≤
      (criticalCrossingPolynomialConstant A₀ * (1 + x) ^ 14 * Real.exp (-x - Real.exp 1 * A₀)) *
        (criticalDepthWeight d j * (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ 14) := by
  have hdp : 0 < d := by omega
  let Z := 1 + (crossingAllowance d j (x / Real.exp 1 + A₀) (2 / Real.exp 1) + 2 / Real.exp 1) ^ 14
  let K := criticalCrossingPolynomialConstant A₀ * (1 + x) ^ 14
  let L := (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ 14
  let R := Real.exp (-x - Real.exp 1 * A₀)
  let N := (d : ℝ) ^ (3 * (j : ℝ) / (2 * d))
  let M := (((min j (d - j) : ℕ) : ℝ) + 1) ^ 2
  let J := (j : ℝ) * Real.sqrt j
  have hpoly : Z ≤ K * L := critical_crossing_allowance_polynomial hA hx d j
  have hfac : 0 ≤ R * N / M / J := by dsimp [R, N, M, J]; positivity
  unfold criticalCrossingEnvelope
  rw [critical_crossing_exponential_identity hdp j x A₀]
  change Z / J * (R * N / M) ≤ (K * R) * (N / (J * M) * L)
  calc
    _ = Z * (R * N / M / J) := by ring
    _ ≤ (K * L) * (R * N / M / J) := mul_le_mul_of_nonneg_right hpoly hfac
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Every crossing dimension, including the last one, is bounded by the
same finite logarithmic series. -/
theorem sum_criticalCrossingEnvelope_le (d : ℕ) {A₀ x : ℝ} (hA : 0 ≤ A₀) (hx : 0 ≤ x) :
    (∑ j ∈ Finset.Icc 1 d, criticalCrossingEnvelope d j A₀ x) ≤
      8 * shiftedLogBallotSum 14 * criticalCrossingPolynomialConstant A₀ *
        (1 + x) ^ 14 * Real.exp (-x - Real.exp 1 * A₀) := by
  let F := criticalCrossingPolynomialConstant A₀ * (1 + x) ^ 14 * Real.exp (-x - Real.exp 1 * A₀)
  have hF : 0 ≤ F := by dsimp [F]; have := criticalCrossingPolynomialConstant_pos hA; positivity
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 d, F * (criticalDepthWeight d j *
        (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ 14) := by
      apply Finset.sum_le_sum
      intro j hj
      exact criticalCrossingEnvelope_le (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hA hx
    _ = F * ∑ j ∈ Finset.Icc 1 d, criticalDepthWeight d j *
        (1 + Real.log (((min j (d - j) : ℕ) : ℝ) + 1)) ^ 14 := (Finset.mul_sum _ _ _).symm
    _ ≤ F * (8 * shiftedLogBallotSum 14) :=
      mul_le_mul_of_nonneg_left (sum_criticalDepthWeight_log_power_le 14 d) hF
    _ = _ := by dsimp [F]; ring

theorem sum_criticalCrossingEnvelope_from_thirty_le (d : ℕ)
    {A₀ x : ℝ} (hA : 0 ≤ A₀) (hx : 0 ≤ x) :
    (∑ j ∈ Finset.Icc 30 d, criticalCrossingEnvelope d j A₀ x) ≤
      8 * shiftedLogBallotSum 14 * criticalCrossingPolynomialConstant A₀ *
        (1 + x) ^ 14 * Real.exp (-x - Real.exp 1 * A₀) := by
  apply le_trans _ (sum_criticalCrossingEnvelope_le d hA hx)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; omega, (Finset.mem_Icc.mp hj).2⟩
  · intro j _ _
    exact criticalCrossingEnvelope_nonneg d j A₀ x

noncomputable def criticalClockUpperConstant (A₀ : ℝ) : ℝ :=
  8 * logGenerationConstant * shiftedLogBallotSum 14 * criticalCrossingPolynomialConstant A₀ *
    Real.exp (-Real.exp 1 * A₀)

theorem criticalClockUpperConstant_pos {A₀ : ℝ} (hA : 0 ≤ A₀) :
    0 < criticalClockUpperConstant A₀ := by
  have h₁ := logGenerationConstant_pos
  have h₂ := shiftedLogBallotSum_pos 14
  have h₃ := criticalCrossingPolynomialConstant_pos hA
  unfold criticalClockUpperConstant
  positivity

theorem crossingIntensityBound_eq_criticalEnvelope (d j : ℕ) (A₀ x : ℝ) :
    crossingIntensityBound d j (x / Real.exp 1 + A₀) (2 / Real.exp 1) =
      logGenerationConstant * criticalCrossingEnvelope d j A₀ x := by
  unfold crossingIntensityBound criticalCrossingEnvelope
  ring

/-- The real finite sum consumed by the actual probability union bound. -/
theorem sum_crossingIntensityBound_critical_le (d : ℕ) {A₀ x : ℝ}
    (hA : 0 ≤ A₀) (hx : 0 ≤ x) :
    (∑ j ∈ Finset.Icc 30 d, crossingIntensityBound d j (x / Real.exp 1 + A₀) (2 / Real.exp 1)) ≤
      criticalClockUpperConstant A₀ * (1 + x) ^ 14 * Real.exp (-x) := by
  simp_rw [crossingIntensityBound_eq_criticalEnvelope]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (sum_criticalCrossingEnvelope_from_thirty_le d hA hx)
    logGenerationConstant_pos.le).trans_eq
  have he : Real.exp (-x - Real.exp 1 * A₀) = Real.exp (-Real.exp 1 * A₀) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold criticalClockUpperConstant
  ring

end FreezingGrowth.PWIT
