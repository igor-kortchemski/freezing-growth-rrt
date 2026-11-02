module

public import FreezingGrowth.PWIT.SimplexSoftBallot
public import FreezingGrowth.PWIT.LogBarrierSummation

/-! Uniform scalar control of the symmetric two-block occupancy kernel. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem sqrt_sum_over_larger {k q : ℝ} (hk : 0 < k) (hq : 0 < q) (hkq : k ≤ q) :
    Real.sqrt (k + q) / (q * Real.sqrt q) ≤ 4 / (k + q) := by
  have hd : 0 < k + q := by linarith
  have hs : Real.sqrt (k + q) ≤ 2 * Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt (show k + q ≤ 4 * q by linarith)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    norm_num at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt q) / (q * Real.sqrt q) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = 2 / q := by field_simp
    _ ≤ _ := (div_le_div_iff₀ hq hd).mpr (by linarith)

theorem symmetric_occupancy_kernel_le {k q : ℝ} (hk : 0 < k) (hq : 0 < q) :
    Real.sqrt (k + q) / ((k * Real.sqrt k) * (q * Real.sqrt q)) ≤
      4 / ((k + q) * (min k q * Real.sqrt (min k q))) := by
  by_cases hh : k ≤ q
  · rw [min_eq_left hh]
    have hp := div_le_div_of_nonneg_right (sqrt_sum_over_larger hk hq hh)
      (show 0 ≤ k * Real.sqrt k by positivity)
    convert hp using 1 <;> field_simp
  · rw [min_eq_right (by linarith : q ≤ k)]
    have hp := div_le_div_of_nonneg_right (sqrt_sum_over_larger hq hk (by linarith))
      (show 0 ≤ q * Real.sqrt q by positivity)
    convert hp using 1 <;> field_simp <;> ring_nf

theorem log_allowance_factor {A c t : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (ht : 0 ≤ t) :
    1 + (A + c * t) ≤ (1 + A + c) * (1 + t) := by
  nlinarith [mul_nonneg (show 0 ≤ 1 + A by linarith) ht]

/-- In the non-exceptional regime the actual leading occupancy is bounded
by a single summable weight at the smaller block. -/
theorem simplex_log_occupancy_le_weight {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hsmall : 2 * (A + c * Real.log ((min k q : ℕ) + 1 : ℝ)) ≤ (q : ℝ)) :
    (simplexLaw (k + q)).real
        (simplexLeadingOccupancy k q (A + c * Real.log ((min k q : ℕ) + 1 : ℝ))) ≤
      (4 * twoBlockOccupancyConstant * (1 + A + c) ^ 13 / (k + q : ℕ)) *
        logBallotWeight 13 (min k q) := by
  let L := A + c * Real.log ((min k q : ℕ) + 1 : ℝ)
  have hl : 0 ≤ Real.log ((min k q : ℕ) + 1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ min k q + 1 by omega))
  have hL : 0 ≤ L := add_nonneg hA (mul_nonneg hc hl)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hfac := pow_le_pow_left₀ (show 0 ≤ 1 + L by linarith)
    (log_allowance_factor hA hc hl) 13
  rw [mul_pow] at hfac
  have hker := symmetric_occupancy_kernel_le hkR hqR
  rw [← Nat.cast_add, ← Nat.cast_min] at hker
  have hbound := simplex_leading_occupancy_bound hk hq hL hsmall
  apply hbound.trans
  have hmul := mul_le_mul hfac hker (by positivity :
      0 ≤ Real.sqrt ((k + q : ℕ) : ℝ) /
        (((k : ℝ) * Real.sqrt (k : ℝ)) * ((q : ℝ) * Real.sqrt (q : ℝ)))) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hmul twoBlockOccupancyConstant_pos.le
  unfold logBallotWeight
  convert hh using 1 <;> field_simp

theorem simplex_log_occupancy_short_suffix {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hlarge : 42 * (1 + A + c) ^ 2 < ((k + q : ℕ) : ℝ))
    (hsmall : (q : ℝ) ≤ 2 * (A + c * Real.log ((min k q : ℕ) + 1 : ℝ))) :
    (simplexLaw (k + q)).real
        (simplexLeadingOccupancy k q (A + c * Real.log ((min k q : ℕ) + 1 : ℝ))) ≤
      2 * simplexNearLeadingConstant * (1 + (11 : ℝ) ^ 6) * (1 + A + c) ^ 12 /
        ((k + q : ℕ) : ℝ) := by
  let M := 1 + A + c
  let L := A + c * Real.log ((min k q : ℕ) + 1 : ℝ)
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hlog : 0 ≤ Real.log ((min k q : ℕ) + 1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ min k q + 1 by omega))
  have hL : 0 ≤ L := add_nonneg hA (mul_nonneg hc hlog)
  have hLq : L ≤ A + c * Real.log ((q : ℝ) + 1) := by
    have hh := Real.log_le_log
      (by positivity : (0 : ℝ) < ((min k q : ℕ) + 1 : ℝ))
      (show ((min k q : ℕ) + 1 : ℝ) ≤ (q : ℝ) + 1 by
        exact_mod_cast Nat.add_le_add_right (Nat.min_le_right k q) 1)
    dsimp [L]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hh hc) A
  have hqs : (q : ℝ) ≤ 2 * (A + c * Real.log ((q : ℝ) + 1)) := by
    linarith
  have hqbound : (q : ℝ) ≤ 21 * M ^ 2 :=
    short_log_window_polynomial hA hc (Nat.cast_nonneg q) hqs
  have hcap : L ≤ 11 * M ^ 2 :=
    hLq.trans (short_log_window_allowance_bound hA hc (Nat.cast_nonneg q) hqs)
  have hpow := pow_le_pow_left₀ hL hcap 6
  have hpow' : L ^ 6 ≤ (11 : ℝ) ^ 6 * M ^ 12 := by
    simpa only [mul_pow, ← pow_mul, show (2 : ℕ) * 6 = 12 by norm_num] using hpow
  have hM12 : 1 ≤ M ^ 12 := one_le_pow₀ hM
  have hpoly : 1 + L ^ 6 ≤ (1 + (11 : ℝ) ^ 6) * M ^ 12 := by linarith
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hd : (0 : ℝ) < (k + q : ℕ) := by positivity
  have hhalf : ((k + q : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    have he : ((k + q : ℕ) : ℝ) = (k : ℝ) + q := by push_cast; rfl
    linarith
  let U := simplexNearLeadingConstant * (1 + (11 : ℝ) ^ 6) * M ^ 12
  have hU : 0 ≤ U := by dsimp [U]; have := simplexNearLeadingConstant_pos; positivity
  have hfrac : U / k ≤ 2 * U / (k + q : ℕ) := by
    apply (div_le_div_iff₀ hkR hd).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hU
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  calc
    _ ≤ simplexNearLeadingConstant * (1 + L ^ 6) / k :=
      simplex_leading_occupancy_prefix_bound hk hq hL
    _ ≤ U / k := by
      apply div_le_div_of_nonneg_right _ hkR.le
      simpa only [U, mul_assoc] using
        mul_le_mul_of_nonneg_left hpoly simplexNearLeadingConstant_pos.le
    _ ≤ 2 * U / (k + q : ℕ) := hfrac
    _ = _ := by dsimp [U, M]; ring

end FreezingGrowth.PWIT
