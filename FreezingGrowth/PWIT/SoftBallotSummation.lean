module

public import FreezingGrowth.PWIT.LogBallotKernel

/-! The actual cyclic occupancy terms, split into summable and short-suffix
contributions. All constants are uniform in dimension and barrier parameters. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped Classical BigOperators

noncomputable def shortLogBallotConstant : ℝ :=
  2 * simplexNearLeadingConstant * (1 + (11 : ℝ) ^ 6)

theorem shortLogBallotConstant_pos : 0 < shortLogBallotConstant := by
  unfold shortLogBallotConstant
  have := simplexNearLeadingConstant_pos
  positivity

theorem simplex_log_point_bound {d : ℕ} [NeZero d]
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hlarge : 42 * (1 + A + c) ^ 2 < (d : ℝ)) (r : Fin d) :
    (simplexLaw d).real {p | minimumAt (simplexCenteredBridge p) 0 ∧
        simplexCenteredBridge p r - simplexCenteredBridge p 0 ≤ logBarrierAllowance A c r} ≤
      (if r = 0 then 1 / (d : ℝ) else 0) +
        (4 * twoBlockOccupancyConstant * (1 + A + c) ^ 13 / (d : ℝ)) *
          logBallotWeight 13 (min r.val (d - r.val)) +
        (shortLogBallotConstant * (1 + A + c) ^ 12 / (d : ℝ)) *
          (if ((d - r.val : ℕ) : ℝ) ≤ 21 * (1 + A + c) ^ 2 then 1 else 0) := by
  by_cases hr : r = 0
  · subst r
    have hshort : ¬(d : ℝ) ≤ 21 * (1 + A + c) ^ 2 := by
      nlinarith [sq_nonneg (1 + A + c)]
    have hh := (simplex_zero_position_probability (d := d) hA).le
    simpa [logBarrierAllowance, logBallotWeight, hshort] using hh
  · rw [ite_eq_right hr, zero_add]
    rcases r with ⟨k, hkd⟩
    have hk : 0 < k := by
      have hk0 : k ≠ 0 := by intro hk0; apply hr; exact Fin.ext hk0
      omega
    obtain ⟨q, he⟩ := Nat.exists_eq_add_of_le hkd.le
    subst d
    have hq : 0 < q := by omega
    let L := A + c * Real.log ((min k q : ℕ) + 1 : ℝ)
    simp only [logBarrierAllowance, Nat.add_sub_cancel_left]
    rw [simplex_near_position_probability_eq_occupancy hk hq L]
    have hgoodnonneg : 0 ≤
        (4 * twoBlockOccupancyConstant * (1 + A + c) ^ 13 / ((k + q : ℕ) : ℝ)) *
          logBallotWeight 13 (min k q) := by
      apply mul_nonneg _ (logBallotWeight_nonneg 13 _)
      have := twoBlockOccupancyConstant_pos
      positivity
    by_cases hgood : 2 * L ≤ (q : ℝ)
    · apply (simplex_log_occupancy_le_weight hk hq hA hc hgood).trans
      apply le_add_of_nonneg_right
      split_ifs <;> have := shortLogBallotConstant_pos <;> positivity
    · have hbad : (q : ℝ) ≤ 2 * L := (lt_of_not_ge hgood).le
      have hqbound : (q : ℝ) ≤ 21 * (1 + A + c) ^ 2 := by
        have hh := logBarrierAllowance_short_suffix hA hc (⟨k, hkd⟩ : Fin (k + q))
          (by simpa only [logBarrierAllowance, Fin.val_mk, Nat.add_sub_cancel_left] using hbad)
        simpa only [Nat.add_sub_cancel_left] using hh
      rw [ite_eq_left hqbound, mul_one]
      have hh := simplex_log_occupancy_short_suffix hk hq hA hc hlarge hbad
      change (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) ≤
        _ + shortLogBallotConstant * (1 + A + c) ^ 12 / ((k + q : ℕ) : ℝ)
      exact hh.trans (by
        unfold shortLogBallotConstant
        exact le_add_of_nonneg_left hgoodnonneg)

noncomputable def logSoftBallotConstant : ℝ :=
  43 + 8 * twoBlockOccupancyConstant * logBallotSum 13 + 22 * shortLogBallotConstant

theorem logSoftBallotConstant_ge_forty_two : 42 ≤ logSoftBallotConstant := by
  have hg := twoBlockOccupancyConstant_pos
  have hs := logBallotSum_pos 13
  have hb := shortLogBallotConstant_pos
  have hgood : 0 ≤ 8 * twoBlockOccupancyConstant * logBallotSum 13 := by positivity
  have hbad : 0 ≤ 22 * shortLogBallotConstant := by positivity
  unfold logSoftBallotConstant
  linarith

/-- The actual simplex bridge has the uniform logarithmic-ballot bound.
Its fixed degree is fourteen and all dimensions, including one, are retained. -/
theorem simplex_log_ballot_bound {d : ℕ} [NeZero d]
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) :
    (simplexLaw d).real {p | softBridge (logBarrierAllowance A c) (simplexCenteredBridge p)} ≤
      logSoftBallotConstant * (1 + A + c) ^ 14 / (d : ℝ) := by
  let M := 1 + A + c
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hM0 : 0 ≤ M := by linarith
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hM14 : 1 ≤ M ^ 14 := one_le_pow₀ hM
  have hM13 : M ^ 13 ≤ M ^ 14 := by
    have hh := mul_le_mul_of_nonneg_left hM (pow_nonneg hM0 13)
    simpa only [mul_one, ← pow_succ] using hh
  by_cases hlarge : 42 * M ^ 2 < (d : ℝ)
  · let α := 4 * twoBlockOccupancyConstant * M ^ 13 / (d : ℝ)
    let β := shortLogBallotConstant * M ^ 12 / (d : ℝ)
    have hα : 0 ≤ α := by dsimp [α]; have := twoBlockOccupancyConstant_pos; positivity
    have hβ : 0 ≤ β := by dsimp [β]; have := shortLogBallotConstant_pos; positivity
    have hweights : (∑ r : Fin d, logBallotWeight 13 (min r.val (d - r.val))) ≤
        2 * logBallotSum 13 := by
      rw [Fin.sum_univ_eq_sum_range (fun k => logBallotWeight 13 (min k (d - k)))]
      exact sum_min_logBallotWeight_le 13 d (Finset.range d)
        (fun k hk => (Finset.mem_range.mp hk).le)
    have hshort : (∑ r : Fin d,
        if ((d - r.val : ℕ) : ℝ) ≤ 21 * M ^ 2 then (1 : ℝ) else 0) ≤ 22 * M ^ 2 := by
      have hh := sum_short_suffix_indicators_le d (show 0 ≤ 21 * M ^ 2 by positivity)
      have hm2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
      exact hh.trans (by linarith)
    have hsum : (∑ r : Fin d, (simplexLaw d).real
        {p | minimumAt (simplexCenteredBridge p) 0 ∧
          simplexCenteredBridge p r - simplexCenteredBridge p 0 ≤ logBarrierAllowance A c r}) ≤
        1 / (d : ℝ) + α * (2 * logBallotSum 13) + β * (22 * M ^ 2) := by
      calc
        _ ≤ ∑ r : Fin d, ((if r = 0 then 1 / (d : ℝ) else 0) +
            α * logBallotWeight 13 (min r.val (d - r.val)) +
            β * (if ((d - r.val : ℕ) : ℝ) ≤ 21 * M ^ 2 then 1 else 0)) :=
          Finset.sum_le_sum (fun r _ => simplex_log_point_bound hA hc hlarge r)
        _ = 1 / (d : ℝ) + α * (∑ r : Fin d, logBallotWeight 13 (min r.val (d - r.val))) +
            β * (∑ r : Fin d, if ((d - r.val : ℕ) : ℝ) ≤ 21 * M ^ 2 then 1 else 0) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
        _ ≤ _ := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hweights hα))
          (mul_le_mul_of_nonneg_left hshort hβ)
    apply (simplex_softBridge_probability_le_sum (logBarrierAllowance A c)
      (logBarrierAllowance_neg A c)).trans (hsum.trans _)
    have he : 1 / (d : ℝ) + α * (2 * logBallotSum 13) + β * (22 * M ^ 2) =
        (1 + (8 * twoBlockOccupancyConstant * logBallotSum 13) * M ^ 13 +
          (22 * shortLogBallotConstant) * M ^ 14) / (d : ℝ) := by
      dsimp [α, β]
      ring
    rw [he]
    apply div_le_div_of_nonneg_right _ hd.le
    have hgood : 0 ≤ 8 * twoBlockOccupancyConstant * logBallotSum 13 := by
      have := twoBlockOccupancyConstant_pos
      have := logBallotSum_pos 13
      positivity
    have hh := mul_le_mul_of_nonneg_left hM13 hgood
    calc
      _ ≤ M ^ 14 + (8 * twoBlockOccupancyConstant * logBallotSum 13) * M ^ 14 +
          (22 * shortLogBallotConstant) * M ^ 14 :=
        add_le_add (add_le_add hM14 hh) le_rfl
      _ = (1 + 8 * twoBlockOccupancyConstant * logBallotSum 13 +
          22 * shortLogBallotConstant) * M ^ 14 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by unfold logSoftBallotConstant; linarith) (pow_nonneg hM0 _)
  · have hM2 : M ^ 2 ≤ M ^ 14 := by
      have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M ^ 12)
        (pow_nonneg hM0 2)
      simpa only [mul_one, ← pow_add, show (2 : ℕ) + 12 = 14 by norm_num] using hh
    apply measureReal_le_one.trans
    apply (le_div_iff₀ hd).mpr
    rw [one_mul]
    change (d : ℝ) ≤ logSoftBallotConstant * M ^ 14
    calc
      (d : ℝ) ≤ 42 * M ^ 2 := le_of_not_gt hlarge
      _ ≤ 42 * M ^ 14 := mul_le_mul_of_nonneg_left hM2 (by norm_num)
      _ ≤ logSoftBallotConstant * M ^ 14 := mul_le_mul_of_nonneg_right
        logSoftBallotConstant_ge_forty_two (pow_nonneg hM0 _)

theorem exists_simplex_log_ballot_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) [NeZero d], ∀ A c : ℝ, 0 ≤ A → 0 ≤ c →
      (simplexLaw d).real {p | softBridge (logBarrierAllowance A c) (simplexCenteredBridge p)} ≤
        C * (1 + A + c) ^ 14 / (d : ℝ) := by
  refine ⟨logSoftBallotConstant, by have := logSoftBallotConstant_ge_forty_two; linarith, ?_⟩
  intro d hd A c hA hc
  exact @simplex_log_ballot_bound d hd A c hA hc

end FreezingGrowth.PWIT
