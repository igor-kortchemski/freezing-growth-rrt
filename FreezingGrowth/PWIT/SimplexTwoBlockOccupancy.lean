module

public import FreezingGrowth.PWIT.SimplexTwoBlockBand

/-! Near-zero occupancy on a genuinely leading simplex bridge, obtained from
independent internal bridges and a positive Gamma total band. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

theorem canonical_twoBlock_leading_factors {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {p : Fin k → ℝ} {r : Fin q → ℝ} (hp : totalWait p = 1) (hr : totalWait r = 1)
    {y L : ℝ} (hy : 0 ≤ y) (hyL : y ≤ L) (hLq : 2 * L ≤ (q : ℝ))
    (h : vectorLeading 0 (Fin.append (((k : ℝ) + y) • p) (((q : ℝ) - y) • r))) :
    p ∈ simplexNearLeadingEvent k L ∧ r ∈ simplexNearLeadingEvent q (2 * L) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hnR : (0 : ℝ) < (k + q : ℕ) := by positivity
  have hL : 0 ≤ L := hy.trans hyL
  have hspos : 0 < (k : ℝ) + y := by linarith
  have htpos : 0 < (q : ℝ) - y := by linarith
  have hs : (∑ i, (((k : ℝ) + y) • p) i) = (k : ℝ) + y := by
    change totalWait (((k : ℝ) + y) • p) = _
    rw [totalWait_smul, hp, mul_one]
  have ht : (∑ i, (((q : ℝ) - y) • r) i) = (q : ℝ) - y := by
    change totalWait (((q : ℝ) - y) • r) = _
    rw [totalWait_smul, hr, mul_one]
  have hdelta : (k : ℝ) + y - (k : ℝ) / (k + q : ℕ) *
      (((k : ℝ) + y) + ((q : ℝ) - y)) = y := by
    push_cast
    field_simp
    ring
  have hb := vectorLeading_split hk hq h
  dsimp only at hb
  rw [hs, ht, hdelta] at hb
  have hfirst : y / ((k : ℝ) + y) ≤ L / (k : ℝ) := by
    apply (div_le_div_iff₀ hspos hkR).mpr
    nlinarith [mul_nonneg hL hy, mul_nonneg hkR.le (sub_nonneg.mpr hyL)]
  have hsecond : y / ((q : ℝ) - y) ≤ (2 * L) / (q : ℝ) := by
    apply (div_le_div_iff₀ htpos hqR).mpr
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hLq),
      mul_nonneg (show 0 ≤ (q : ℝ) + 2 * L by linarith) (sub_nonneg.mpr hyL)]
  constructor
  · apply (vectorLeading_smul_iff hkR L p).mpr
    exact vectorLeading_mono hfirst ((vectorLeading_smul_iff hspos y p).mp hb.2.1)
  · apply (vectorLeading_smul_iff hqR (2 * L) r).mpr
    exact vectorLeading_mono hsecond ((vectorLeading_smul_iff htpos y r).mp hb.2.2)

private theorem vectorPrefix_at_length {d : ℕ} (x : Fin d → ℝ) :
    ((List.ofFn x).take d).sum = totalWait x := by
  have hh : (List.ofFn x).take d = List.ofFn x := by
    simpa only [List.length_ofFn] using List.take_length (l := List.ofFn x)
  rw [hh, List.sum_ofFn]
  rfl

theorem twoBlock_normalized_form {k q : ℕ} (z : TwoBlockBridgeSample k q)
    (hp : totalWait z.1.1 = 1) (hr : totalWait z.2.1 = 1) :
    totalWait (twoBlockReconstruction z) = z.1.2 + z.2.2 ∧
      normalizedSpacings (twoBlockReconstruction z) =
        (1 / (z.1.2 + z.2.2)) • twoBlockReconstruction z := by
  have ht : totalWait (twoBlockReconstruction z) = z.1.2 + z.2.2 := by
    rw [twoBlockReconstruction, totalWait_append, totalWait_smul, totalWait_smul,
      hp, hr, mul_one, mul_one]
  refine ⟨ht, ?_⟩
  funext i
  simp only [normalizedSpacings, ht, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem twoBlock_normalized_surplus {k q : ℕ} (z : TwoBlockBridgeSample k q)
    (hp : totalWait z.1.1 = 1) (hr : totalWait z.2.1 = 1) :
    simplexSplitSurplus k q (normalizedSpacings (twoBlockReconstruction z)) =
      ((k + q : ℕ) : ℝ) / (z.1.2 + z.2.2) * z.1.2 - k := by
  rw [simplexSplitSurplus, (twoBlock_normalized_form z hp hr).2,
    vectorPrefix_smul _ _ k (by omega), twoBlockReconstruction,
    vectorPrefix_append_left _ _ k le_rfl, vectorPrefix_at_length, totalWait_smul, hp, mul_one]
  ring

/-- A leading global bridge in the low-occupancy event forces the two
independent internal near-leading events and the raw slanted Gamma band. -/
theorem twoBlock_occupancy_inclusion {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (_hL : 0 ≤ L) (hLq : 2 * L ≤ (q : ℝ))
    (z : TwoBlockBridgeSample k q) (hp : z.1.1 ∈ simplexSupport k)
    (hr : z.2.1 ∈ simplexSupport q)
    (hocc : normalizedSpacings (twoBlockReconstruction z) ∈ simplexLeadingOccupancy k q L)
    (hband : totalWait (twoBlockReconstruction z) ∈
      Icc ((k + q : ℕ) : ℝ) (((k + q : ℕ) : ℝ) + 1)) :
    z.1.1 ∈ simplexNearLeadingEvent k L ∧
      z.2.1 ∈ simplexNearLeadingEvent q (2 * L) ∧
      (z.1.2, z.2.2) ∈ gammaTwoBlockBand k q L := by
  let N : ℝ := (k + q : ℕ)
  let T : ℝ := z.1.2 + z.2.2
  let y : ℝ := simplexSplitSurplus k q (normalizedSpacings (twoBlockReconstruction z))
  have hn : 0 < N := by dsimp [N]; positivity
  have htot := (twoBlock_normalized_form z hp.2 hr.2).1
  have hT : T ∈ Icc N (N + 1) := by simpa only [htot] using hband
  have hTp : 0 < T := hn.trans_le hT.1
  have hy : 0 ≤ y := hocc.2.1
  have hyL : y ≤ L := hocc.2.2
  have hyform : y = N / T * z.1.2 - k := twoBlock_normalized_surplus z hp.2 hr.2
  have hfirst : N / T * z.1.2 = (k : ℝ) + y := by linarith
  have hsecond : N / T * z.2.2 = (q : ℝ) - y := by
    have hsum : N / T * z.1.2 + N / T * z.2.2 = N := by
      rw [← mul_add]
      change N / T * T = N
      exact div_mul_cancel₀ _ hTp.ne'
    have hN : N = (k : ℝ) + q := by dsimp [N]; push_cast; rfl
    linarith
  have hcanon : N • normalizedSpacings (twoBlockReconstruction z) =
      Fin.append (((k : ℝ) + y) • z.1.1) (((q : ℝ) - y) • z.2.1) := by
    rw [(twoBlock_normalized_form z hp.2 hr.2).2, smul_smul,
      show N * (1 / (z.1.2 + z.2.2)) = N / T by dsimp [T]; ring,
      twoBlockReconstruction, smul_append_vector, smul_smul, smul_smul, hfirst, hsecond]
  have hcanLead : vectorLeading 0
      (Fin.append (((k : ℝ) + y) • z.1.1) (((q : ℝ) - y) • z.2.1)) := by
    rw [← hcanon, vectorLeading_smul_iff hn, zero_div]
    exact hocc.1
  obtain ⟨h₁, h₂⟩ := canonical_twoBlock_leading_factors hk hq hp.2 hr.2 hy hyL hLq hcanLead
  refine ⟨h₁, h₂, ?_⟩
  have hs : N * z.1.2 = T * ((k : ℝ) + y) := by
    have hh := congrArg (fun a : ℝ => a * T) hfirst
    field_simp at hh
    nlinarith
  have hyN : (k : ℝ) + y ≤ N := by dsimp [N]; push_cast; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hslo : (k : ℝ) ≤ z.1.2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hT.1) hk0
    have hm' := mul_nonneg hTp.le hy
    nlinarith
  have hsup : z.1.2 ≤ (k : ℝ) + L + 1 := by
    have hm := mul_nonneg (show 0 ≤ N + 1 - T by linarith [hT.2])
      (show 0 ≤ (k : ℝ) + y by positivity)
    have hm' := mul_nonneg hn.le (sub_nonneg.mpr hyL)
    nlinarith
  exact ⟨⟨hslo, hsup⟩, hT⟩

theorem twoBlockBridgeLaw_ae_support (k q : ℕ) [NeZero k] [NeZero q] :
    ∀ᵐ z ∂twoBlockBridgeLaw k q,
      z.1.1 ∈ simplexSupport k ∧ z.2.1 ∈ simplexSupport q := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  have h₁ : ∀ᵐ z ∂(simplexLaw k).prod (gammaMeasure (k : ℝ) 1),
      z.1 ∈ simplexSupport k :=
    (measurePreserving_fst (μ := simplexLaw k) (ν := gammaMeasure (k : ℝ) 1)).quasiMeasurePreserving.ae
      (simplexLaw_ae_nonnegative_sum_one k)
  have h₂ : ∀ᵐ z ∂(simplexLaw q).prod (gammaMeasure (q : ℝ) 1),
      z.1 ∈ simplexSupport q :=
    (measurePreserving_fst (μ := simplexLaw q) (ν := gammaMeasure (q : ℝ) 1)).quasiMeasurePreserving.ae
      (simplexLaw_ae_nonnegative_sum_one q)
  have ha := (measurePreserving_fst
    (μ := (simplexLaw k).prod (gammaMeasure (k : ℝ) 1))
    (ν := (simplexLaw q).prod (gammaMeasure (q : ℝ) 1))).quasiMeasurePreserving.ae h₁
  have hb := (measurePreserving_snd
    (μ := (simplexLaw k).prod (gammaMeasure (k : ℝ) 1))
    (ν := (simplexLaw q).prod (gammaMeasure (q : ℝ) 1))).quasiMeasurePreserving.ae h₂
  exact ha.and hb

/-- The positive total-band factor is retained before dividing. This is an
ordinary product-measure inequality, with no singleton conditioning. -/
theorem simplex_occupancy_band_inequality {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) (hLq : 2 * L ≤ (q : ℝ)) :
    (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) *
        (gammaMeasure ((k + q : ℕ) : ℝ) 1).real
          (Icc ((k + q : ℕ) : ℝ) (((k + q : ℕ) : ℝ) + 1)) ≤
      (simplexLaw k).real (simplexNearLeadingEvent k L) *
        (simplexLaw q).real (simplexNearLeadingEvent q (2 * L)) *
        ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)).real
          (gammaTwoBlockBand k q L) := by
  let : NeZero k := ⟨hk.ne'⟩
  let : NeZero q := ⟨hq.ne'⟩
  let N : ℝ := (k + q : ℕ)
  have : IsProbabilityMeasure (gammaMeasure N 1) :=
    isProbabilityMeasure_gammaMeasure (by dsimp [N]; positivity) (by norm_num)
  let E := simplexLeadingOccupancy k q L
  let B := Icc N (N + 1)
  let F : TwoBlockBridgeSample k q → (Fin (k + q) → ℝ) × ℝ :=
    fun z => (normalizedSpacings (twoBlockReconstruction z), totalWait (twoBlockReconstruction z))
  have hF : Measurable F := by unfold F; fun_prop
  have hE := measurableSet_simplexLeadingOccupancy k q L
  have hleft : (twoBlockBridgeLaw k q).real (F ⁻¹' (E ×ˢ B)) =
      (simplexLaw (k + q)).real E * (gammaMeasure N 1).real B := by
    rw [← map_measureReal_apply hF (hE.prod measurableSet_Icc),
      twoBlockReconstruction_normalized_joint, measureReal_prod_prod]
  let D := twoBlockRegroup ⁻¹'
    ((simplexNearLeadingEvent k L ×ˢ simplexNearLeadingEvent q (2 * L)) ×ˢ gammaTwoBlockBand k q L)
  have hright : (twoBlockBridgeLaw k q).real D =
      (simplexLaw k).real (simplexNearLeadingEvent k L) *
        (simplexLaw q).real (simplexNearLeadingEvent q (2 * L)) *
        ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)).real (gammaTwoBlockBand k q L) :=
    twoBlock_separated_probability k q (measurableSet_simplexNearLeadingEvent k L)
      (measurableSet_simplexNearLeadingEvent q (2 * L)) (measurableSet_gammaTwoBlockBand k q L)
  rw [← hleft, ← hright]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [twoBlockBridgeLaw_ae_support k q] with z hz
  intro h
  obtain ⟨h₁, h₂, h₃⟩ := twoBlock_occupancy_inclusion hk hq hL hLq z hz.1 hz.2 h.1 h.2
  exact ⟨⟨h₁, h₂⟩, h₃⟩

noncomputable def twoBlockOccupancyConstant : ℝ :=
  256 * simplexNearLeadingConstant ^ 2 / Real.exp (-3)

theorem twoBlockOccupancyConstant_pos : 0 < twoBlockOccupancyConstant := by
  unfold twoBlockOccupancyConstant
  have := simplexNearLeadingConstant_pos
  positivity

/-- Uniform near-zero occupancy on a leading canonical simplex bridge. -/
theorem simplex_leading_occupancy_bound {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) (hLq : 2 * L ≤ (q : ℝ)) :
    (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) ≤
      twoBlockOccupancyConstant * (1 + L) ^ 13 * Real.sqrt ((k + q : ℕ) : ℝ) /
        (((k : ℝ) * Real.sqrt (k : ℝ)) * ((q : ℝ) * Real.sqrt (q : ℝ))) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hn : 0 < k + q := by omega
  have hnR : (0 : ℝ) < (k + q : ℕ) := Nat.cast_pos.mpr hn
  have hc := simplexNearLeadingConstant_pos
  have hbound := simplex_occupancy_band_inequality hk hq hL hLq
  have hγ := gammaMeasure_nat_unitBand_lower hn
  have h₁ := simplex_nearLeading_canonical_bound hk hL
  have h₂ := simplex_nearLeading_canonical_bound hq (show 0 ≤ 2 * L by positivity)
  have h₃ := gammaTwoBlockBand_real_le hk hq hL
  have hupper :
      (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) *
          (Real.exp (-3) / Real.sqrt ((k + q : ℕ) : ℝ)) ≤
        (simplexNearLeadingConstant * (1 + L ^ 6) / k) *
          (simplexNearLeadingConstant * (1 + (2 * L) ^ 6) / q) *
          (4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ))) := by
    apply (mul_le_mul_of_nonneg_left hγ measureReal_nonneg).trans
    apply hbound.trans
    exact mul_le_mul (mul_le_mul h₁ h₂ measureReal_nonneg (by positivity)) h₃
      measureReal_nonneg (by positivity)
  have hpow : 1 + L ^ 6 ≤ (1 + L) ^ 6 := by
    simpa only [one_pow] using pow_add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hL (by decide : 6 ≠ 0)
  have hpow₂ : 1 + (2 * L) ^ 6 ≤ 64 * (1 + L) ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 64)
    rw [show (2 * L) ^ 6 = 64 * L ^ 6 by ring]
    linarith
  have hpoly :
      (simplexNearLeadingConstant * (1 + L ^ 6) / k) *
        (simplexNearLeadingConstant * (1 + (2 * L) ^ 6) / q) *
        (4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ))) ≤
      (simplexNearLeadingConstant * (1 + L) ^ 6 / k) *
        (simplexNearLeadingConstant * (64 * (1 + L) ^ 6) / q) *
        (4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ))) := by
    gcongr
  have hquot := (le_div_iff₀ (by positivity :
    0 < Real.exp (-3) / Real.sqrt ((k + q : ℕ) : ℝ))).mpr (hupper.trans hpoly)
  apply hquot.trans_eq
  unfold twoBlockOccupancyConstant
  field_simp
  ring

theorem exists_simplex_leading_occupancy_bound : ∃ C : ℝ, 0 < C ∧
    ∀ k q : ℕ, 0 < k → 0 < q → ∀ L : ℝ, 0 ≤ L → 2 * L ≤ (q : ℝ) →
      (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) ≤
        C * (1 + L) ^ 13 * Real.sqrt ((k + q : ℕ) : ℝ) /
          (((k : ℝ) * Real.sqrt (k : ℝ)) * ((q : ℝ) * Real.sqrt (q : ℝ))) :=
  ⟨twoBlockOccupancyConstant, twoBlockOccupancyConstant_pos,
    fun _ _ hk hq _ hL hLq => simplex_leading_occupancy_bound hk hq hL hLq⟩

end FreezingGrowth.PWIT
