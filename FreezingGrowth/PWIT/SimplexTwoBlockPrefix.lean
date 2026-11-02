module

public import FreezingGrowth.PWIT.SimplexTwoBlockOccupancy

/-! A one-block bound for leading-bridge occupancy. It covers the short
suffix regime without dividing by an endpoint-band probability. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

theorem canonical_firstBlock_leading_factor {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {p : Fin k → ℝ} {r : Fin q → ℝ} (hp : totalWait p = 1) (hr : totalWait r = 1)
    {y L : ℝ} (hy : 0 ≤ y) (hyL : y ≤ L)
    (h : vectorLeading 0 (Fin.append (((k : ℝ) + y) • p) (((q : ℝ) - y) • r))) :
    p ∈ simplexNearLeadingEvent k L := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hnR : (0 : ℝ) < (k + q : ℕ) := by positivity
  have hL : 0 ≤ L := hy.trans hyL
  have hspos : 0 < (k : ℝ) + y := by linarith
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
  apply (vectorLeading_smul_iff hkR L p).mpr
  exact vectorLeading_mono hfirst ((vectorLeading_smul_iff hspos y p).mp hb.2.1)

theorem twoBlock_normalized_canonical_form {k q : ℕ} (z : TwoBlockBridgeSample k q)
    (hp : totalWait z.1.1 = 1) (hr : totalWait z.2.1 = 1)
    (hT : 0 < totalWait (twoBlockReconstruction z)) :
    let y := simplexSplitSurplus k q (normalizedSpacings (twoBlockReconstruction z))
    ((k + q : ℕ) : ℝ) • normalizedSpacings (twoBlockReconstruction z) =
      Fin.append (((k : ℝ) + y) • z.1.1) (((q : ℝ) - y) • z.2.1) := by
  dsimp only
  let N : ℝ := (k + q : ℕ)
  let T : ℝ := z.1.2 + z.2.2
  let y := simplexSplitSurplus k q (normalizedSpacings (twoBlockReconstruction z))
  have hTp : 0 < T := by rwa [(twoBlock_normalized_form z hp hr).1] at hT
  have hyform : y = N / T * z.1.2 - k := twoBlock_normalized_surplus z hp hr
  have hfirst : N / T * z.1.2 = (k : ℝ) + y := by linarith
  have hsecond : N / T * z.2.2 = (q : ℝ) - y := by
    have hsum : N / T * z.1.2 + N / T * z.2.2 = N := by
      rw [← mul_add]
      change N / T * T = N
      exact div_mul_cancel₀ _ hTp.ne'
    have hN : N = (k : ℝ) + q := by dsimp [N]; push_cast; rfl
    linarith
  change N • normalizedSpacings (twoBlockReconstruction z) =
    Fin.append (((k : ℝ) + y) • z.1.1) (((q : ℝ) - y) • z.2.1)
  rw [(twoBlock_normalized_form z hp hr).2, smul_smul,
    show N * (1 / (z.1.2 + z.2.2)) = N / T by dsimp [T]; ring,
    twoBlockReconstruction, smul_append_vector, smul_smul, smul_smul, hfirst, hsecond]

theorem twoBlock_occupancy_prefix_inclusion {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (z : TwoBlockBridgeSample k q) (hp : z.1.1 ∈ simplexSupport k)
    (hr : z.2.1 ∈ simplexSupport q) (hT : 0 < totalWait (twoBlockReconstruction z))
    (hocc : normalizedSpacings (twoBlockReconstruction z) ∈ simplexLeadingOccupancy k q L) :
    z.1.1 ∈ simplexNearLeadingEvent k L := by
  have hn : (0 : ℝ) < (k + q : ℕ) := by positivity
  have hcanon := twoBlock_normalized_canonical_form z hp.2 hr.2 hT
  have hcanLead : vectorLeading 0 (((k + q : ℕ) : ℝ) •
      normalizedSpacings (twoBlockReconstruction z)) := by
    rw [vectorLeading_smul_iff hn, zero_div]
    exact hocc.1
  rw [hcanon] at hcanLead
  exact canonical_firstBlock_leading_factor hk hq hp.2 hr.2 hocc.2.1 hocc.2.2 hcanLead

theorem twoBlockReconstruction_normalized_marginal (k q : ℕ) [NeZero k] [NeZero q] :
    (twoBlockBridgeLaw k q).map (fun z => normalizedSpacings (twoBlockReconstruction z)) =
      simplexLaw (k + q) := by
  rw [simplexLaw, ← map_twoBlockReconstruction k q,
    Measure.map_map (measurable_normalizedSpacings _) (measurable_twoBlockReconstruction k q)]
  rfl

theorem twoBlockBridgeLaw_firstAngle (k q : ℕ) [NeZero k] [NeZero q] :
    (twoBlockBridgeLaw k q).map (fun z => z.1.1) = simplexLaw k := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  exact ((measurePreserving_fst (μ := simplexLaw k) (ν := gammaMeasure (k : ℝ) 1)).comp
    (measurePreserving_fst (μ := (simplexLaw k).prod (gammaMeasure (k : ℝ) 1))
      (ν := (simplexLaw q).prod (gammaMeasure (q : ℝ) 1)))).map_eq

/-- Only the first internal bridge is retained, so no relation between L
and the suffix length is needed. -/
theorem simplex_leading_occupancy_le_firstBlock {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    (L : ℝ) :
    (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) ≤
      (simplexLaw k).real (simplexNearLeadingEvent k L) := by
  let : NeZero k := ⟨hk.ne'⟩
  let : NeZero q := ⟨hq.ne'⟩
  let : NeZero (k + q) := ⟨by omega⟩
  have hT : ∀ᵐ z ∂twoBlockBridgeLaw k q, 0 < totalWait (twoBlockReconstruction z) :=
    (show MeasurePreserving (@twoBlockReconstruction k q) (twoBlockBridgeLaw k q)
      (finiteClockLaw (k + q)) from
      ⟨measurable_twoBlockReconstruction k q, map_twoBlockReconstruction k q⟩).quasiMeasurePreserving.ae
        (finiteClockLaw_ae_total_pos (k + q))
  have hF : Measurable (fun z : TwoBlockBridgeSample k q =>
      normalizedSpacings (twoBlockReconstruction z)) := by fun_prop
  have hfst : Measurable (fun z : TwoBlockBridgeSample k q => z.1.1) := by fun_prop
  rw [← twoBlockReconstruction_normalized_marginal k q,
    map_measureReal_apply hF (measurableSet_simplexLeadingOccupancy k q L),
    ← twoBlockBridgeLaw_firstAngle k q,
    map_measureReal_apply hfst (measurableSet_simplexNearLeadingEvent k L)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [twoBlockBridgeLaw_ae_support k q, hT] with z hz ht
  exact twoBlock_occupancy_prefix_inclusion hk hq z hz.1 hz.2 ht

theorem simplex_leading_occupancy_prefix_bound {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) :
    (simplexLaw (k + q)).real (simplexLeadingOccupancy k q L) ≤
      simplexNearLeadingConstant * (1 + L ^ 6) / k :=
  (simplex_leading_occupancy_le_firstBlock hk hq L).trans
    (simplex_nearLeading_canonical_bound hk hL)

end FreezingGrowth.PWIT
