module

public import FreezingGrowth.PWIT.GammaBridgeBounds
public import FreezingGrowth.PWIT.SimplexNearLeading

/-! Two independent exponential-clock blocks, their internal normalized
bridges, and a positive-mass band for the total endpoint. No conditional law
at a singleton endpoint is used. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable def simplexSplitSurplus (k q : ℕ) (p : Fin (k + q) → ℝ) : ℝ :=
  ((k + q : ℕ) : ℝ) * ((List.ofFn p).take k).sum - k

def simplexLeadingOccupancy (k q : ℕ) (L : ℝ) : Set (Fin (k + q) → ℝ) :=
  {p | vectorLeading 0 p ∧ 0 ≤ simplexSplitSurplus k q p ∧ simplexSplitSurplus k q p ≤ L}

@[fun_prop] theorem measurable_simplexSplitSurplus (k q : ℕ) :
    Measurable (simplexSplitSurplus k q) := by
  unfold simplexSplitSurplus
  exact (measurable_const.mul (measurable_vectorPrefix k (by omega))).sub measurable_const

theorem measurableSet_simplexLeadingOccupancy (k q : ℕ) (L : ℝ) :
    MeasurableSet (simplexLeadingOccupancy k q L) :=
  (measurableSet_vectorLeading (k + q) 0).inter
    ((measurableSet_le measurable_const (measurable_simplexSplitSurplus k q)).inter
      (measurableSet_le (measurable_simplexSplitSurplus k q) measurable_const))

abbrev TwoBlockBridgeSample (k q : ℕ) :=
  ((Fin k → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ)

noncomputable def twoBlockBridgeLaw (k q : ℕ) : Measure (TwoBlockBridgeSample k q) :=
  ((simplexLaw k).prod (gammaMeasure (k : ℝ) 1)).prod
    ((simplexLaw q).prod (gammaMeasure (q : ℝ) 1))

instance twoBlockBridgeLaw_probability (k q : ℕ) [NeZero k] [NeZero q] :
    IsProbabilityMeasure (twoBlockBridgeLaw k q) := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  unfold twoBlockBridgeLaw
  infer_instance

noncomputable def twoBlockReconstruction {k q : ℕ} (z : TwoBlockBridgeSample k q) :
    Fin (k + q) → ℝ := Fin.append (z.1.2 • z.1.1) (z.2.2 • z.2.1)

@[fun_prop] theorem measurable_twoBlockReconstruction (k q : ℕ) :
    Measurable (@twoBlockReconstruction k q) := by
  unfold twoBlockReconstruction
  have h₁ : Measurable (fun z : TwoBlockBridgeSample k q => z.1.2 • z.1.1) := by fun_prop
  have h₂ : Measurable (fun z : TwoBlockBridgeSample k q => z.2.2 • z.2.1) := by fun_prop
  exact (measurable_append k q).comp (h₁.prodMk h₂)

theorem map_twoBlockReconstruction (k q : ℕ) [NeZero k] [NeZero q] :
    (twoBlockBridgeLaw k q).map twoBlockReconstruction = finiteClockLaw (k + q) := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  let blocks : TwoBlockBridgeSample k q → (Fin k → ℝ) × (Fin q → ℝ) :=
    fun z => (z.1.2 • z.1.1, z.2.2 • z.2.1)
  have hb : Measurable blocks := by unfold blocks; fun_prop
  have hblocks : (twoBlockBridgeLaw k q).map blocks =
      (finiteClockLaw k).prod (finiteClockLaw q) := by
    rw [finiteClockLaw_eq_scaled_simplex_gamma k, finiteClockLaw_eq_scaled_simplex_gamma q]
    unfold twoBlockBridgeLaw
    rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    rfl
  have he : (@twoBlockReconstruction k q) =
      (fun z : (Fin k → ℝ) × (Fin q → ℝ) => Fin.append z.1 z.2) ∘ blocks := rfl
  rw [he, ← Measure.map_map (measurable_append k q) hb, hblocks, map_append_finiteClockLaw]

theorem twoBlockReconstruction_normalized_joint (k q : ℕ) [NeZero k] [NeZero q] :
    (twoBlockBridgeLaw k q).map (fun z =>
      (normalizedSpacings (twoBlockReconstruction z), totalWait (twoBlockReconstruction z))) =
      (simplexLaw (k + q)).prod (gammaMeasure ((k + q : ℕ) : ℝ) 1) := by
  have : NeZero (k + q) := ⟨by have := NeZero.pos k; omega⟩
  rw [← normalizedSpacings_joint_law (k + q), ← map_twoBlockReconstruction k q,
    Measure.map_map (by fun_prop) (measurable_twoBlockReconstruction k q)]
  rfl

def twoBlockRegroup {k q : ℕ} (z : TwoBlockBridgeSample k q) :
    ((Fin k → ℝ) × (Fin q → ℝ)) × (ℝ × ℝ) := ((z.1.1, z.2.1), (z.1.2, z.2.2))

@[fun_prop] theorem measurable_twoBlockRegroup (k q : ℕ) :
    Measurable (@twoBlockRegroup k q) := by unfold twoBlockRegroup; fun_prop

/-- Both internal angles remain independent of both raw Gamma totals. -/
theorem twoBlockBridgeLaw_regroup (k q : ℕ) [NeZero k] [NeZero q] :
    (twoBlockBridgeLaw k q).map twoBlockRegroup =
      ((simplexLaw k).prod (simplexLaw q)).prod
        ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)) := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  let μ := simplexLaw k
  let ν := gammaMeasure (k : ℝ) 1
  let ρ := simplexLaw q
  let τ := gammaMeasure (q : ℝ) 1
  have h₁ := measurePreserving_prodAssoc μ ν (ρ.prod τ)
  have h₂ := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : (ℝ × (Fin q → ℝ)) × ℝ ≃ᵐ ℝ × ((Fin q → ℝ) × ℝ))
    (measurePreserving_prodAssoc ν ρ τ)
  have h₃ := (Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id τ)
  have h₄ := measurePreserving_prodAssoc ρ ν τ
  have hinner := h₄.comp (h₃.comp h₂)
  have h₅ := (MeasurePreserving.id μ).prod hinner
  have h₆ := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : ((Fin k → ℝ) × (Fin q → ℝ)) × (ℝ × ℝ) ≃ᵐ
      (Fin k → ℝ) × ((Fin q → ℝ) × (ℝ × ℝ)))
    (measurePreserving_prodAssoc μ ρ (ν.prod τ))
  exact (h₆.comp (h₅.comp h₁)).map_eq

theorem twoBlock_separated_probability (k q : ℕ) [NeZero k] [NeZero q]
    {A : Set (Fin k → ℝ)} {B : Set (Fin q → ℝ)} {W : Set (ℝ × ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hW : MeasurableSet W) :
    (twoBlockBridgeLaw k q).real (twoBlockRegroup ⁻¹' ((A ×ˢ B) ×ˢ W)) =
      (simplexLaw k).real A * (simplexLaw q).real B *
        ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)).real W := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos k)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos q)) (by norm_num)
  change ((twoBlockBridgeLaw k q) (twoBlockRegroup ⁻¹' ((A ×ˢ B) ×ˢ W))).toReal = _
  rw [← Measure.map_apply (measurable_twoBlockRegroup k q) ((hA.prod hB).prod hW),
    twoBlockBridgeLaw_regroup]
  exact (measureReal_prod_prod (A ×ˢ B) W).trans
    (congrArg (fun r => r * ((gammaMeasure (k : ℝ) 1).prod
      (gammaMeasure (q : ℝ) 1)).real W) (measureReal_prod_prod A B))

/-- Global density control bounds every interval, even one crossing zero. -/
theorem gammaMeasure_nat_Icc_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (_hab : a ≤ b) :
    gammaMeasure (n : ℝ) 1 (Icc a b) ≤ ENNReal.ofReal (2 * (b - a) / Real.sqrt (n : ℝ)) := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ _x in Icc a b, ENNReal.ofReal (2 / Real.sqrt (n : ℝ)) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gammaPDFReal_nat_upper hn x)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

def gammaTwoBlockBand (k q : ℕ) (L : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc (k : ℝ) ((k : ℝ) + L + 1) ∧
    z.1 + z.2 ∈ Icc ((k + q : ℕ) : ℝ) (((k + q : ℕ) : ℝ) + 1)}

theorem measurableSet_gammaTwoBlockBand (k q : ℕ) (L : ℝ) :
    MeasurableSet (gammaTwoBlockBand k q L) := by
  exact (measurableSet_Icc.preimage measurable_fst).inter
    (measurableSet_Icc.preimage (measurable_fst.add measurable_snd))

theorem gammaTwoBlockBand_measure_le {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) :
    ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)) (gammaTwoBlockBand k q L) ≤
      ENNReal.ofReal (4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ))) := by
  have : IsProbabilityMeasure (gammaMeasure (k : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr hk) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (q : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr hq) (by norm_num)
  let I := Icc (k : ℝ) ((k : ℝ) + L + 1)
  let N : ℝ := (k + q : ℕ)
  have hslice (s : ℝ) : Prod.mk s ⁻¹' gammaTwoBlockBand k q L =
      if s ∈ I then Icc (N - s) (N + 1 - s) else ∅ := by
    by_cases hs : s ∈ I
    · rw [ite_eq_left hs]
      ext t
      change (s ∈ I ∧ N ≤ s + t ∧ s + t ≤ N + 1) ↔ N - s ≤ t ∧ t ≤ N + 1 - s
      constructor
      · intro h
        exact ⟨by linarith [h.2.1], by linarith [h.2.2]⟩
      · intro h
        exact ⟨hs, by linarith [h.1], by linarith [h.2]⟩
    · rw [ite_eq_right hs]
      ext t
      change (s ∈ I ∧ N ≤ s + t ∧ s + t ≤ N + 1) ↔ False
      simp only [hs, false_and]
  rw [Measure.prod_apply (measurableSet_gammaTwoBlockBand k q L)]
  calc
    _ ≤ ∫⁻ s, I.indicator (fun _ => ENNReal.ofReal (2 / Real.sqrt (q : ℝ))) s
        ∂gammaMeasure (k : ℝ) 1 := by
      apply lintegral_mono
      intro s
      dsimp only
      rw [hslice]
      by_cases hs : s ∈ I
      · rw [ite_eq_left hs, Set.indicator_of_mem hs]
        have hh := gammaMeasure_nat_Icc_le hq (show N - s ≤ N + 1 - s by linarith)
        convert hh using 1
        congr 1
        ring
      · simp [hs]
    _ = ENNReal.ofReal (2 / Real.sqrt (q : ℝ)) * gammaMeasure (k : ℝ) 1 I := by
      exact lintegral_indicator_const measurableSet_Icc _
    _ ≤ ENNReal.ofReal (2 / Real.sqrt (q : ℝ)) *
        ENNReal.ofReal (2 * (L + 1) / Real.sqrt (k : ℝ)) := by
      gcongr
      have hh := gammaMeasure_nat_Icc_le hk (show (k : ℝ) ≤ (k : ℝ) + L + 1 by linarith)
      convert hh using 1
      congr 1
      ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

theorem gammaTwoBlockBand_real_le {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) :
    ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (q : ℝ) 1)).real
        (gammaTwoBlockBand k q L) ≤
      4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (gammaTwoBlockBand_measure_le hk hq hL)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity :
    0 ≤ 4 * (L + 1) / (Real.sqrt (k : ℝ) * Real.sqrt (q : ℝ)))] using hh

end FreezingGrowth.PWIT
