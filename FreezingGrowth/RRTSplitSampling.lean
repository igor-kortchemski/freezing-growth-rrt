module

public import FreezingGrowth.RRTSplitRoughGap
public import FreezingGrowth.RRTSharpHeight

/-! The uniform component-size tag and its actual first-component height.
All probability formulas are derived from the proved first-edge split law. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable def uniformIndexLaw (n : ℕ) : Measure ℕ :=
  Measure.uniformOfFinset (Finset.range (n + 1))

instance uniformIndexLaw_probability (n : ℕ) : IsProbabilityMeasure (uniformIndexLaw n) := by
  constructor
  rw [uniformIndexLaw, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_range]
  exact ENNReal.div_self (by positivity) (by finiteness)

theorem uniformIndexLaw_real (n : ℕ) (E : Set ℕ) :
    (uniformIndexLaw n).real E = ((Finset.range (n + 1)).filter (fun i => i ∈ E)).card /
      ((n : ℝ) + 1) := by
  unfold Measure.real uniformIndexLaw
  rw [Measure.uniformOfFinset_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, Finset.card_range, Nat.cast_add, Nat.cast_one]

theorem uniformIndexLaw_real_eq_sum (n : ℕ) (E : Set ℕ) :
    (uniformIndexLaw n).real E = (1 / ((n : ℝ) + 1)) *
      ∑ i ∈ Finset.range (n + 1), if i ∈ E then (1 : ℝ) else 0 := by
  have he : (∑ i ∈ Finset.range (n + 1), if i ∈ E then (1 : ℝ) else 0) =
      (((Finset.range (n + 1)).filter (fun i => i ∈ E)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [uniformIndexLaw_real, he]
  ring

/-- Exact finite counting includes the zero-sized component. -/
theorem uniformIndexLaw_ratio_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (uniformIndexLaw n).real {i | ((i : ℝ) + 1) / ((n : ℝ) + 1) ≤ r} ≤ r := by
  let s := (Finset.range (n + 1)).filter
    (fun i : ℕ => ((i : ℝ) + 1) / ((n : ℝ) + 1) ≤ r)
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfloor : (s.image Nat.succ) ⊆ Finset.Icc 1 ⌊r * ((n : ℝ) + 1)⌋₊ := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hh := (Finset.mem_filter.mp hi).2
    have hreal : ((i + 1 : ℕ) : ℝ) ≤ r * ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (div_le_iff₀ hN).mp hh
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hreal⟩
  have hcard := Finset.card_le_card hfloor
  rw [Finset.card_image_of_injective _ Nat.succ_injective] at hcard
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  have hreal : (s.card : ℝ) ≤ r * ((n : ℝ) + 1) :=
    (Nat.cast_le.mpr hcard).trans (Nat.floor_le (mul_nonneg hr hN.le))
  rw [uniformIndexLaw_real]
  exact (div_le_iff₀ hN).mpr hreal

noncomputable def sampledHeightLaw (n : ℕ) : Measure (ℕ × ℕ) :=
  (Forward.treeLaw RRT.allAttach (n + 1)).map
    (fun s => ((firstEdgeSplit n s).1, Forward.treeHeight (firstEdgeSplit n s).2.1))

instance sampledHeightLaw_probability (n : ℕ) : IsProbabilityMeasure (sampledHeightLaw n) :=
  Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

theorem sampledHeightLaw_eq_sum (n : ℕ) :
    sampledHeightLaw n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ i ∈ Finset.range (n + 1), (Forward.heightLaw RRT.allAttach i).map (Prod.mk i) := by
  let F : Result → ℕ × ℕ := fun z => (z.1, Forward.treeHeight z.2.1)
  have hH : Measurable (Forward.treeHeight : Forward.State → ℕ) := measurable_from_top
  have hF : Measurable F := measurable_fst.prodMk
    (hH.comp (measurable_fst.comp measurable_snd))
  have hsplit : Measurable (firstEdgeSplit n) := measurable_from_top
  change (Forward.treeLaw RRT.allAttach (n + 1)).map (F ∘ firstEdgeSplit n) = _
  rw [← Measure.map_map hF hsplit, treeLaw_firstEdgeSplit,
    mixtureLaw_eq_sum, Measure.map_smul _ hF.aemeasurable,
    Measure.map_finset_sum hF.aemeasurable]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [componentLaw, Measure.map_map hF measurable_prodMk_left]
  have he : F ∘ Prod.mk i =
      (Prod.mk i ∘ Forward.treeHeight) ∘ (Prod.fst : Forward.State × Forward.State → Forward.State) := rfl
  rw [he, ← Measure.map_map measurable_from_top measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, Forward.heightLaw, Measure.map_map measurable_prodMk_left measurable_from_top]

theorem sampledHeightLaw_real_eq_sum (n : ℕ) (E : Set (ℕ × ℕ)) :
    (sampledHeightLaw n).real E = (1 / ((n : ℝ) + 1)) *
      ∑ i ∈ Finset.range (n + 1), (Forward.heightLaw RRT.allAttach i).real {h | (i, h) ∈ E} := by
  unfold Measure.real
  rw [sampledHeightLaw_eq_sum, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
  · simp only [Nat.cast_add, Nat.cast_one, one_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.map_apply measurable_prodMk_left (by measurability)]
    rfl
  · intro i _
    finiteness

theorem heightPairLaw_real_eq_sum (n : ℕ) (E : Set (ℕ × ℕ)) :
    (heightPairLaw n).real E = (1 / ((n : ℝ) + 1)) *
      ∑ i ∈ Finset.range (n + 1),
        ((Forward.heightLaw RRT.allAttach i).prod
          (Forward.heightLaw RRT.allAttach (n - i))).real E := by
  unfold Measure.real
  rw [heightPairLaw_eq_sum, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
  · simp only [Nat.cast_add, Nat.cast_one, one_div]
  · intro i _
    finiteness

noncomputable def sampledHeightDeviation (n : ℕ) (t : ℝ) : ℝ :=
  (sampledHeightLaw n).real {z | t ≤ |(z.2 : ℝ) - RRT.meanHeight z.1|}

noncomputable def sampledMeanDeviation (n : ℕ) (t : ℝ) : ℝ :=
  (uniformIndexLaw n).real {i | t ≤ |RRT.meanHeight i - RRT.meanHeight n|}

theorem sampledHeightDeviation_eq_sum (n : ℕ) (t : ℝ) :
    sampledHeightDeviation n t = (1 / ((n : ℝ) + 1)) *
      ∑ i ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach i).real {h | t ≤ |(h : ℝ) - RRT.meanHeight i|} :=
  sampledHeightLaw_real_eq_sum n _

theorem height_pair_triangle_four (a b u v M : ℝ) :
    |a - b| ≤ |a - u| + |b - v| + |u - M| + |v - M| := by
  have h₁ := le_abs_self (a - u)
  have h₂ := neg_le_abs (a - u)
  have h₃ := le_abs_self (b - v)
  have h₄ := neg_le_abs (b - v)
  have h₅ := le_abs_self (u - M)
  have h₆ := neg_le_abs (u - M)
  have h₇ := le_abs_self (v - M)
  have h₈ := neg_le_abs (v - M)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem heightPair_product_tail_le (i j : ℕ) (M k : ℝ) :
    ((Forward.heightLaw RRT.allAttach i).prod (Forward.heightLaw RRT.allAttach j)).real
        {p | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ≤
      (Forward.heightLaw RRT.allAttach i).real {h | k / 4 ≤ |(h : ℝ) - RRT.meanHeight i|} +
      (Forward.heightLaw RRT.allAttach j).real {h | k / 4 ≤ |(h : ℝ) - RRT.meanHeight j|} +
      (if k / 4 ≤ |RRT.meanHeight i - M| then 1 else 0) +
      (if k / 4 ≤ |RRT.meanHeight j - M| then 1 else 0) := by
  let μ := (Forward.heightLaw RRT.allAttach i).prod (Forward.heightLaw RRT.allAttach j)
  have hp₁ : 0 ≤ (Forward.heightLaw RRT.allAttach i).real
      {h | k / 4 ≤ |(h : ℝ) - RRT.meanHeight i|} := measureReal_nonneg
  have hp₂ : 0 ≤ (Forward.heightLaw RRT.allAttach j).real
      {h | k / 4 ≤ |(h : ℝ) - RRT.meanHeight j|} := measureReal_nonneg
  by_cases hi : k / 4 ≤ |RRT.meanHeight i - M|
  · rw [ite_eq_left hi]
    apply measureReal_le_one.trans
    split_ifs <;> linarith
  · rw [ite_eq_right hi]
    by_cases hj : k / 4 ≤ |RRT.meanHeight j - M|
    · rw [ite_eq_left hj]
      apply measureReal_le_one.trans

      linarith
    · rw [ite_eq_right hj, add_zero, add_zero]
      let A : Set (ℕ × ℕ) := {h : ℕ | k / 4 ≤ |(h : ℝ) - RRT.meanHeight i|} ×ˢ Set.univ
      let B : Set (ℕ × ℕ) := Set.univ ×ˢ {h : ℕ | k / 4 ≤ |(h : ℝ) - RRT.meanHeight j|}
      have hsub : {p : ℕ × ℕ | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ⊆ A ∪ B := by
        intro p hp
        by_cases ha : k / 4 ≤ |(p.1 : ℝ) - RRT.meanHeight i|
        · exact Or.inl ⟨ha, Set.mem_univ _⟩
        · right
          refine ⟨Set.mem_univ _, ?_⟩
          by_contra hb
          have hh := height_pair_triangle_four (p.1 : ℝ) (p.2 : ℝ)
            (RRT.meanHeight i) (RRT.meanHeight j) M
          change k ≤ |(p.1 : ℝ) - (p.2 : ℝ)| at hp
          change ¬k / 4 ≤ |(p.2 : ℝ) - RRT.meanHeight j| at hb
          linarith [lt_of_not_ge hi, lt_of_not_ge hj, lt_of_not_ge ha, lt_of_not_ge hb]
      calc
        _ ≤ μ.real (A ∪ B) := measureReal_mono hsub
        _ ≤ μ.real A + μ.real B := measureReal_union_le _ _
        _ = _ := by
          simp only [μ, A, B, measureReal_prod_prod, probReal_univ, mul_one, one_mul]

theorem sum_range_complement (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), f (n - i)) = ∑ i ∈ Finset.range (n + 1), f i := by
  simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect f (n + 1)

/-- LP3: the exact source four-term decomposition after averaging the actual
uniform size and using its reflection symmetry. -/
theorem heightPair_tail_le_sampled_deviations (n : ℕ) (k : ℝ) :
    (heightPairLaw n).real {p | k ≤ |(p.1 : ℝ) - (p.2 : ℝ)|} ≤
      2 * sampledHeightDeviation n (k / 4) + 2 * sampledMeanDeviation n (k / 4) := by
  rw [heightPairLaw_real_eq_sum, sampledHeightDeviation_eq_sum,
    sampledMeanDeviation, uniformIndexLaw_real_eq_sum]
  have hrow := Finset.sum_le_sum (s := Finset.range (n + 1))
    (fun i _ => heightPair_product_tail_le i (n - i) (RRT.meanHeight n) k)
  simp only [Finset.sum_add_distrib, Set.mem_ofPred_eq] at hrow ⊢
  rw [sum_range_complement n (fun i => (Forward.heightLaw RRT.allAttach i).real
    {h | k / 4 ≤ |(h : ℝ) - RRT.meanHeight i|}),
    sum_range_complement n (fun i => if k / 4 ≤ |RRT.meanHeight i - RRT.meanHeight n| then (1 : ℝ) else 0)] at hrow
  have hh := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity)
  linarith

end FreezingGrowth.RRTSplit
