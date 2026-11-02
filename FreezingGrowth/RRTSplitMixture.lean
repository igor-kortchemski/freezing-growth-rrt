module

public import FreezingGrowth.RRTSplitKernel

/-!
# Uniform size mixture for the first-edge components

The two incoming possibilities for a component size have coefficients adding
to a constant. This proves preservation of the full product-law mixture by
the size-biased two-component growth kernel. The identification with splitting
the actual full recursive tree is a separate, necessary bridge.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem comp_finset_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) (I : Finset ι) (μ : ι → Measure α) :
    κ ∘ₘ (∑ i ∈ I, μ i) = ∑ i ∈ I, κ ∘ₘ μ i := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp only [Finset.sum_insert hi, Measure.comp_add, ih]

/-- The joint law stated in the paper: a uniform root-side edge count and,
conditional on it, two independent recursive trees of the complementary sizes. -/
noncomputable def mixtureLaw (n : ℕ) : Measure Result :=
  (Measure.uniformOfFinset (Finset.range (n + 1))).bind
    (fun k => componentLaw k (n - k))

theorem mixtureLaw_eq_sum (n : ℕ) :
    mixtureLaw n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), componentLaw k (n - k) := by
  let κ : Kernel ℕ Result := ⟨fun k => componentLaw k (n - k), measurable_of_countable _⟩
  change κ ∘ₘ Measure.uniformOfFinset (Finset.range (n + 1)) = _
  rw [Measure.uniformOfFinset, comp_finset_sum]
  simp only [Measure.comp_smul, Finset.card_range, Measure.dirac_bind κ.measurable]
  rw [Finset.smul_sum]
  rfl

theorem mixtureLaw_zero : mixtureLaw 0 =
    Measure.dirac (0, Forward.initial, Forward.initial) := by
  simp [mixtureLaw_eq_sum, componentLaw, Forward.treeLaw,
    Measure.dirac_prod_dirac, Measure.map_dirac' measurable_prodMk_left]

/-- Counting the two predecessor sizes, with the zero-sized endpoints kept. -/
theorem incoming_size_weights (n : ℕ) (f : ℕ → ℝ≥0∞) :
    (∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ≥0∞) * f (k + 1)) +
      (∑ k ∈ Finset.range (n + 1), ((n - k + 1 : ℕ) : ℝ≥0∞) * f k) =
      ((n + 1 : ℕ) : ℝ≥0∞) * ∑ k ∈ Finset.range (n + 2), f k := by
  have hleft : (∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ≥0∞) * f (k + 1)) =
      ∑ k ∈ Finset.range (n + 2), (k : ℝ≥0∞) * f k := by
    rw [show n + 2 = (n + 1) + 1 from rfl,
      Finset.sum_range_succ' (fun k : ℕ => (k : ℝ≥0∞) * f k) (n + 1)]
    simp
  have hright : (∑ k ∈ Finset.range (n + 1), ((n - k + 1 : ℕ) : ℝ≥0∞) * f k) =
      ∑ k ∈ Finset.range (n + 2), ((n + 1 - k : ℕ) : ℝ≥0∞) * f k := by
    rw [show n + 2 = (n + 1) + 1 from rfl,
      Finset.sum_range_succ (fun k : ℕ => ((n + 1 - k : ℕ) : ℝ≥0∞) * f k) (n + 1)]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    congr 2
    omega
  rw [hleft, hright, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← add_mul, ← Nat.cast_add]
  have hk' := Finset.mem_range.mp hk
  congr 2
  omega

theorem incoming_size_probabilities (n : ℕ) (f : ℕ → ℝ≥0∞) :
    ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
      ((∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : ℝ≥0∞) / (n + 2 : ℕ)) * f (k + 1)) +
        (∑ k ∈ Finset.range (n + 1),
          (((n - k + 1 : ℕ) : ℝ≥0∞) / (n + 2 : ℕ)) * f k)) =
      ((n + 2 : ℕ) : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range (n + 2), f k := by
  have h1 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  calc
    _ = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹ *
        ((∑ k ∈ Finset.range (n + 1), ((k + 1 : ℕ) : ℝ≥0∞) * f (k + 1)) +
          (∑ k ∈ Finset.range (n + 1), ((n - k + 1 : ℕ) : ℝ≥0∞) * f k))) := by
      congr 1
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> simp only [div_eq_mul_inv] <;>
        ac_rfl
    _ = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * (((n + 2 : ℕ) : ℝ≥0∞)⁻¹ *
        (((n + 1 : ℕ) : ℝ≥0∞) * ∑ k ∈ Finset.range (n + 2), f k)) := by
      rw [incoming_size_weights]
    _ = _ := by
      have hc : ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((n + 1 : ℕ) : ℝ≥0∞) = 1 :=
        ENNReal.inv_mul_cancel h1 (ENNReal.natCast_ne_top _)
      calc _ = (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((n + 1 : ℕ) : ℝ≥0∞)) *
            (((n + 2 : ℕ) : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.range (n + 2), f k) := by ac_rfl
        _ = _ := by rw [hc, one_mul]

/-- One additional birth preserves uniform size and conditional independence. -/
theorem growthKernel_comp_mixtureLaw (n : ℕ) :
    growthKernel n ∘ₘ mixtureLaw n = mixtureLaw (n + 1) := by
  rw [mixtureLaw_eq_sum, Measure.comp_smul, comp_finset_sum, mixtureLaw_eq_sum]
  simp_rw [growthKernel_comp_componentLaw]
  ext E hE
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.add_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib]
  have hterms :
      (∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : ℝ≥0∞) / (k + (n - k) + 2 : ℕ)) *
            componentLaw (k + 1) (n - k) E) +
        (∑ k ∈ Finset.range (n + 1),
          (((n - k + 1 : ℕ) : ℝ≥0∞) / (k + (n - k) + 2 : ℕ)) *
            componentLaw k (n - k + 1) E) =
      (∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : ℝ≥0∞) / (n + 2 : ℕ)) *
            componentLaw (k + 1) (n + 1 - (k + 1)) E) +
        (∑ k ∈ Finset.range (n + 1),
          (((n - k + 1 : ℕ) : ℝ≥0∞) / (n + 2 : ℕ)) *
            componentLaw k (n + 1 - k) E) := by
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      have h1 : k + (n - k) + 2 = n + 2 := by omega
      have h2 : n - k = n + 1 - (k + 1) := by omega
      rw [h1, h2]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      have h1 : k + (n - k) + 2 = n + 2 := by omega
      have h3 : n - k + 1 = n + 1 - k := by omega
      rw [h1, h3]
  rw [hterms]
  simpa only [Nat.add_assoc] using
    incoming_size_probabilities n (fun k => componentLaw k (n + 1 - k) E)

end FreezingGrowth.RRTSplit
