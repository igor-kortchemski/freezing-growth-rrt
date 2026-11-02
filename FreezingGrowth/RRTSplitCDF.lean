module

public import FreezingGrowth.RRTSplitIntegrals

/-! Exact first-edge CDF recurrences for the actual RRT laws. -/

@[expose] public section
namespace FreezingGrowth.RRTSplit

open MeasureTheory
open scoped Classical ENNReal

/-- Projection to arbitrary height events preserves the child edge offset. -/
theorem heightLaw_event_split (n : ℕ) (E : Set ℕ) :
    (Forward.heightLaw RRT.allAttach (n + 1)).real E =
      (heightPairLaw n).real {p | max p.1 (p.2 + 1) ∈ E} := by
  rw [Forward.heightLaw, heightPairLaw_eq_map,
    map_measureReal_apply measurable_from_top E.to_countable.measurableSet,
    map_measureReal_apply measurable_from_top (Set.to_countable _).measurableSet]
  apply measureReal_congr
  filter_upwards [treeLaw_height_split n] with s hs
  exact congrArg (fun h => h ∈ E) hs

/-- Given the split size, both component laws are the genuine RRT laws. -/
theorem heightPairLaw_rectangle (n : ℕ) (A B : Set ℕ) :
    heightPairLaw n (A ×ˢ B) = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ k ∈ Finset.range (n + 1),
        Forward.heightLaw RRT.allAttach k A *
          Forward.heightLaw RRT.allAttach (n - k) B := by
  rw [heightPairLaw, Measure.map_apply measurable_heightPair (by measurability),
    pairLaw_eq_sum, Measure.smul_apply, smul_eq_mul,
    Measure.finsetSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have he : (fun p : Forward.State × Forward.State =>
      (Forward.treeHeight p.1, Forward.treeHeight p.2)) ⁻¹' (A ×ˢ B) =
      (Forward.treeHeight ⁻¹' A) ×ˢ (Forward.treeHeight ⁻¹' B) := rfl
  rw [he, Measure.prod_prod, Forward.heightLaw, Forward.heightLaw,
    Measure.map_apply measurable_from_top A.to_countable.measurableSet,
    Measure.map_apply measurable_from_top B.to_countable.measurableSet]

theorem heightPairLaw_real_rectangle (n : ℕ) (A B : Set ℕ) :
    (heightPairLaw n).real (A ×ˢ B) = (1 / ((n : ℝ) + 1)) *
      ∑ k ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach k).real A *
          (Forward.heightLaw RRT.allAttach (n - k)).real B := by
  unfold Measure.real
  rw [heightPairLaw_rectangle, ENNReal.toReal_mul, ENNReal.toReal_sum]
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    simp only [Nat.cast_add, Nat.cast_one, one_div, ENNReal.toReal_mul]
  · intro k hk
    finiteness

/-- Strict real thresholds, in the form used by the lower-tail amplifier. -/
theorem heightLaw_real_lt_succ (n : ℕ) (t : ℝ) :
    (Forward.heightLaw RRT.allAttach (n + 1)).real {h | (h : ℝ) < t} =
      (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach k).real {h | (h : ℝ) < t} *
          (Forward.heightLaw RRT.allAttach (n - k)).real {h | (h : ℝ) < t - 1} := by
  rw [heightLaw_event_split]
  simp only [Set.mem_ofPred_eq]
  have he : {p : ℕ × ℕ | ((max p.1 (p.2 + 1) : ℕ) : ℝ) < t} =
      {h : ℕ | (h : ℝ) < t} ×ˢ {h : ℕ | (h : ℝ) < t - 1} := by
    ext p
    simp only [Nat.cast_max, Nat.cast_add, Nat.cast_one, max_lt_iff,
      Set.mem_ofPred_eq, Set.mem_prod]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he, heightPairLaw_real_rectangle]

/-- Non-strict real thresholds, without rounding or positivity assumptions. -/
theorem heightLaw_real_le_succ (n : ℕ) (t : ℝ) :
    (Forward.heightLaw RRT.allAttach (n + 1)).real {h | (h : ℝ) ≤ t} =
      (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach k).real {h | (h : ℝ) ≤ t} *
          (Forward.heightLaw RRT.allAttach (n - k)).real {h | (h : ℝ) ≤ t - 1} := by
  rw [heightLaw_event_split]
  simp only [Set.mem_ofPred_eq]
  have he : {p : ℕ × ℕ | ((max p.1 (p.2 + 1) : ℕ) : ℝ) ≤ t} =
      {h : ℕ | (h : ℝ) ≤ t} ×ˢ {h : ℕ | (h : ℝ) ≤ t - 1} := by
    ext p
    simp only [Nat.cast_max, Nat.cast_add, Nat.cast_one, max_le_iff,
      Set.mem_ofPred_eq, Set.mem_prod]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he, heightPairLaw_real_rectangle]

/-- Natural CDF recurrence; the total tree has `n+1` edges. -/
theorem heightLaw_cdf_succ (n h : ℕ) :
    (Forward.heightLaw RRT.allAttach (n + 1)).real {a | a ≤ h + 1} =
      (1 / ((n : ℝ) + 1)) * ∑ k ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach k).real {a | a ≤ h + 1} *
          (Forward.heightLaw RRT.allAttach (n - k)).real {a | a ≤ h} := by
  rw [heightLaw_event_split]
  simp only [Set.mem_ofPred_eq]
  have he : {p : ℕ × ℕ | max p.1 (p.2 + 1) ≤ h + 1} =
      {a : ℕ | a ≤ h + 1} ×ˢ {a : ℕ | a ≤ h} := by
    ext p
    simp
  rw [he, heightPairLaw_real_rectangle]

/-- Boundary values needed by the generating-function argument. -/
@[simp] theorem heightLaw_cdf_initial (h : ℕ) :
    (Forward.heightLaw RRT.allAttach 0).real {a | a ≤ h} = 1 := by
  simp [Forward.heightLaw, Forward.treeLaw, Measure.map_dirac' measurable_from_top,
    Forward.treeHeight_initial]

@[simp] theorem heightLaw_cdf_zero (n : ℕ) :
    (Forward.heightLaw RRT.allAttach (n + 1)).real {a | a ≤ 0} = 0 := by
  rw [heightLaw_event_split]
  have he : {p : ℕ × ℕ | max p.1 (p.2 + 1) ∈ {a | a ≤ 0}} = ∅ := by
    ext p
    simp
  rw [he, measureReal_empty]

end FreezingGrowth.RRTSplit
