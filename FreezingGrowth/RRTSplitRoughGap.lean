module

public import FreezingGrowth.RRTRoughAbsoluteDeviation
public import FreezingGrowth.RRTSplitIntegrals
import Mathlib.Analysis.Complex.Exponential

/-!
# A coarse mean imbalance of the actual first-edge component heights

The component law retains its uniform size mixture and its exchangeability.
The resulting logarithmic-logarithmic estimate is an auxiliary bound, not the
sharper bounded-imbalance statement quoted in the source.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory
open scoped Classical ENNReal

theorem heightPairLaw_eq_sum (n : ℕ) :
    heightPairLaw n = ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ •
      ∑ k ∈ Finset.range (n + 1),
        (Forward.heightLaw RRT.allAttach k).prod
          (Forward.heightLaw RRT.allAttach (n - k)) := by
  rw [heightPairLaw, pairLaw_eq_sum,
    Measure.map_smul _ measurable_heightPair.aemeasurable,
    Measure.map_finset_sum measurable_heightPair.aemeasurable]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (Measure.map_prod_map (Forward.treeLaw RRT.allAttach k)
    (Forward.treeLaw RRT.allAttach (n - k)) measurable_from_top measurable_from_top).symm

theorem integral_heightPairLaw_fst (n : ℕ) (f : ℕ → ℝ) :
    (∫ p : ℕ × ℕ, f p.1 ∂heightPairLaw n) =
      ((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1),
        ∫ h : ℕ, f h ∂Forward.heightLaw RRT.allAttach k := by
  rw [heightPairLaw_eq_sum, integral_smul_measure,
    integral_finsetSum_measure (fun k _ =>
      (Forward.heightLaw_integrable RRT.allAttach k f).comp_fst
        (Forward.heightLaw RRT.allAttach (n - k)))]
  simp only [ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one,
    smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← integral_map (f := f) measurable_fst.aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  simp

theorem integral_heightPairLaw_snd (n : ℕ) (f : ℕ → ℝ) :
    (∫ p : ℕ × ℕ, f p.2 ∂heightPairLaw n) =
      ∫ p : ℕ × ℕ, f p.1 ∂heightPairLaw n := by
  have h := integral_map (μ := heightPairLaw n) (f := fun p : ℕ × ℕ => f p.1)
    measurable_swap.aemeasurable (measurable_of_countable _).aestronglyMeasurable
  rw [heightPairLaw_swap] at h
  exact h.symm

theorem sum_log_succ_eq_log_factorial (N : ℕ) :
    (∑ k ∈ Finset.range N, Real.log ((k : ℝ) + 1)) =
      Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Averaging the loss from the largest first-order center costs at most one
before multiplying by `e`. -/
theorem sum_log_defect_le (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (Real.log ((n : ℝ) + 1) - Real.log ((k : ℝ) + 1))) ≤ (n : ℝ) + 1 := by
  let N := n + 1
  have hN : (0 : ℝ) < (N : ℝ) := by dsimp [N]; positivity
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by positivity
  have he := Real.pow_div_factorial_le_exp (x := (N : ℝ)) hN.le N
  have hp : (N : ℝ) ^ N ≤ Real.exp (N : ℝ) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp he
  have hlog := Real.log_le_log (pow_pos hN N) hp
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at hlog
  rw [Finset.sum_sub_distrib, sum_log_succ_eq_log_factorial]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  dsimp [N] at hlog
  push_cast at hlog
  linarith

theorem loglog_mono {k n : ℕ} (hkn : k ≤ n) :
    Real.log (1 + Real.log ((k : ℝ) + 1)) ≤
      Real.log (1 + Real.log ((n : ℝ) + 1)) := by
  have hk : 0 ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  apply Real.log_le_log (by linarith)
  have h := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) + 1)
    (show (k : ℝ) + 1 ≤ (n : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hkn 1)
  linarith

theorem integral_abs_sub_larger_center_le {k n : ℕ} (hkn : k ≤ n) :
    (∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|
      ∂Forward.heightLaw RRT.allAttach k) ≤
        RRT.roughAbsoluteDeviation k + Real.exp 1 *
          (Real.log ((n : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by
  let b := Real.exp 1 * Real.log ((k : ℝ) + 1)
  let c := Real.exp 1 * Real.log ((n : ℝ) + 1)
  have hbc : b ≤ c := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hkn 1)
  have hp (h : ℕ) : |(h : ℝ) - c| ≤ |(h : ℝ) - b| + (c - b) := by
    have hu := le_abs_self ((h : ℝ) - b)
    have hl := neg_le_abs ((h : ℝ) - b)
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ ∫ h : ℕ, (|(h : ℝ) - b| + (c - b)) ∂Forward.heightLaw RRT.allAttach k :=
      integral_mono (Forward.heightLaw_integrable RRT.allAttach k _)
        ((RRT.roughAbsoluteDeviation_integrable k).add (integrable_const _)) hp
    _ = RRT.roughAbsoluteDeviation k + (c - b) := by
      rw [integral_add (RRT.roughAbsoluteDeviation_integrable k) (integrable_const _),
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      rfl
    _ = _ := by dsimp [b, c]; ring

noncomputable def roughHeightGap (n : ℕ) : ℝ :=
  ∫ p : ℕ × ℕ, |(p.1 : ℝ) - (p.2 : ℝ)| ∂heightPairLaw n

theorem roughHeightGap_le_twice_centered (n : ℕ) (b : ℝ) :
    roughHeightGap n ≤ 2 * ∫ p : ℕ × ℕ, |(p.1 : ℝ) - b| ∂heightPairLaw n := by
  have hp (p : ℕ × ℕ) : |(p.1 : ℝ) - (p.2 : ℝ)| ≤
      |(p.1 : ℝ) - b| + |(p.2 : ℝ) - b| := by
    have h1 := le_abs_self ((p.1 : ℝ) - b)
    have h2 := neg_le_abs ((p.1 : ℝ) - b)
    have h3 := le_abs_self ((p.2 : ℝ) - b)
    have h4 := neg_le_abs ((p.2 : ℝ) - b)
    apply abs_le.mpr
    constructor <;> linarith
  calc
    roughHeightGap n ≤ ∫ p : ℕ × ℕ, (|(p.1 : ℝ) - b| + |(p.2 : ℝ) - b|)
        ∂heightPairLaw n :=
      integral_mono (heightPairLaw_integrable n _) (heightPairLaw_integrable n _) hp
    _ = 2 * ∫ p : ℕ × ℕ, |(p.1 : ℝ) - b| ∂heightPairLaw n := by
      rw [integral_add (heightPairLaw_integrable n _) (heightPairLaw_integrable n _),
        integral_heightPairLaw_snd n (fun h => |(h : ℝ) - b|)]
      ring

/-- Uniform coarse imbalance of the unshifted two component heights. -/
theorem uniformRoughHeightGap :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, roughHeightGap n ≤
      C + 4 * Real.log (1 + Real.log ((n : ℝ) + 1)) := by
  obtain ⟨C, hC, hrough⟩ := RRT.uniformRoughAbsoluteDeviation
  refine ⟨2 * C + 2 * Real.exp 1, by positivity, fun n => ?_⟩
  let L := Real.log (1 + Real.log ((n : ℝ) + 1))
  let B := C + 2 * L
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (∫ h : ℕ, |(h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|
        ∂Forward.heightLaw RRT.allAttach k) ≤
          B + Real.exp 1 * (Real.log ((n : ℝ) + 1) - Real.log ((k : ℝ) + 1)) := by
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    apply (integral_abs_sub_larger_center_le hkn).trans
    apply add_le_add _ (le_refl _)
    exact (hrough k).trans (by have := loglog_mono hkn; dsimp [B, L]; linarith)
  have hmean : (∫ p : ℕ × ℕ, |(p.1 : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|
      ∂heightPairLaw n) ≤ B + Real.exp 1 := by
    rw [integral_heightPairLaw_fst n
      (fun h : ℕ => |(h : ℝ) - Real.exp 1 * Real.log ((n : ℝ) + 1)|)]
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (inv_nonneg.mpr hN.le)).trans
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    calc
      ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * B + Real.exp 1 *
          ∑ k ∈ Finset.range (n + 1),
            (Real.log ((n : ℝ) + 1) - Real.log ((k : ℝ) + 1))) ≤
        ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * B + Real.exp 1 * ((n : ℝ) + 1)) := by
          gcongr
          exact sum_log_defect_le n
      _ = B + Real.exp 1 := by field_simp
  have hg := roughHeightGap_le_twice_centered n (Real.exp 1 * Real.log ((n : ℝ) + 1))
  dsimp [B, L] at hmean
  linarith

end FreezingGrowth.RRTSplit
