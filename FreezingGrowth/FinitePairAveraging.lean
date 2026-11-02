module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Uniform deletion preserves the mean of a zero-diagonal statistic of two
distinct elements. Distinct elements may still have equal observed values. -/

@[expose] public section
namespace FreezingGrowth.FiniteAveraging

open scoped Classical

noncomputable def pairSum {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ) : ℝ :=
  ∑ u ∈ s, ∑ v ∈ s, g u v

noncomputable def distinctPairMean {ι : Type*} (s : Finset ι) (g : ι → ι → ℝ) : ℝ :=
  pairSum s g / ((s.card : ℝ) * ((s.card : ℝ) - 1))

theorem pairSum_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ι → ℝ)
    {w : ι} (hw : w ∈ s) (hg : g w w = 0) :
    pairSum (s.erase w) g = pairSum s g -
      (∑ v ∈ s, g w v) - (∑ u ∈ s, g u w) := by
  have he : pairSum (s.erase w) g =
      ∑ u ∈ s.erase w, ((∑ v ∈ s, g u v) - g u w) := by
    apply Finset.sum_congr rfl
    intro u _
    have hh := Finset.sum_erase_add s (fun v => g u v) hw
    linarith
  rw [he, Finset.sum_sub_distrib]
  have ho := Finset.sum_erase_add s (fun u => ∑ v ∈ s, g u v) hw
  have hc := Finset.sum_erase_add s (fun u => g u w) hw
  rw [hg, add_zero] at hc
  change _ = (∑ u ∈ s, ∑ v ∈ s, g u v) - _ - _
  linarith

theorem sum_pairSum_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ι → ℝ)
    (hg : ∀ w ∈ s, g w w = 0) :
    (∑ w ∈ s, pairSum (s.erase w) g) = ((s.card : ℝ) - 2) * pairSum s g := by
  have he (w : ι) (hw : w ∈ s) := pairSum_erase s g hw (hg w hw)
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hc : (∑ w ∈ s, ∑ u ∈ s, g u w) = pairSum s g := by
    rw [Finset.sum_comm]
    rfl
  rw [hc]
  change (s.card : ℝ) * pairSum s g - pairSum s g - pairSum s g = _
  ring

/-- The denominators count ordered distinct pairs before and after deletion. -/
theorem average_distinctPairMean_erase {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → ι → ℝ) (hs : 3 ≤ s.card) (hg : ∀ w ∈ s, g w w = 0) :
    (∑ w ∈ s, distinctPairMean (s.erase w) g) / s.card = distinctPairMean s g := by
  have hN : (s.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  have hN1 : (s.card : ℝ) - 1 ≠ 0 := by
    have hh : (3 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  have hN2 : (s.card : ℝ) - 2 ≠ 0 := by
    have hh : (3 : ℝ) ≤ s.card := by exact_mod_cast hs
    linarith
  have he (w : ι) (hw : w ∈ s) : distinctPairMean (s.erase w) g =
      pairSum (s.erase w) g / (((s.card : ℝ) - 1) * ((s.card : ℝ) - 2)) := by
    unfold distinctPairMean
    rw [Finset.card_erase_of_mem hw, Nat.cast_sub (by omega), Nat.cast_one]
    congr 1
    ring
  rw [Finset.sum_congr rfl he, ← Finset.sum_div, sum_pairSum_erase s g hg]
  unfold distinctPairMean
  field_simp

end FreezingGrowth.FiniteAveraging
