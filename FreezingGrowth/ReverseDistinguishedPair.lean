module

public import FreezingGrowth.ReverseUniformRootPair
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Uniform pairs avoiding a distinguished component

Algorithm 3 delays an ordered pair precisely when both selected positions
avoid the distinguished singleton. The restriction identity below computes
the full subprobability law of that event, including its zero-probability
two-component boundary. Conditional uniformity is derived only when at least
three components are present. Independence from the shortened process's
history must still be proved by the joint construction.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

/-- Restricting an actual finite uniform measure leaves a cardinality factor
times the uniform measure on the retained points, including an empty filter. -/
theorem uniformOfFinset_restrict_eq_card_ratio {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α]
    (s : Finset α) (A : Set α) :
    (Measure.uniformOfFinset s).restrict A =
      (((s.filter (fun a => a ∈ A)).card : ℝ≥0∞) / (s.card : ℝ≥0∞)) •
        Measure.uniformOfFinset (s.filter (fun a => a ∈ A)) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.restrict_apply (measurableSet_singleton a), Measure.smul_apply, smul_eq_mul]
  by_cases ha : a ∈ s.filter (fun a => a ∈ A)
  · obtain ⟨has, haA⟩ := Finset.mem_filter.mp ha
    rw [Set.singleton_inter_of_mem haA,
      Measure.uniformOfFinset_apply_singleton_of_mem has,
      Measure.uniformOfFinset_apply_singleton_of_mem ha]
    have hne : ((s.filter (fun a => a ∈ A)).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩).ne'
    simpa only [one_div, mul_comm] using
      (ENNReal.div_mul_div_cancel (a := 1) (c := (s.card : ℝ≥0∞)) hne
        (ENNReal.natCast_ne_top _)).symm
  · rw [Measure.uniformOfFinset_apply_singleton_of_notMem ha, mul_zero]
    by_cases haA : a ∈ A
    · have has : a ∉ s := by intro hs; exact ha (Finset.mem_filter.mpr ⟨hs, haA⟩)
      rw [Set.singleton_inter_of_mem haA, Measure.uniformOfFinset_apply_singleton_of_notMem has]
    · rw [Set.singleton_inter_of_notMem haA, measure_empty]

section Distinguished

variable {V : Type*} [DecidableEq V]

/-- The fresh ordered pair does not use the distinguished component. -/
def avoidsDistinguished (d : V) : Set (V × V) := {p | p.1 ≠ d ∧ p.2 ≠ d}

theorem offDiag_filter_avoidsDistinguished (s : Finset V) (d : V) :
    s.offDiag.filter (fun p => p ∈ avoidsDistinguished d) = (s.erase d).offDiag := by
  ext p
  constructor
  · intro hp
    obtain ⟨hp, had⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpa, hpb, hne⟩ := Finset.mem_offDiag.mp hp
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_erase.mpr ⟨had.1, hpa⟩, Finset.mem_erase.mpr ⟨had.2, hpb⟩, hne⟩
  · intro hp
    obtain ⟨hpa, hpb, hne⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨had, hpa⟩ := Finset.mem_erase.mp hpa
    obtain ⟨hbd, hpb⟩ := Finset.mem_erase.mp hpb
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hpa, hpb, hne⟩, had, hbd⟩

/-- The cardinality ratio retains the two-component zero case exactly. -/
theorem offDiag_erase_card_ratio (s : Finset V) {d : V} (hd : d ∈ s)
    (hs : 2 ≤ s.card) :
    (((s.erase d).offDiag.card : ℝ≥0∞) / (s.offDiag.card : ℝ≥0∞)) =
      ((s.card - 2 : ℕ) : ℝ≥0∞) / (s.card : ℝ≥0∞) := by
  rw [card_offDiag_eq_mul_pred, card_offDiag_eq_mul_pred, Finset.card_erase_of_mem hd]
  have he : s.card - 1 - 1 = s.card - 2 := by omega
  rw [he, Nat.cast_mul, Nat.cast_mul, mul_comm (s.card : ℝ≥0∞)]
  exact ENNReal.mul_div_mul_left _ _ (by exact_mod_cast (show s.card - 1 ≠ 0 by omega))
    (ENNReal.natCast_ne_top _)

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The entire fresh-pair subprobability law on the avoidance event.
No independence or conditional-uniformity premise is used. -/
theorem uniformRootPair_restrict_avoidsDistinguished (s : Finset V) {d : V}
    (hd : d ∈ s) (hs : 2 ≤ s.card) :
    (uniformRootPair s).restrict (avoidsDistinguished d) =
      (((s.card - 2 : ℕ) : ℝ≥0∞) / (s.card : ℝ≥0∞)) • uniformRootPair (s.erase d) := by
  unfold uniformRootPair
  rw [uniformOfFinset_restrict_eq_card_ratio, offDiag_filter_avoidsDistinguished,
    offDiag_erase_card_ratio s hd hs]

omit [Countable V] in
/-- Exact chance of postponing the distinguished component's first use. -/
theorem uniformRootPair_avoid_probability (s : Finset V) {d : V}
    (hd : d ∈ s) (hs : 2 ≤ s.card) :
    (uniformRootPair s).real (avoidsDistinguished d) =
      ((s.card : ℝ) - 2) / (s.card : ℝ) := by
  change ((uniformRootPair s) (avoidsDistinguished d)).toReal = _
  rw [uniformRootPair, Measure.uniformOfFinset_apply,
    offDiag_filter_avoidsDistinguished, offDiag_erase_card_ratio s hd hs]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.cast_sub hs, Nat.cast_ofNat]

/-- With two components the next pair must use the distinguished singleton. -/
theorem uniformRootPair_restrict_avoids_eq_zero (s : Finset V) {d : V}
    (hd : d ∈ s) (hs : s.card = 2) :
    (uniformRootPair s).restrict (avoidsDistinguished d) = 0 := by
  rw [uniformRootPair_restrict_avoidsDistinguished s hd (by omega), hs]
  norm_num

/-- Whenever avoidance has positive probability, its normalized law is
uniform on the remaining ordered distinct pairs. -/
theorem uniformRootPair_conditional_avoid (s : Finset V) {d : V}
    (hd : d ∈ s) (hs : 3 ≤ s.card) :
    ((((s.card - 2 : ℕ) : ℝ≥0∞) / (s.card : ℝ≥0∞))⁻¹) •
      ((uniformRootPair s).restrict (avoidsDistinguished d)) =
        uniformRootPair (s.erase d) := by
  have hnum : ((s.card - 2 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : s.card - 2 ≠ 0)
  have hden : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  have hpos := ENNReal.div_pos hnum (ENNReal.natCast_ne_top s.card)
  have hfinite := ENNReal.div_ne_top (ENNReal.natCast_ne_top (s.card - 2)) hden
  rw [uniformRootPair_restrict_avoidsDistinguished s hd (by omega), smul_smul,
    ENNReal.inv_mul_cancel hpos.ne' hfinite, one_smul]

end Distinguished
end FreezingGrowth
