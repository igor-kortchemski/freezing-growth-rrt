module

public import FreezingGrowth.ReverseHeightPermutation
public import FreezingGrowth.ReverseDistinguishedPair

/-!
# First-step recursion and avoiding the added singleton

These identities connect the complete coalescence law to one actual uniform
graft and identify the entire avoidance submeasure when a zero-height
component is prepended. The empty avoidance boundary remains explicit.
-/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

open MeasureTheory
open scoped Classical ENNReal

theorem graftLaw_ae_length (xs : List ℕ) (hx : 2 ≤ xs.length) :
    ∀ᵐ ys ∂graftLaw xs, ys.length = xs.length - 1 := by
  rw [graftLaw, ite_eq_left hx]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
  filter_upwards [uniformRootPair_ae_offDiag (Finset.range xs.length)] with p hp
  exact graft_length xs p.1 p.2 (Finset.mem_range.mp (Finset.mem_offDiag.mp hp).2.1)

@[simp] theorem finishLaw_nil : finishLaw [] = Measure.dirac 0 := by
  simp [finishLaw, finishAfter]

@[simp] theorem finishLaw_singleton (a : ℕ) : finishLaw [a] = Measure.dirac a := by
  simp [finishLaw, finishAfter]

/-- Complete coalescence obeys its genuine one-step Markov recursion. The
fuel after that step is justified by the kernel's component-count support. -/
theorem finishLaw_step (xs : List ℕ) (hx : 2 ≤ xs.length) :
    finishLaw xs = (graftLaw xs).bind finishLaw := by
  rw [finishLaw, show xs.length - 1 = (xs.length - 2) + 1 by omega, finishAfter]
  apply Measure.bind_congr_right
  filter_upwards [graftLaw_ae_length xs hx] with ys hy
  change finishAfter (xs.length - 2) ys = finishAfter (ys.length - 1) ys
  rw [hy, Nat.sub_sub]

theorem finishLaw_tail_step (xs : List ℕ) (hx : 2 ≤ xs.length) (h : ℕ) :
    finishLaw xs {z | h ≤ z} =
      ∫⁻ p, finishLaw (graft xs p.1 p.2) {z | h ≤ z}
        ∂uniformRootPair (Finset.range xs.length) := by
  rw [finishLaw_step xs hx, graftLaw, ite_eq_left hx,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable,
    lintegral_map measurable_from_top (measurable_of_countable _)]

/-- Shift ordinary positions past the newly prepended distinguished entry. -/
def successorPair (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 1, p.2 + 1)

theorem successorPair_injective : Function.Injective successorPair := by
  intro p q h
  apply Prod.ext
  · have := congrArg Prod.fst h
    simp only [successorPair] at this
    omega
  · have := congrArg Prod.snd h
    simp only [successorPair] at this
    omega

theorem successorPair_image (r : ℕ) :
    ((Finset.range r).offDiag.image successorPair) =
      ((Finset.range (r + 1)).erase 0).offDiag := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hq
    simp only [Finset.mem_range] at ha hb
    apply Finset.mem_offDiag.mpr
    refine ⟨Finset.mem_erase.mpr ⟨by simp [successorPair], ?_⟩,
      Finset.mem_erase.mpr ⟨by simp [successorPair], ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr (by simp only [successorPair]; omega)
    · exact Finset.mem_range.mpr (by simp only [successorPair]; omega)
    · simp only [successorPair]
      omega
  · intro hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨ha0, ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨hb0, hb⟩ := Finset.mem_erase.mp hb
    simp only [Finset.mem_range] at ha hb
    refine Finset.mem_image.mpr ⟨(p.1 - 1, p.2 - 1),
      Finset.mem_offDiag.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega), by omega⟩, ?_⟩
    apply Prod.ext <;> simp only [successorPair] <;> omega

theorem map_uniformRootPair_successor (r : ℕ) :
    (uniformRootPair (Finset.range r)).map successorPair =
      uniformRootPair ((Finset.range (r + 1)).erase 0) := by
  unfold uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
    successorPair_injective.injOn, successorPair_image]

/-- Avoidance is an exact scaled copy of the shorter list's uniform pair
law. For `r = 1` its coefficient and its entire submeasure are zero. -/
theorem uniformRootPair_restrict_avoid_zero (r : ℕ) (hr : 1 ≤ r) :
    (uniformRootPair (Finset.range (r + 1))).restrict (avoidsDistinguished 0) =
      (((r - 1 : ℕ) : ℝ≥0∞) / ((r + 1 : ℕ) : ℝ≥0∞)) •
        (uniformRootPair (Finset.range r)).map successorPair := by
  rw [uniformRootPair_restrict_avoidsDistinguished _ (by simp)
    (by simpa using (show 2 ≤ r + 1 by omega)), ← map_uniformRootPair_successor]
  simp only [Finset.card_range]
  rw [show r + 1 - 2 = r - 1 by omega]

/-- The coefficient is also the actual mass of avoidance, including the
zero mass when the shorter list has just one component. -/
theorem uniformRootPair_avoid_zero_mass (r : ℕ) (hr : 1 ≤ r) :
    uniformRootPair (Finset.range (r + 1)) (avoidsDistinguished 0) =
      (((r - 1 : ℕ) : ℝ≥0∞) / ((r + 1 : ℕ) : ℝ≥0∞)) := by
  rw [uniformRootPair, Measure.uniformOfFinset_apply,
    offDiag_filter_avoidsDistinguished,
    offDiag_erase_card_ratio _ (by simp)
      (by simpa using (show 2 ≤ r + 1 by omega))]
  simp only [Finset.card_range]
  rw [show r + 1 - 2 = r - 1 by omega]

end FreezingGrowth.ReverseHeightList
