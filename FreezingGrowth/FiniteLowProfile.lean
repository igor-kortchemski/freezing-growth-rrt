module

public import FreezingGrowth.FiniteLaw
public import FreezingGrowth.LowProfile

/-!
# Endpoint-complete finite low-population estimates

These finite estimates supply the expectation and lower-tail input to the
low-values argument of Theorem 1.2. They apply to every admissible finite word,
including words whose last operation freezes the final active vertex.

The proof uses the forward active-height mean and MGF estimates. It does not
assert the separate independent-Bernoulli representation or binomial stochastic
domination stated in the manuscript, nor the theorem's asymptotic conclusion.
-/

@[expose] public section

namespace FreezingGrowth.Word

open MeasureTheory

/-- Every real function of finite-word height is integrable. -/
theorem heightLaw_integrable (xs : Word) (f : ℕ → ℝ) : Integrable f xs.heightLaw :=
  Forward.heightLaw_integrable xs.toSigns xs.length f

/-- Either use the whole word or remove its terminal extinction step.
The representative has a nonempty active population, the same number of
attachments, and the same distribution of the maximum tree height. -/
theorem exists_surviving_prefix (xs : Word) (ha : xs.admissible) :
    ∃ k ≤ xs.length, PositiveThrough xs.toSigns k ∧
      plusCount xs.toSigns k = xs.attachments ∧
      Forward.heightLaw xs.toSigns k = xs.heightLaw := by
  by_cases hz : activeCount xs.toSigns xs.length = 0
  · obtain ⟨hlen, hfreeze, _, _⟩ := terminal_zero_last_freeze ha hz
    have hsucc : xs.length - 1 + 1 = xs.length := by omega
    refine ⟨xs.length - 1, Nat.sub_le _ _, ?_, ?_, ?_⟩
    · intro j hj
      exact ha j (by omega)
    · have hstep := plusCount_succ xs.toSigns (xs.length - 1)
      rw [hsucc, hfreeze] at hstep
      simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, attachments] using hstep.symm
    · have hh := heightLaw_take_pred_of_terminal_zero ha hz
      rw [heightLaw_take xs (Nat.sub_le _ _)] at hh
      exact hh
  · have hpos : 0 < activeCount xs.toSigns xs.length := by
      have hnonneg := terminal_activeCount_nonneg ha
      omega
    refine ⟨xs.length, le_rfl, ?_, rfl, rfl⟩
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | rfl
    · exact ha j hlt
    · exact hpos

/-- A cap on each post-attachment active population gives a lower bound for
expected height, even when the finite word ends at extinction. -/
theorem profile_expected_lower_bound (xs : Word) (ha : xs.admissible)
    {r : ℝ} (hr : 0 < r)
    (hcap : ∀ i < xs.length, xs.toSigns (i + 1) = true →
      (activeCount xs.toSigns (i + 1) : ℝ) ≤ r) :
    (xs.attachments : ℝ) / r ≤ xs.expectedHeight := by
  obtain ⟨k, hkle, hpos, hcount, hlaw⟩ := exists_surviving_prefix xs ha
  have hτ : (k : ℕ∞) < extinctionTime xs.toSigns :=
    (lt_extinctionTime_iff xs.toSigns k).mpr hpos
  have hcapk : ∀ i < k, xs.toSigns (i + 1) = true →
      (activeCount xs.toSigns (i + 1) : ℝ) ≤ r :=
    fun i hi hx => hcap i (hi.trans_le hkle) hx
  calc
    (xs.attachments : ℝ) / r = (plusCount xs.toSigns k : ℝ) / r := by rw [hcount]
    _ ≤ ∫ s, (Forward.treeHeight s : ℝ) ∂Forward.treeLaw xs.toSigns k :=
      Forward.profile_expected_lower_bound xs.toSigns k hτ hr hcapk
    _ = ∫ h : ℕ, (h : ℝ) ∂Forward.heightLaw xs.toSigns k :=
      (Forward.heightLaw_integral xs.toSigns k (fun h : ℕ => (h : ℝ))).symm
    _ = xs.expectedHeight := by rw [hlaw]; rfl

/-- Finite low-population Bennett bound centered at the number of attachments
divided by the population cap. Terminal extinction is included. -/
theorem profile_height_lower_tail (xs : Word) (ha : xs.admissible)
    (hattach : 0 < xs.attachments) {r : ℝ} (hr : 0 < r)
    (hcap : ∀ i < xs.length, xs.toSigns (i + 1) = true →
      (activeCount xs.toSigns (i + 1) : ℝ) ≤ r)
    {t : ℝ} (ht : 0 < t) :
    xs.heightLaw.real {h : ℕ | (h : ℝ) < (xs.attachments : ℝ) / r - t} ≤
      Real.exp (-((xs.attachments : ℝ) / r) *
        bennettRate (t / ((xs.attachments : ℝ) / r))) := by
  obtain ⟨k, hkle, hpos, hcount, hlaw⟩ := exists_surviving_prefix xs ha
  have hk : 1 ≤ k := by
    have hle := plusCount_le xs.toSigns k
    rw [hcount] at hle
    omega
  have hτ : (k : ℕ∞) < extinctionTime xs.toSigns :=
    (lt_extinctionTime_iff xs.toSigns k).mpr hpos
  have hcapk : ∀ i < k, xs.toSigns (i + 1) = true →
      (activeCount xs.toSigns (i + 1) : ℝ) ≤ r :=
    fun i hi hx => hcap i (hi.trans_le hkle) hx
  have hb := Forward.profile_height_lower_tail xs.toSigns k hk hτ hr hcapk ht
  rw [← hlaw, Forward.heightLaw,
    map_measureReal_apply measurable_from_top ((Set.to_countable _).measurableSet)]
  change (Forward.treeLaw xs.toSigns k).real
    {s | (Forward.treeHeight s : ℝ) < (xs.attachments : ℝ) / r - t} ≤ _
  simpa only [hcount] using hb

end FreezingGrowth.Word
