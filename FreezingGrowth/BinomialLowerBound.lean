module

public import FreezingGrowth.BinomialSum
public import FreezingGrowth.ActiveHeightOrder

/-!
# The low-population binomial stochastic lower bound

This proves the distributional comparison at main.tex 920–923 for the actual
maximum-height law. Terminal extinction is handled by the proved surviving
prefix, preserving both the attachment count and the maximum-height law.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem attachmentIndices_card (x : SignSequence) (n k : ℕ) (hk : k ≤ n) :
    (attachmentIndices x n k).card = plusCount x k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have ih := ih (by omega)
    cases hx : x (k + 1)
    · rw [attachmentIndices_succ_freeze x n k hx, plusCount_succ, hx]
      simpa using ih
    · rw [attachmentIndices_succ_attach x hkn hx, Finset.card_insert_of_notMem
        (not_mem_attachmentIndices x hkn), plusCount_succ, hx]
      simpa using ih

theorem attachment_filter_card (x : SignSequence) (n : ℕ) :
    (Finset.univ.filter fun i : Fin n => x (i.val + 1) = true).card = plusCount x n := by
  rw [← attachmentIndices_horizon]
  exact attachmentIndices_card x n n le_rfl

namespace Word

/-- Any common Bernoulli parameter below all post-attachment reciprocals gives
an actual binomial stochastic lower bound with exactly `xs.attachments` trials. -/
theorem binomial_real_tail_le (xs : Word) (ha : xs.admissible) (p : unitInterval)
    (hp : ∀ i < xs.length, xs.toSigns (i + 1) = true →
      (p : ℝ) ≤ 1 / (activeCount xs.toSigns (i + 1) : ℝ)) (h : ℕ) :
    (binomial xs.attachments p).real {k | h ≤ k} ≤ xs.heightLaw.real {k | h ≤ k} := by
  obtain ⟨k, hkle, hk, hcount, hlaw⟩ := exists_surviving_prefix xs ha
  have hb := Forward.bernoulliPartialSumLaw_real_tail_le_heightLaw xs.toSigns k hk
    (fun _ => p) (fun i hi => hp i.val (by omega) hi) h
  rw [bernoulliPartialSumLaw_const_eq_binomial, attachment_filter_card, hcount, hlaw] at hb
  exact hb

/-- The source value `1/r` as a valid Bernoulli parameter for every `r ≥ 1`. -/
noncomputable def reciprocalParameter (r : ℝ) (hr : 1 ≤ r) : unitInterval :=
  ⟨1 / r, by
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    exact ⟨(one_div_pos.mpr hr0).le, (div_le_one hr0).mpr hr⟩⟩

/-- D2: a cap on each post-attachment active population gives the manuscript's
`Bin(n,1/r)` lower bound. Extinction at the final step is included. -/
theorem binomial_tail_lower_bound (xs : Word) (ha : xs.admissible)
    (r : ℝ) (hr : 1 ≤ r)
    (hcap : ∀ i < xs.length, xs.toSigns (i + 1) = true →
      (activeCount xs.toSigns (i + 1) : ℝ) ≤ r) (h : ℕ) :
    (binomial xs.attachments (reciprocalParameter r hr)).real {k | h ≤ k} ≤
      xs.heightLaw.real {k | h ≤ k} := by
  apply binomial_real_tail_le xs ha
  intro i hi hx
  have hs : 0 < activeCount xs.toSigns (i + 1) := by
    rw [activeCount_succ, hx]
    have := ha i hi
    simp only [↓reduceIte]
    omega
  have hsR : (0 : ℝ) < activeCount xs.toSigns (i + 1) := by exact_mod_cast hs
  exact one_div_le_one_div_of_le hsR (hcap i hi hx)

end Word
end FreezingGrowth
