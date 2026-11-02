module

/- The reciprocal-parameter positivity proof is adapted from the local
   freezing1 companion project's ScheduleBernoulli.lean (Apache-2.0).
   See NOTICE for provenance. -/

public import FreezingGrowth.Path
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# The exact finite Bernoulli parameters in the manuscript

Every step before extinction receives the parameter reciprocal to its
post-step active population. Only attachment coordinates are summed in the
uniform-active-height representation. Freezing coordinates retain the
parameters stated in the paper rather than being replaced by zero parameters.
-/

@[expose] public section

namespace FreezingGrowth

/-- The source parameter `1 / S_(i+1)`, at every step in the finite horizon. -/
noncomputable def populationBernoulliParameter (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (i : Fin n) : unitInterval :=
  ⟨1 / (activeCount x (i.val + 1) : ℝ), by
    have hS : (1 : ℝ) ≤ (activeCount x (i.val + 1) : ℝ) := by
      have hs : (1 : ℤ) ≤ activeCount x (i.val + 1) := by
        have := h (i.val + 1) (by omega)
        omega
      exact_mod_cast hs
    exact ⟨by positivity, (div_le_one (lt_of_lt_of_le zero_lt_one hS)).mpr hS⟩⟩

@[simp] theorem populationBernoulliParameter_coe (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (i : Fin n) :
    (populationBernoulliParameter x n h i : ℝ) =
      1 / (activeCount x (i.val + 1) : ℝ) := rfl

/-- Attachment coordinates among the first `k` steps, inside a fixed horizon. -/
def attachmentIndices (x : SignSequence) (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k ∧ x (i.val + 1) = true)

@[simp] theorem attachmentIndices_zero (x : SignSequence) (n : ℕ) :
    attachmentIndices x n 0 = ∅ := by simp [attachmentIndices]

theorem attachmentIndices_horizon (x : SignSequence) (n : ℕ) :
    attachmentIndices x n n = Finset.univ.filter (fun i : Fin n => x (i.val + 1) = true) := by
  ext i
  simp [attachmentIndices]

theorem not_mem_attachmentIndices (x : SignSequence) {n k : ℕ} (hk : k < n) :
    (⟨k, hk⟩ : Fin n) ∉ attachmentIndices x n k := by simp [attachmentIndices]

theorem attachmentIndices_succ_attach (x : SignSequence) {n k : ℕ} (hk : k < n)
    (hx : x (k + 1) = true) :
    attachmentIndices x n (k + 1) = insert ⟨k, hk⟩ (attachmentIndices x n k) := by
  ext i
  simp only [attachmentIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  by_cases hi : i.val = k
  · simp [hi, hx]
  · have hlt : i.val < k + 1 ↔ i.val < k := by omega
    simp [hi, hlt]

theorem attachmentIndices_succ_freeze (x : SignSequence) (n k : ℕ)
    (hx : x (k + 1) = false) :
    attachmentIndices x n (k + 1) = attachmentIndices x n k := by
  ext i
  simp only [attachmentIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.val = k
  · simp [hi, hx]
  · have hlt : i.val < k + 1 ↔ i.val < k := by omega
    rw [hlt]

end FreezingGrowth
