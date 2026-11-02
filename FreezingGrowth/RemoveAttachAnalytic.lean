module

public import FreezingGrowth.RemoveAttachMixture
public import FreezingGrowth.MainStatements

/-!
# Proposition 1.1(iii), without a finite numerical witness

Sublinear mean growth supplies arbitrarily late small increments. The actual
seeded-growth identities then give strict expected-height reversal. This does
not assert reversal at every sufficiently large index.
-/

@[expose] public section
namespace FreezingGrowth

private theorem admissible_append_attachments (xs : Word) (hx : xs.admissible)
    (hp : 0 < activeCount xs.toSigns xs.length) (n : ℕ) :
    Word.admissible (xs ++ List.replicate n true) := by
  intro j hj
  by_cases hpre : j < xs.length
  · rw [Word.activeCount_append_left xs _ hpre.le]
    exact hx j hpre
  · have hjn : j - xs.length ≤ n := by
      simp only [List.length_append, List.length_replicate] at hj
      omega
    rw [show j = xs.length + (j - xs.length) by omega,
      Word.activeCount_append_add, Word.activeCount_replicate_true hjn]
    omega

theorem removalLong_admissible (n : ℕ) : (removalLong n).admissible := by
  apply admissible_append_attachments
  · intro j hj
    have hj' : j < 3 := by simpa using hj
    interval_cases j <;> norm_num [activeCount, Word.toSigns, Finset.sum_range_succ]
  · norm_num [activeCount, Word.toSigns, Finset.sum_range_succ]

theorem removalShort_admissible (n : ℕ) : (removalShort n).admissible := by
  apply admissible_append_attachments
  · intro j hj
    have hj' : j < 2 := by simpa using hj
    interval_cases j <;> norm_num [activeCount, Word.toSigns, Finset.sum_range_succ]
  · norm_num [activeCount, Word.toSigns, Finset.sum_range_succ]

theorem removal_reversal_arbitrarily_late (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
      (removalLong n).expectedHeight < (removalShort n).expectedHeight := by
  obtain ⟨n, hn, hδ⟩ := RRT.meanHeight_exists_small_increment
    (ε := 1 / 24) (by norm_num) (max N 2)
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hf : (6 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast (show 6 ≤ (n + 1).factorial from by
      simpa only [show Nat.factorial 3 = 6 by decide +kernel] using
        Nat.factorial_le (show 3 ≤ n + 1 by omega))
  have hc : (1 : ℝ) / (6 * ((n + 1).factorial : ℝ)) ≤ 1 / 36 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hcomp := removal_expectedHeight_comparison (show 1 ≤ n by omega)
  exact ⟨n, hnN, hn2, by linarith⟩

theorem removeAttachClaim : RemoveAttachClaim := by
  obtain ⟨n, _, _, hn⟩ := removal_reversal_arbitrarily_late 0
  exact ⟨n, removalLong_admissible n, removalShort_admissible n, hn⟩

end FreezingGrowth
