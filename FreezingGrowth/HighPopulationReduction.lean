module

public import FreezingGrowth.HeightMonotonicity
public import FreezingGrowth.FirstPeakDeletion
public import FreezingGrowth.MainStatements

/-!
# The corrected high-population reduction

Reaching r active vertices gives a comparison with a pure recursive-tree prefix
having r-1 attachments. This is the corrected index in main.tex 904–906.
The reduction below explicitly depends on the first-pair deletion theorem; it
is not an unconditional proof of that theorem or of Theorem 1.2.
-/

@[expose] public section

namespace FreezingGrowth.Word

theorem HeightLE.trans {xs ys zs : Word} (hxy : HeightLE xs ys) (hyz : HeightLE ys zs) :
    HeightLE xs zs := fun h => (hxy h).trans (hyz h)

/-- Every finite Boolean word either has no freeze or has a first freeze. -/
theorem initialRun_decomposition (xs : Word) :
    (∃ k, xs = List.replicate k true) ∨
      ∃ k tail, xs = List.replicate k true ++ [false] ++ tail := by
  induction xs with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b xs ih =>
    cases b
    · exact Or.inr ⟨0, xs, rfl⟩
    · rcases ih with ⟨k, rfl⟩ | ⟨k, tail, rfl⟩
      · exact Or.inl ⟨k + 1, by simp [List.replicate_succ]⟩
      · exact Or.inr ⟨k + 1, tail, by simp [List.replicate_succ]⟩

/-- A shorter pure-attachment prefix is below any extension of a longer one. -/
theorem heightLE_replicate_prefix {a b : ℕ} (hab : a ≤ b) (tail : Word) :
    HeightLE (List.replicate a true) (List.replicate b true ++ tail) := by
  have he : List.replicate b true =
      List.replicate a true ++ List.replicate (b - a) true := by
    rw [← List.replicate_add, Nat.add_sub_of_le hab]
  rw [he, List.append_assoc]
  exact heightLE_append _ _

/-- Before and at the first freezing step the population is at most k+1. -/
theorem first_peak_initial_population_le (k : ℕ) (tail : Word) (j : ℕ)
    (hj : j ≤ k + 1) :
    activeCount (toSigns (List.replicate k true ++ [false] ++ tail)) j ≤ (k : ℤ) + 1 := by
  by_cases hjk : j ≤ k
  · rw [List.append_assoc,
      activeCount_append_left _ _ (by simpa using hjk), activeCount_replicate_true hjk]
    exact_mod_cast Nat.add_le_add_right hjk 1
  · have he : j = k + 1 := by omega
    subst j
    rw [activeCount_append_left _ _ (by simp), first_peak_prefix_activeCount]
    omega

/-- Conditional high-profile reduction. The single comparison premise is
exactly the independently stated Theorem 1.3 target, and must be discharged
before counting this as a completed source result. -/
theorem high_population_domination_of_firstPairDeletion (hdelete : FirstPairDeletionClaim)
    (xs : Word) (ha : xs.admissible) {r : ℕ}
    (hhigh : ∃ j ≤ xs.length, (r : ℤ) ≤ activeCount xs.toSigns j) :
    HeightLE (List.replicate (r - 1) true) xs := by
  by_cases hrsmall : r ≤ 1
  · have hr : r - 1 = 0 := by omega
    simpa [hr] using heightLE_append [] xs
  have hr : 2 ≤ r := by omega
  suffices haux : ∀ N : ℕ, ∀ ws : Word, ws.length = N → ws.admissible →
      (∃ j ≤ ws.length, (r : ℤ) ≤ activeCount ws.toSigns j) →
      HeightLE (List.replicate (r - 1) true) ws by
    exact haux xs.length xs rfl ha hhigh
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ws hlen hw hh
    rcases initialRun_decomposition ws with ⟨k, rfl⟩ | ⟨k, tail, rfl⟩
    · obtain ⟨j, hj, hhigh⟩ := hh
      have hjk : j ≤ k := by simpa using hj
      rw [activeCount_replicate_true hjk] at hhigh
      have hk : r - 1 ≤ k := by omega
      simpa using heightLE_replicate_prefix hk []
    · obtain ⟨j, hj, hhigh⟩ := hh
      have hk : 1 ≤ k := by
        by_contra hk
        have hk0 : k = 0 := by omega
        subst k
        have hjlarge : 1 < j := by
          by_contra hjlarge
          have hb := first_peak_initial_population_le 0 tail j (by omega)
          omega
        have hp := hw 1 (by simpa using lt_of_lt_of_le hjlarge hj)
        norm_num [activeCount, toSigns] at hp
      by_cases hkr : r - 1 ≤ k
      · simpa only [List.append_assoc] using heightLE_replicate_prefix hkr ([false] ++ tail)
      · have hjlate : k + 1 ≤ j := by
          by_contra hjlate
          have hb := first_peak_initial_population_le k tail j (by omega)
          omega
        let d := j - (k + 1)
        have hjd : j = k + 1 + d := by dsimp [d]; omega
        have hcounts := first_peak_deletion_activeCount k hk tail d
        rw [← hjd] at hcounts
        have hshort : ∃ i ≤ (List.replicate (k - 1) true ++ tail).length,
            (r : ℤ) ≤ activeCount (toSigns (List.replicate (k - 1) true ++ tail)) i := by
          refine ⟨k - 1 + d, ?_, ?_⟩
          · simp only [List.length_append, List.length_replicate, List.length_singleton] at hj ⊢
            dsimp [d]
            omega
          · rw [← hcounts]
            exact hhigh
        have hlenlt : (List.replicate (k - 1) true ++ tail).length < N := by
          simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen ⊢
          omega
        have hdel := hdelete k hk tail hw
        exact (ih _ hlenlt _ rfl hdel.1 hshort).trans hdel.2

end FreezingGrowth.Word
