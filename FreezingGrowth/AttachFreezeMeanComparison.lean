module

public import FreezingGrowth.AttachFreezeWordExpectation

/-! A bounded local comparison reduces attachment-then-freezing to the
freezing-then-attachment comparison. Every mean uses the actual seeded growth
law, and every maximum includes the new child even when that child is frozen. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory

noncomputable def freezeAttachMean (a b M n : ℕ) : ℝ :=
  (meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
    meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n) / 2

noncomputable def attachFreezeMean (a b M n : ℕ) : ℝ :=
  (meanGrowth ⟨{a, b}, max M (a + 1)⟩ n +
    meanGrowth ⟨{a + 1, b}, max M (a + 1)⟩ n +
    meanGrowth ⟨{a, a + 1}, max M (a + 1)⟩ n +
    meanGrowth ⟨{a, b}, max M (b + 1)⟩ n +
    meanGrowth ⟨{b, b + 1}, max M (b + 1)⟩ n +
    meanGrowth ⟨{a, b + 1}, max M (b + 1)⟩ n) / 6

/-- Increasing each seed and the retained maximum by at most one increases
the eventual maximum by at most one, using the same actual split growth law. -/
theorem meanGrowth_pair_le_add_one (a b M a' b' M' n : ℕ)
    (hab : max a b ≤ M) (hab' : max a' b' ≤ M')
    (ha : a' ≤ a + 1) (hb : b' ≤ b + 1) (hM : M' ≤ M + 1) :
    meanGrowth ⟨{a', b'}, M'⟩ n ≤ meanGrowth ⟨{a, b}, M⟩ n + 1 := by
  have hpoint (p : ℕ × ℕ) : seedHeight a' b' M' p ≤ seedHeight a b M p + 1 := by
    unfold seedHeight
    apply max_le
    · exact hM.trans (Nat.add_le_add_right (le_max_left _ _) 1)
    · apply max_le
      · calc
          a' + p.1 ≤ (a + p.1) + 1 := by omega
          _ ≤ max M (max (a + p.1) (b + p.2)) + 1 :=
            Nat.add_le_add_right ((le_max_left _ _).trans (le_max_right _ _)) 1
      · calc
          b' + p.2 ≤ (b + p.2) + 1 := by omega
          _ ≤ max M (max (a + p.1) (b + p.2)) + 1 :=
            Nat.add_le_add_right ((le_max_right _ _).trans (le_max_right _ _)) 1
  unfold meanGrowth
  rw [join_seed_mean a' b' M' hab' n, join_seed_mean a b M hab n]
  have hi : Integrable (fun p => (seedHeight a b M p : ℝ)) (RRTSplit.heightPairLaw n) :=
    RRTSplit.heightPairLaw_integrable n _
  have hh := integral_mono (RRTSplit.heightPairLaw_integrable n
      (fun p => (seedHeight a' b' M' p : ℝ))) (hi.add (integrable_const 1))
    (fun p => (by exact_mod_cast hpoint p :
      (seedHeight a' b' M' p : ℝ) ≤ (seedHeight a b M p : ℝ) + 1))
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const 1), integral_const] at hh
  simpa only [probReal_univ, smul_eq_mul, mul_one] using hh

theorem attachFreezeMean_le (a b M n : ℕ) (hab : max a b ≤ M) :
    attachFreezeMean a b M n ≤
      (freezeAttachMean a b M n + 2 * meanGrowth ⟨{a, b}, M⟩ n + 2) / 3 := by
  have ha : a ≤ M := (le_max_left a b).trans hab
  have hb : b ≤ M := (le_max_right a b).trans hab
  have hMa : max M (a + 1) ≤ M + 1 := max_le (Nat.le_succ M) (by omega)
  have hMb : max M (b + 1) ≤ M + 1 := max_le (Nat.le_succ M) (by omega)
  have h₁ := meanGrowth_pair_le_add_one a b M a b (max M (a + 1)) n hab
    (hab.trans (le_max_left _ _)) (Nat.le_succ a) (Nat.le_succ b) hMa
  have h₂ := meanGrowth_pair_le_add_one a b M (a + 1) b (max M (a + 1)) n hab
    (max_le (le_max_right _ _) (hb.trans (le_max_left _ _))) le_rfl (Nat.le_succ b) hMa
  have h₃ := meanGrowth_pair_le_add_one a b M a b (max M (b + 1)) n hab
    (hab.trans (le_max_left _ _)) (Nat.le_succ a) (Nat.le_succ b) hMb
  have h₄ := meanGrowth_pair_le_add_one a b M a (b + 1) (max M (b + 1)) n hab
    (max_le (ha.trans (le_max_left _ _)) (le_max_right _ _)) (Nat.le_succ a) le_rfl hMb
  unfold attachFreezeMean freezeAttachMean
  linarith

theorem baseline_sub_attachFreezeMean_ge (a b M n : ℕ) (hab : max a b ≤ M) :
    (meanGrowth ⟨{a, b}, M⟩ n - freezeAttachMean a b M n - 2) / 3 ≤
      meanGrowth ⟨{a, b}, M⟩ n - attachFreezeMean a b M n := by
  linarith [attachFreezeMean_le a b M n hab]

end FreezingGrowth.HeightProfile
