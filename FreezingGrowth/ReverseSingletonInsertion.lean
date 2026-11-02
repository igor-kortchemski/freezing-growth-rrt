module

public import FreezingGrowth.ReverseHeightRecursion

/-!
# Adding an isolated component increases the terminal height law

This is a recursive reformulation of the delayed-pair argument in Algorithm 3.
It compares actual finite uniform-position coalescence laws. If the first pair
avoids the added singleton, its exact restricted law reduces the problem to
a shorter list. If the first pair uses it, the resulting list dominates the
old list, up to the already verified permutation invariance.

This terminal-law proof does not assert the paper's full path-coupling
invariant or independence of a stored pair from the exposed joint history.
-/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

open MeasureTheory
open scoped Classical ENNReal

/-- Either orientation of a pair hitting the new singleton resolves the
comparison immediately. The receiver case uses a proved permutation, not
an incorrect equality of the ordered lists. -/
theorem finishLaw_tail_le_hit (xs : List ℕ) (a b h : ℕ)
    (ha : a < xs.length + 1) (hb : b < xs.length + 1) (hab : a ≠ b)
    (hhit : a = 0 ∨ b = 0) :
    finishLaw xs {z | h ≤ z} ≤ finishLaw (graft (0 :: xs) a b) {z | h ≤ z} := by
  rcases hhit with rfl | rfl
  · have hb0 : b ≠ 0 := by omega
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [finishLaw_perm (graft_receiver_perm_resolution xs i (by omega))]
    exact finishLaw_tail_mono (le_resolveReceiver xs i) h
  · have ha0 : a ≠ 0 := hab
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
    rw [graft_distinguished_donor]
    exact finishLaw_tail_mono (le_resolveDonor xs i) h

/-- On the avoidance submeasure the induction hypothesis applies after one
ordinary graft. Its normalization is derived from the actual uniform pair
law; the one-component boundary has zero avoidance mass. -/
theorem avoidance_integral_lower_bound (xs : List ℕ) (hx : 1 ≤ xs.length) (h : ℕ)
    (ih : ∀ ys : List ℕ, ys.length < xs.length →
      finishLaw ys {z | h ≤ z} ≤ finishLaw (0 :: ys) {z | h ≤ z}) :
    uniformRootPair (Finset.range (xs.length + 1)) (avoidsDistinguished 0) *
        finishLaw xs {z | h ≤ z} ≤
      ∫⁻ p in avoidsDistinguished 0,
        finishLaw (graft (0 :: xs) p.1 p.2) {z | h ≤ z}
        ∂uniformRootPair (Finset.range (xs.length + 1)) := by
  by_cases hx2 : 2 ≤ xs.length
  · rw [uniformRootPair_avoid_zero_mass xs.length hx,
      uniformRootPair_restrict_avoid_zero xs.length hx,
      lintegral_smul_measure, smul_eq_mul,
      lintegral_map (measurable_of_countable _) (measurable_of_countable _),
      finishLaw_tail_step xs hx2]
    refine mul_le_mul' le_rfl ?_
    apply lintegral_mono_ae
    filter_upwards [uniformRootPair_ae_offDiag (Finset.range xs.length)] with p hp
    have hlen := graft_length xs p.1 p.2
      (Finset.mem_range.mp (Finset.mem_offDiag.mp hp).2.1)
    simpa only [successorPair, graft_prepend_zero] using
      ih (graft xs p.1 p.2) (by omega)
  · have hlen : xs.length = 1 := by omega
    rw [uniformRootPair_avoid_zero_mass xs.length hx, hlen]
    norm_num

/-- On the hit submeasure the old terminal law is bounded by every supported
new terminal law. The measure is the actual restriction of the fresh pair. -/
theorem hit_integral_lower_bound (xs : List ℕ) (h : ℕ) :
    uniformRootPair (Finset.range (xs.length + 1)) (avoidsDistinguished 0)ᶜ *
        finishLaw xs {z | h ≤ z} ≤
      ∫⁻ p in (avoidsDistinguished 0)ᶜ,
        finishLaw (graft (0 :: xs) p.1 p.2) {z | h ≤ z}
        ∂uniformRootPair (Finset.range (xs.length + 1)) := by
  rw [mul_comm]
  rw [← Measure.restrict_apply_univ (avoidsDistinguished (0 : ℕ))ᶜ,
    ← lintegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae
    (uniformRootPair_ae_offDiag (Finset.range (xs.length + 1))),
    ae_restrict_mem (show MeasurableSet (avoidsDistinguished (0 : ℕ))ᶜ from
      (Set.to_countable _).measurableSet)] with p hp hhit
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  exact finishLaw_tail_le_hit xs p.1 p.2 h
    (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab
    (by simpa only [Set.mem_compl_iff, avoidsDistinguished, Set.mem_ofPred_eq,
      not_and_or, not_not] using hhit)

/-- A new isolated component can only increase the final maximum-height
distribution after complete uniform ordered-position coalescence. -/
theorem finishLaw_tail_le_prepend_zero (xs : List ℕ) (h : ℕ) :
    finishLaw xs {z | h ≤ z} ≤ finishLaw (0 :: xs) {z | h ≤ z} := by
  suffices hall : ∀ n : ℕ, ∀ ys : List ℕ, ys.length = n →
      finishLaw ys {z | h ≤ z} ≤ finishLaw (0 :: ys) {z | h ≤ z} from
    hall xs.length xs rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ys hlen
    by_cases hn : n = 0
    · have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hy]
    · have hy : 1 ≤ ys.length := by omega
      let U := uniformRootPair (Finset.range (ys.length + 1))
      let A := avoidsDistinguished (0 : ℕ)
      let P := finishLaw ys {z | h ≤ z}
      let f := fun p : ℕ × ℕ => finishLaw (graft (0 :: ys) p.1 p.2) {z | h ≤ z}
      have hU : IsProbabilityMeasure U := uniformRootPair_isProbabilityMeasure _ (by
        simpa using (show 2 ≤ ys.length + 1 by omega))
      have hA : MeasurableSet A := (Set.to_countable _).measurableSet
      have havoid : U A * P ≤ ∫⁻ p in A, f p ∂U :=
        avoidance_integral_lower_bound ys hy h (fun zs hz => ih zs.length (by omega) zs rfl)
      have hhit : U Aᶜ * P ≤ ∫⁻ p in Aᶜ, f p ∂U := hit_integral_lower_bound ys h
      rw [finishLaw_tail_step (0 :: ys) (by simp only [List.length_cons]; omega)]
      change P ≤ ∫⁻ p, f p ∂U
      calc
        P = (U A + U Aᶜ) * P := by rw [measure_add_measure_compl hA, measure_univ, one_mul]
        _ = U A * P + U Aᶜ * P := add_mul _ _ _
        _ ≤ (∫⁻ p in A, f p ∂U) + ∫⁻ p in Aᶜ, f p ∂U := add_le_add havoid hhit
        _ = ∫⁻ p, f p ∂U := lintegral_add_compl f hA

/-- Appending instead of prepending the new component has the same final
law, so this form matches the actual ordered reverse freeze operation. -/
theorem finishLaw_tail_le_append_zero (xs : List ℕ) (h : ℕ) :
    finishLaw xs {z | h ≤ z} ≤ finishLaw (xs ++ [0]) {z | h ≤ z} := by
  have hperm : (xs ++ [0]).Perm (0 :: xs) := List.perm_append_singleton 0 xs
  rw [finishLaw_perm hperm]
  exact finishLaw_tail_le_prepend_zero xs h

end FreezingGrowth.ReverseHeightList
