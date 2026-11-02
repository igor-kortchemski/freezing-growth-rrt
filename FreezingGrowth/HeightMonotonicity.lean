module

public import FreezingGrowth.FiniteLaw

/-!
# Height cannot decrease as the forward process runs

These source-facing helpers use the genuine transition measure and its valid
state support. They include freezing, terminal extinction, and absorption after
extinction. They supply the prefix comparison in the high-population argument.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped ENNReal

namespace Forward

theorem treeHeight_le_step {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) (v : ℕ) : treeHeight s ≤ treeHeight (step s (n + 1) sign v) := by
  cases sign
  · rw [treeHeight_step_freeze]
  · by_cases hv : v ∈ s.active
    · have ht : n + 1 ∉ s.vertices := by
        intro h; have := hs.vertices_le _ h; omega
      simp only [step, hv, ↓reduceIte]
      rw [treeHeight_attach s _ _ ht]
      exact le_max_left _ _
    · simp [step, hv]

/-- Every successor lies above any height already reached. -/
theorem transitionLaw_height_tail_eq_one {n : ℕ} {s : State} (hs : ValidAt n s)
    (sign : Bool) {h : ℕ} (hh : h ≤ treeHeight s) :
    transitionLaw s (n + 1) sign {s' | h ≤ treeHeight s'} = 1 := by
  by_cases ha : s.active.Nonempty
  · rw [transitionLaw_apply s _ _ ha]
    have he : s.active.filter (fun v => h ≤ treeHeight (step s (n + 1) sign v)) =
        s.active := by
      apply Finset.filter_eq_self.mpr
      intro v _
      exact hh.trans (treeHeight_le_step hs sign v)
    simp only [Set.mem_ofPred_eq]
    rw [he]
    exact ENNReal.div_self (by exact_mod_cast ha.card_pos.ne') (by simp)
  · simp [transitionLaw, ha, hh]

/-- One more operation stochastically increases the genuine tree height. -/
theorem heightLaw_tail_le_succ (x : SignSequence) (n h : ℕ) :
    heightLaw x n {k | h ≤ k} ≤ heightLaw x (n + 1) {k | h ≤ k} := by
  simp only [heightLaw, Measure.map_apply measurable_from_top
    (show MeasurableSet {k : ℕ | h ≤ k} from by trivial)]
  change treeLaw x n {s | h ≤ treeHeight s} ≤ treeLaw x (n + 1) {s | h ≤ treeHeight s}
  have hE : MeasurableSet {s : State | h ≤ treeHeight s} := by trivial
  rw [treeLaw, Measure.bind_apply hE measurable_from_top.aemeasurable,
    ← lintegral_indicator_one (μ := treeLaw x n) hE]
  apply lintegral_mono_ae
  filter_upwards [treeLaw_valid x n] with s hs
  by_cases hh : h ≤ treeHeight s
  · have ht := transitionLaw_height_tail_eq_one hs (x (n + 1)) hh
    simp [hh, ht]
  · simp [hh]

/-- Stochastic monotonicity in the operation horizon, without a survival premise. -/
theorem heightLaw_tail_mono_time (x : SignSequence) {n m : ℕ} (hnm : n ≤ m) (h : ℕ) :
    heightLaw x n {k | h ≤ k} ≤ heightLaw x m {k | h ≤ k} := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact ih.trans (heightLaw_tail_le_succ x m h)

theorem heightLaw_real_tail_mono_time (x : SignSequence) {n m : ℕ} (hnm : n ≤ m) (h : ℕ) :
    (heightLaw x n).real {k | h ≤ k} ≤ (heightLaw x m).real {k | h ≤ k} :=
  (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
    (heightLaw_tail_mono_time x hnm h)

end Forward

namespace Word

/-- Extending a finite word never decreases its maximum-height law. -/
theorem heightLE_append (xs tail : Word) : HeightLE xs (xs ++ tail) := by
  intro h
  rw [← heightLaw_append_left xs tail]
  exact Forward.heightLaw_tail_mono_time (toSigns (xs ++ tail))
    (by simp : xs.length ≤ (xs ++ tail).length) h

end Word
end FreezingGrowth
