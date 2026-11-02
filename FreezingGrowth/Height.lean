module

public import FreezingGrowth.ForwardLaw

/-!
# The height of the actual forward tree

Heights are graph distances, by `ValidAt.height_eq_tree_dist`. Freezing changes
only activity labels, including at extinction, and leaves the height law fixed.
-/

@[expose] public section

namespace FreezingGrowth.Forward

open MeasureTheory
open scoped ENNReal Classical

/-- Maximum distance from the root in the finite tree. -/
def treeHeight (s : State) : ℕ := s.vertices.sup s.height

theorem height_le_treeHeight {s : State} {v : ℕ} (hv : v ∈ s.vertices) :
    s.height v ≤ treeHeight s := Finset.le_sup hv

theorem treeHeight_initial : treeHeight initial = 0 := by
  simp [treeHeight, initial]

theorem treeHeight_freeze (s : State) (t v : ℕ) :
    treeHeight (freeze s t v) = treeHeight s := rfl

theorem treeHeight_attach (s : State) (t v : ℕ) (ht : t ∉ s.vertices) :
    treeHeight (attach s t v) = max (treeHeight s) (s.height v + 1) := by
  have hs : s.vertices.sup (Function.update s.height t (s.height v + 1)) =
      s.vertices.sup s.height := by
    apply Finset.sup_congr rfl
    intro w hw
    have hwt : w ≠ t := fun h => ht (h ▸ hw)
    simp [hwt]
  unfold treeHeight attach
  rw [Finset.sup_insert]
  simp only [Function.update_self, hs]
  exact max_comm _ _

theorem treeHeight_step_freeze (s : State) (t v : ℕ) :
    treeHeight (step s t false v) = treeHeight s := by
  by_cases hv : v ∈ s.active <;> simp [step, hv, treeHeight_freeze]

/-- The one-step height bound used at `eq:HeightIncrease` in the paper. -/
theorem treeHeight_attach_le_succ {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) :
    treeHeight (attach s (n + 1) v) ≤ treeHeight s + 1 := by
  have ht : n + 1 ∉ s.vertices := by
    intro h; have := hs.vertices_le _ h; omega
  rw [treeHeight_attach s _ _ ht]
  have h := height_le_treeHeight (hs.active_subset hv)
  omega

/-- An attachment increases the height exactly when its parent has maximal height. -/
theorem treeHeight_attach_eq_succ_iff {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.active) :
    treeHeight (attach s (n + 1) v) = treeHeight s + 1 ↔
      s.height v = treeHeight s := by
  have ht : n + 1 ∉ s.vertices := by
    intro h; have := hs.vertices_le _ h; omega
  rw [treeHeight_attach s _ _ ht]
  have h := height_le_treeHeight (hs.active_subset hv)
  omega

/-- The actual height distribution of Algorithm 1 after `n` steps. -/
noncomputable def heightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).map treeHeight

instance heightLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (heightLaw x n) :=
  (Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable).mpr inferInstance

theorem map_transitionLaw_height_freeze (s : State) (t : ℕ) :
    (transitionLaw s t false).map treeHeight = Measure.dirac (treeHeight s) := by
  ext A hA
  rw [Measure.map_apply measurable_from_top hA, Measure.dirac_apply' _ hA]
  by_cases hs : s.active.Nonempty
  · rw [transitionLaw_apply s t false hs]
    by_cases hmem : treeHeight s ∈ A
    · simp only [Set.mem_preimage, treeHeight_step_freeze, hmem, Finset.filter_true,
        Set.indicator_of_mem hmem, Pi.one_apply]
      exact ENNReal.div_self (by exact_mod_cast hs.card_pos.ne') (by simp)
    · simp [treeHeight_step_freeze, hmem]
  · rw [transitionLaw_eq_dirac_of_empty s t false (Finset.not_nonempty_iff_eq_empty.mp hs)]
    rw [Measure.dirac_apply' _ (measurable_from_top hA)]
    rfl

/-- Removing the last freezing step preserves height, even if that step causes extinction.
This supplies the missing endpoint reduction in the low-values argument of Theorem 1.2. -/
theorem heightLaw_succ_freeze (x : SignSequence) (n : ℕ) (hx : x (n + 1) = false) :
    heightLaw x (n + 1) = heightLaw x n := by
  unfold heightLaw
  rw [treeLaw, hx, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  simp_rw [map_transitionLaw_height_freeze]
  exact Measure.bind_dirac_eq_map _ measurable_from_top

end FreezingGrowth.Forward
