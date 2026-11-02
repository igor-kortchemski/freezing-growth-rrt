module

public import FreezingGrowth.ForwardHeight

/-! At a finite horizon the actual forward construction has finite support.
Consequently every real state observable is integrable at that horizon. -/

@[expose] public section
namespace FreezingGrowth.Forward

open MeasureTheory
open scoped Classical ProbabilityTheory

/-- A finite overestimate of the states reachable at each finite horizon. -/
noncomputable def reachableStates (x : SignSequence) : ℕ → Finset State
  | 0 => {initial}
  | n + 1 => (reachableStates x n).biUnion fun s =>
      insert s ((Finset.range (n + 1)).image (fun v => step s (n + 1) (x (n + 1)) v))

theorem treeLaw_ae_reachable (x : SignSequence) (n : ℕ) :
    ∀ᵐ s ∂treeLaw x n, s ∈ reachableStates x n := by
  have hh := treeLaw_ae_induction x
    (fun n s => ValidAt n s ∧ s ∈ reachableStates x n)
    (by simp [reachableStates, initial_valid])
    (by
      intro n s hs _
      refine ⟨hs.1.mono (Nat.le_succ n), ?_⟩
      exact Finset.mem_biUnion.mpr ⟨s, hs.2, Finset.mem_insert_self _ _⟩)
    (by
      intro n s hs v hv
      refine ⟨hs.1.step _ _, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s, hs.2, Finset.mem_insert_of_mem ?_⟩
      apply Finset.mem_image.mpr
      exact ⟨v, Finset.mem_range.mpr (by
        have hh := hs.1.vertices_le v (hs.1.active_subset hv)
        omega), rfl⟩)
    n
  exact hh.mono (fun _ hs => hs.2)

theorem treeLaw_integrable_state (x : SignSequence) (n : ℕ) (f : State → ℝ) :
    Integrable f (treeLaw x n) := by
  let C : ℝ := ∑ s ∈ reachableStates x n, |f s|
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_ae_reachable x n] with s hs
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun s _ => abs_nonneg (f s)) hs

theorem treeLaw_integral_succ_state (x : SignSequence) (n : ℕ) (f : State → ℝ) :
    (∫ s', f s' ∂treeLaw x (n + 1)) =
      ∫ s, (∫ s', f s' ∂transitionLaw s (n + 1) (x (n + 1))) ∂treeLaw x n := by
  let K : ProbabilityTheory.Kernel State State :=
    ⟨fun s => transitionLaw s (n + 1) (x (n + 1)), measurable_from_top⟩
  have hi := treeLaw_integrable_state x (n + 1) f
  rw [treeLaw] at hi
  have hi' : Integrable f ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
      ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  simpa only [K, treeLaw, ProbabilityTheory.Kernel.coe_mk, ProbabilityTheory.Kernel.comp_apply,
    ProbabilityTheory.Kernel.const_apply] using hh

end FreezingGrowth.Forward
