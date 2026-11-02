module

public import FreezingGrowth.PWIT.SampledPath
public import FreezingGrowth.PWIT.CyclicMinimum
public import Mathlib.Data.Nat.Periodic

/-! # Centering finite paths and rotating their bridges -/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

section PositiveDepth

variable {d : ℕ} [NeZero d]

def cyclicPrefix (x : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, x (Fin.ofNat d i)

noncomputable def centeredPrefix (x : Fin d → ℝ) (n : ℕ) : ℝ :=
  cyclicPrefix x n - (n : ℝ) / d * ∑ i, x i

noncomputable def centeredBridge (x : Fin d → ℝ) (i : Fin d) : ℝ := centeredPrefix x i

def rotateIncrements (r : Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => x (r + i)

@[fun_prop] theorem measurable_centeredBridge : Measurable (@centeredBridge d _) := by
  unfold centeredBridge centeredPrefix cyclicPrefix
  fun_prop

omit [NeZero d] in
@[fun_prop] theorem measurable_rotateIncrements (r : Fin d) :
    Measurable (rotateIncrements r) := Measurable.of_eval fun i => measurable_pi_apply (r + i)

private theorem ofNat_val (i : Fin d) : Fin.ofNat d (i : ℕ) = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

private theorem ofNat_add (a b : ℕ) :
    Fin.ofNat d (a + b) = Fin.ofNat d a + Fin.ofNat d b := by
  apply Fin.ext
  exact Nat.add_mod a b d

theorem cyclicPrefix_depth (x : Fin d → ℝ) : cyclicPrefix x d = ∑ i, x i := by
  unfold cyclicPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [ofNat_val]

theorem cyclicPrefix_add (x : Fin d → ℝ) (a b : ℕ) :
    cyclicPrefix x (a + b) = cyclicPrefix x a +
      ∑ i ∈ Finset.range b, x (Fin.ofNat d (a + i)) := by
  exact Finset.sum_range_add _ a b

theorem cyclicPrefix_add_depth (x : Fin d → ℝ) (n : ℕ) :
    cyclicPrefix x (n + d) = cyclicPrefix x n + ∑ i, x i := by
  rw [Nat.add_comm, cyclicPrefix_add, cyclicPrefix_depth]
  have he (i : ℕ) : Fin.ofNat d (d + i) = Fin.ofNat d i := by
    apply Fin.ext
    exact Nat.add_mod_left d i
  simp_rw [he]
  exact add_comm _ _

theorem centeredPrefix_periodic (x : Fin d → ℝ) : Function.Periodic (centeredPrefix x) d := by
  intro n
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [centeredPrefix, cyclicPrefix_add_depth, Nat.cast_add]
  field_simp
  ring

theorem sum_rotateIncrements (r : Fin d) (x : Fin d → ℝ) :
    (∑ i, rotateIncrements r x i) = ∑ i, x i := by
  exact Equiv.sum_comp (Equiv.addLeft r) x

theorem cyclicPrefix_rotate (r : Fin d) (x : Fin d → ℝ) (n : ℕ) :
    cyclicPrefix (rotateIncrements r x) n = cyclicPrefix x ((r : ℕ) + n) - cyclicPrefix x r := by
  rw [cyclicPrefix_add]
  simp only [add_sub_cancel_left, cyclicPrefix, rotateIncrements, ofNat_add, ofNat_val]

theorem centeredPrefix_rotate (r : Fin d) (x : Fin d → ℝ) (n : ℕ) :
    centeredPrefix (rotateIncrements r x) n =
      centeredPrefix x ((r : ℕ) + n) - centeredPrefix x r := by
  simp only [centeredPrefix, cyclicPrefix_rotate, sum_rotateIncrements, Nat.cast_add]
  ring

theorem centeredBridge_rotate (r : Fin d) (x : Fin d → ℝ) :
    centeredBridge (rotateIncrements r x) = bridgeRotate r (centeredBridge x) := by
  funext j
  simp only [centeredBridge, centeredPrefix_rotate, bridgeRotate, Fin.val_add]
  rw [(centeredPrefix_periodic x).map_mod_nat]

theorem rotateIncrements_preserving (k : ℕ) (r : Fin d) :
    MeasurePreserving (rotateIncrements r) (rankIncrementMeasure d k)
      (rankIncrementMeasure d k) := by
  refine ⟨measurable_rotateIncrements r, ?_⟩
  exact rankIncrementMeasure_permutation d k (Equiv.addLeft r)

@[simp] theorem centeredBridge_zero (x : Fin d → ℝ) : centeredBridge x 0 = 0 := by
  simp [centeredBridge, centeredPrefix, cyclicPrefix]

end PositiveDepth

end FreezingGrowth.PWIT
