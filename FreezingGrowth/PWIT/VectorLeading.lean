module

public import FreezingGrowth.PWIT.SampledPath
public import FreezingGrowth.PWIT.CenteredPath
public import FreezingGrowth.PWIT.GoodPaths
import Mathlib.Algebra.BigOperators.Ring.List

/-! A common finite-vector barrier for the simplex and actual path laws.
The empty vector retains the endpoint condition `0 ≤ a`. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory

def vectorLeading {d : ℕ} (a : ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ j : Fin (d + 1),
    (j : ℝ) / d * (∑ i, x i) - a ≤ ((List.ofFn x).take j).sum

theorem take_ofFn_eq {d : ℕ} (x : Fin d → ℝ) (j : ℕ) (hj : j ≤ d) :
    (List.ofFn x).take j = List.ofFn (fun i : Fin j => x (i.castLE hj)) := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hj]
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

@[fun_prop] theorem measurable_vectorPrefix {d : ℕ} (j : ℕ) (hj : j ≤ d) :
    Measurable (fun x : Fin d → ℝ => ((List.ofFn x).take j).sum) := by
  simp only [take_ofFn_eq _ j hj, List.sum_ofFn]
  fun_prop

theorem measurableSet_vectorLeading (d : ℕ) (a : ℝ) :
    MeasurableSet {x : Fin d → ℝ | vectorLeading a x} := by
  unfold vectorLeading
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop) (measurable_vectorPrefix j (by omega))

theorem measurableSet_vectorLeading_joint (d : ℕ) :
    MeasurableSet {z : ℝ × (Fin d → ℝ) | vectorLeading z.1 z.2} := by
  unfold vectorLeading
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (by fun_prop)
    ((measurable_vectorPrefix j (by omega)).comp measurable_snd)

theorem vectorLeading_mono {d : ℕ} {a b : ℝ} (hab : a ≤ b) {x : Fin d → ℝ}
    (hx : vectorLeading a x) : vectorLeading b x := by
  intro j
  have hh := hx j
  linarith

theorem vectorLeading_nonneg {d : ℕ} {a : ℝ} {x : Fin d → ℝ}
    (hx : vectorLeading a x) : 0 ≤ a := by
  have hh := hx 0
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, zero_mul, zero_sub,
    List.take_zero, List.sum_nil] at hh
  linarith

theorem vectorPrefix_smul {d : ℕ} (S : ℝ) (x : Fin d → ℝ) (j : ℕ) (hj : j ≤ d) :
    ((List.ofFn (S • x)).take j).sum = S * ((List.ofFn x).take j).sum := by
  simp only [take_ofFn_eq _ j hj, List.sum_ofFn, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]

theorem cyclicPrefix_eq_vectorPrefix {d : ℕ} [NeZero d] (x : Fin d → ℝ)
    (j : ℕ) (hj : j ≤ d) :
    cyclicPrefix x j = ((List.ofFn x).take j).sum := by
  rw [take_ofFn_eq _ j hj, List.sum_ofFn]
  unfold cyclicPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hj)

theorem vectorLeading_zero_iff_minimumAt {d : ℕ} [NeZero d] (x : Fin d → ℝ) :
    vectorLeading 0 x ↔ minimumAt (centeredBridge x) 0 := by
  rw [minimumAt, centeredBridge_zero]
  constructor
  · intro h i
    have hh := h ⟨i, Nat.lt_succ_of_lt i.isLt⟩
    simp only [centeredBridge, centeredPrefix,
      cyclicPrefix_eq_vectorPrefix x i i.isLt.le]
    exact sub_nonneg.mpr (by simpa only [sub_zero] using hh)
  · intro h j
    by_cases hj : (j : ℕ) < d
    · have hh := h ⟨j, hj⟩
      simpa only [centeredBridge, centeredPrefix,
        cyclicPrefix_eq_vectorPrefix x j hj.le, sub_nonneg, sub_zero] using hh
    · have he : (j : ℕ) = d := by omega
      have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      have ht : (List.ofFn x).take d = List.ofFn x := by
        simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn x))
      simp [he, hd, ht, List.sum_ofFn]

theorem vectorLeading_smul_iff {d : ℕ} {S : ℝ} (hS : 0 < S) (a : ℝ) (x : Fin d → ℝ) :
    vectorLeading a (S • x) ↔ vectorLeading (a / S) x := by
  unfold vectorLeading
  apply forall_congr'
  intro j
  rw [vectorPrefix_smul S x j (by omega)]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  have he : (j : ℝ) / d * (S * ∑ i, x i) - a =
      S * ((j : ℝ) / d * (∑ i, x i) - a / S) := by
    field_simp
  rw [he, mul_le_mul_iff_right₀ hS]

theorem sum_take_tupleIncrement {d : ℕ} (r : Fin d → ℕ) (ω : Sample)
    (j : ℕ) (hj : j ≤ d) :
    ((List.ofFn (tupleIncrement r ω)).take j).sum = birth ω ((List.ofFn r).take j) := by
  have hj' : j ≤ (List.ofFn r).length := by simpa using hj
  rw [take_ofFn_eq _ j hj, List.sum_ofFn, birth_take_eq_sum ω (List.ofFn r) j hj']
  apply Finset.sum_congr rfl
  intro i _
  simp only [tupleIncrement, pathIncrement, List.get_ofFn]
  rfl

/-- The shared barrier is exactly the actual path barrier, including d=0. -/
theorem vectorLeading_tupleIncrement_iff {d : ℕ} (a : ℝ) (r : Fin d → ℕ) (ω : Sample) :
    vectorLeading a (tupleIncrement r ω) ↔ leading a (List.ofFn r) ω := by
  unfold vectorLeading leading
  simp only [List.length_ofFn]
  constructor
  · intro h j
    have hh := h ⟨j, by simpa only [List.length_ofFn] using j.isLt⟩
    have hj : (j : ℕ) ≤ d := by simpa only [List.length_ofFn] using (Nat.le_of_lt_succ j.isLt)
    simpa only [sum_take_tupleIncrement r ω j hj,
      ← birth_ofFn_eq_sum_tupleIncrement] using hh
  · intro h j
    have hh := h ⟨j, by simpa only [List.length_ofFn] using j.isLt⟩
    have hj : (j : ℕ) ≤ d := Nat.le_of_lt_succ j.isLt
    simpa only [sum_take_tupleIncrement r ω j hj,
      ← birth_ofFn_eq_sum_tupleIncrement] using hh

end FreezingGrowth.PWIT
