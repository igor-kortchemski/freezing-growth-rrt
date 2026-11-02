module

public import FreezingGrowth.ReverseHeightList
public import FreezingGrowth.ReverseUniformRootPair
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The finite coalescence kernel on component heights

The uniform choice is over ordered distinct positions, retaining multiplicity
when different components have equal heights. `finishLaw` uses exactly one
fewer joins than the number of components. Its semantic projection from the
actual forest, permutation invariance, and singleton-insertion comparison
are separate obligations; none is built into these definitions.
-/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

open MeasureTheory
open scoped Classical ENNReal

instance : MeasurableSpace (List ℕ) := ⊤
instance : DiscreteMeasurableSpace (List ℕ) := ⟨fun _ => trivial⟩

/-- The actual finite ordered-pair kernel; lists with fewer than two entries
are held fixed. -/
noncomputable def graftLaw (xs : List ℕ) : Measure (List ℕ) :=
  if 2 ≤ xs.length then
    (uniformRootPair (Finset.range xs.length)).map (fun p => graft xs p.1 p.2)
  else Measure.dirac xs

instance graftLaw_probability (xs : List ℕ) : IsProbabilityMeasure (graftLaw xs) := by
  unfold graftLaw
  split_ifs with hx
  · have : IsProbabilityMeasure (uniformRootPair (Finset.range xs.length)) :=
      uniformRootPair_isProbabilityMeasure _ (by simpa using hx)
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_of_countable _).aemeasurable).mpr inferInstance
  · infer_instance

/-- Perform a prescribed number of joins, then observe the maximum height.
The fixed-list convention makes this meaningful for every fuel and list. -/
noncomputable def finishAfter : ℕ → List ℕ → Measure ℕ
  | 0, xs => Measure.dirac (xs.toFinset.sup id)
  | k + 1, xs => (graftLaw xs).bind (finishAfter k)

instance finishAfter_probability (k : ℕ) (xs : List ℕ) :
    IsProbabilityMeasure (finishAfter k xs) := by
  induction k generalizing xs with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall ih)

/-- Complete coalescence down to one component; the empty list has height
zero and requires no joins. -/
noncomputable def finishLaw (xs : List ℕ) : Measure ℕ := finishAfter (xs.length - 1) xs

instance finishLaw_probability (xs : List ℕ) : IsProbabilityMeasure (finishLaw xs) :=
  finishAfter_probability _ _

/-- Synchronized finite grafting preserves stochastic maximum-height
domination for every number of steps. Equal component counts are part of
the explicit pointwise list relation. -/
theorem finishAfter_tail_mono (k : ℕ) {xs ys : List ℕ} (hxy : LE xs ys) (h : ℕ) :
    finishAfter k xs {z | h ≤ z} ≤ finishAfter k ys {z | h ≤ z} := by
  induction k generalizing xs ys with
  | zero =>
    have hm := le_maximum hxy
    by_cases hx : h ≤ xs.toFinset.sup id
    · have hy := hx.trans hm
      simp [finishAfter, hx, hy]
    · simp [finishAfter, hx]
  | succ k ih =>
    rw [finishAfter, finishAfter,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    have hlen : xs.length = ys.length := List.Forall₂.length_eq hxy
    by_cases hx : 2 ≤ xs.length
    · have hy : 2 ≤ ys.length := by omega
      rw [graftLaw, graftLaw, ite_eq_left hx, ite_eq_left hy,
        lintegral_map measurable_from_top (measurable_of_countable _),
        lintegral_map measurable_from_top (measurable_of_countable _), ← hlen]
      exact lintegral_mono (fun p => ih (graft_mono hxy p.1 p.2))
    · have hy : ¬2 ≤ ys.length := by omega
      simpa only [graftLaw, ite_eq_right hx, ite_eq_right hy, lintegral_dirac] using ih hxy

theorem finishLaw_tail_mono {xs ys : List ℕ} (hxy : LE xs ys) (h : ℕ) :
    finishLaw xs {z | h ≤ z} ≤ finishLaw ys {z | h ≤ z} := by
  have hlen : xs.length = ys.length := List.Forall₂.length_eq hxy
  simpa only [finishLaw, hlen] using finishAfter_tail_mono (ys.length - 1) hxy h

end FreezingGrowth.ReverseHeightList
