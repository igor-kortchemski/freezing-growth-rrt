module

public import FreezingGrowth.PWIT.PathNoTies
public import FreezingGrowth.PWIT.GoodPaths

/-!
# Weighted leading-path identity for the sampled rank class

This is the cyclic-minimum part of AF13 Lemma 4.2, expressed without
conditioning on a null singleton. The finite measure is the sum of actual
path-increment laws over the rank class, so no fixed-word exchangeability is
used. Endpoint weights retain the information needed for time windows.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

section PositiveDepth

variable {d : ℕ} [NeZero d]

theorem integral_rank_leading (k : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun x : Fin d → ℝ => f (∑ i, x i)) (rankIncrementMeasure d k)) :
    (d : ℝ) * (∫ x, {x | minimumAt (centeredBridge x) 0}.indicator
      (fun x => f (∑ i, x i)) x ∂rankIncrementMeasure d k) =
      ∫ x, f (∑ i, x i) ∂rankIncrementMeasure d k := by
  apply integral_weighted_cyclic_minimum (rankIncrementMeasure d k)
    centeredBridge (fun x => f (∑ i, x i)) rotateIncrements
    measurable_centeredBridge hf (rotateIncrements_preserving k)
  · intro r
    exact Filter.Eventually.of_forall fun x => congrArg f (sum_rotateIncrements r x)
  · intro r
    exact Filter.Eventually.of_forall fun x => centeredBridge_rotate r x
  · exact ae_centeredBridge_injective k

end PositiveDepth

section ActualPath

variable (v : Vertex) [NeZero v.length]

theorem cyclicPrefix_pathIncrement (ω : Sample) (j : ℕ) (hj : j ≤ v.length) :
    cyclicPrefix (pathIncrement v ω) j = birth ω (v.take j) := by
  rw [birth_take_eq_sum ω v j hj]
  unfold cyclicPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hj)

theorem leading_zero_iff_minimumAt (ω : Sample) :
    leading 0 v ω ↔ minimumAt (centeredBridge (pathIncrement v ω)) 0 := by
  have hs := birth_eq_sum_pathIncrement ω v
  rw [minimumAt, centeredBridge_zero]
  constructor
  · intro h i
    have hi := h ⟨i, Nat.lt_succ_of_lt i.isLt⟩
    simp only [centeredBridge, centeredPrefix,
      cyclicPrefix_pathIncrement v ω i i.isLt.le, ← hs]
    simpa only [sub_zero, sub_nonneg] using hi
  · intro h j
    by_cases hj : (j : ℕ) < v.length
    · have hi := h ⟨j, hj⟩
      simpa only [centeredBridge, centeredPrefix,
        cyclicPrefix_pathIncrement v ω j hj.le, ← hs, sub_nonneg, sub_zero] using hi
    · have he : (j : ℕ) = v.length := by omega
      have hd : (v.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v.length)
      simp [he, hd]

end ActualPath

section SampledPath

variable {d : ℕ} [NeZero d]

theorem cyclicPrefix_tupleIncrement (r : Fin d → ℕ) (ω : Sample) (j : ℕ) (hj : j ≤ d) :
    cyclicPrefix (tupleIncrement r ω) j = birth ω ((List.ofFn r).take j) := by
  have hj' : j ≤ (List.ofFn r).length := by simpa using hj
  rw [birth_take_eq_sum ω (List.ofFn r) j hj']
  unfold cyclicPrefix
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have he : Fin.ofNat d (i : ℕ) = i.castLE hj := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hj)
  rw [he]
  simp only [tupleIncrement, pathIncrement, List.get_ofFn]
  rfl

theorem leading_zero_ofFn_iff_minimumAt (r : Fin d → ℕ) (ω : Sample) :
    leading 0 (List.ofFn r) ω ↔ minimumAt (centeredBridge (tupleIncrement r ω)) 0 := by
  have hs := birth_ofFn_eq_sum_tupleIncrement r ω
  rw [minimumAt, centeredBridge_zero]
  unfold leading
  simp only [List.length_ofFn, sub_zero]
  constructor
  · intro h i
    have hi := h ⟨i, by simpa only [List.length_ofFn] using Nat.lt_succ_of_lt i.isLt⟩
    simp only [centeredBridge, centeredPrefix,
      cyclicPrefix_tupleIncrement r ω i i.isLt.le, ← hs]
    exact sub_nonneg.mpr hi
  · intro h j
    by_cases hj : (j : ℕ) < d
    · have hi := h ⟨j, hj⟩
      simpa only [centeredBridge, centeredPrefix,
        cyclicPrefix_tupleIncrement r ω j hj.le, ← hs, sub_nonneg] using hi
    · have hj' : (j : ℕ) < d + 1 := by simpa only [List.length_ofFn] using j.isLt
      have he : (j : ℕ) = d := by omega
      have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
      have ht : (List.ofFn r).take d = List.ofFn r := by
        simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn r))
      simp [he, hd, ht]

/-- The sampled-path identity on the actual PWIT probability space, summed
over every rank word. The common endpoint weight can select any time window.
No assertion is made for one fixed word before summation. -/
theorem integral_leading_rankClass (k : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun x : Fin d → ℝ => f (∑ i, x i)) (rankIncrementMeasure d k)) :
    (d : ℝ) *
        (∑ r ∈ Finset.Nat.antidiagonalTuple d k,
          ∫ ω, {ω | leading 0 (List.ofFn r) ω}.indicator
            (fun ω => f (birth ω (List.ofFn r))) ω ∂law) =
      ∑ r ∈ Finset.Nat.antidiagonalTuple d k,
        ∫ ω, f (birth ω (List.ofFn r)) ∂law := by
  classical
  let w : (Fin d → ℝ) → ℝ := fun x => f (∑ i, x i)
  let g : (Fin d → ℝ) → ℝ := {x | minimumAt (centeredBridge x) 0}.indicator w
  have hg : Integrable g (rankIncrementMeasure d k) :=
    hf.indicator (measurableSet_minimumAt measurable_centeredBridge 0)
  have hwr : ∀ r ∈ Finset.Nat.antidiagonalTuple d k, Integrable w (incrementLaw r) :=
    integrable_finsetSum_measure.mp hf
  have hgr : ∀ r ∈ Finset.Nat.antidiagonalTuple d k, Integrable g (incrementLaw r) :=
    integrable_finsetSum_measure.mp hg
  have mapIntegral (r : Fin d → ℕ) (q : (Fin d → ℝ) → ℝ)
      (hq : Integrable q (incrementLaw r)) :
      (∫ x, q x ∂incrementLaw r) = ∫ ω, q (tupleIncrement r ω) ∂law := by
    rw [← map_tupleIncrement r] at hq ⊢
    exact integral_map (measurable_tupleIncrement r).aemeasurable hq.aestronglyMeasurable
  have hlead (r : Fin d → ℕ) (hr : r ∈ Finset.Nat.antidiagonalTuple d k) :
      (∫ x, g x ∂incrementLaw r) =
        ∫ ω, {ω | leading 0 (List.ofFn r) ω}.indicator
          (fun ω => f (birth ω (List.ofFn r))) ω ∂law := by
    rw [mapIntegral r g (hgr r hr)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simp only [g, w, Set.indicator_apply, Set.mem_ofPred_eq,
        ← leading_zero_ofFn_iff_minimumAt, ← birth_ofFn_eq_sum_tupleIncrement]
  have hend (r : Fin d → ℕ) (hr : r ∈ Finset.Nat.antidiagonalTuple d k) :
      (∫ x, w x ∂incrementLaw r) = ∫ ω, f (birth ω (List.ofFn r)) ∂law := by
    rw [mapIntegral r w (hwr r hr)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => congrArg f
      (birth_ofFn_eq_sum_tupleIncrement r ω).symm
  calc
    _ = (d : ℝ) * ∑ r ∈ Finset.Nat.antidiagonalTuple d k, ∫ x, g x ∂incrementLaw r := by
      congr 1
      exact Finset.sum_congr rfl fun r hr => (hlead r hr).symm
    _ = (d : ℝ) * ∫ x, g x ∂rankIncrementMeasure d k := by
      rw [rankIncrementMeasure, integral_finsetSum_measure hgr]
    _ = ∫ x, w x ∂rankIncrementMeasure d k := integral_rank_leading k f hf
    _ = ∑ r ∈ Finset.Nat.antidiagonalTuple d k, ∫ x, w x ∂incrementLaw r := by
      rw [rankIncrementMeasure, integral_finsetSum_measure hwr]
    _ = _ := Finset.sum_congr rfl hend

end SampledPath

end FreezingGrowth.PWIT
