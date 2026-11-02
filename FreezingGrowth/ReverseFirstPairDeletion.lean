module

public import FreezingGrowth.ReverseHeightDynamics
public import FreezingGrowth.ReverseSingletonInsertion
public import FreezingGrowth.FirstPeakDeletion
public import FreezingGrowth.MainStatements

/-!
# Theorem 1.3: deleting the first attachment-freeze peak

The actual reverse process has the same component-height law on the common
tail, because the two schedules have the same terminal active population.
At the end of that tail both have exactly `k` components. The shorter prefix
coalesces those components; the longer prefix first appends a zero-height
component and then coalesces. The proved singleton-insertion comparison
therefore gives the stochastic comparison of the actual forward heights.

The argument includes `k = 1` and words ending at extinction. It is a terminal
law reformulation of the paper's coupling proof; the stronger source claims
about a joint path construction remain separate obligations.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical
open ReverseHeightList

namespace Word

/-- The component count after processing the common suffix is the active
population at its left boundary. This is transported from the actual ordered
forest process, rather than postulated for the abstract executor. -/
theorem runBackward_tail_length (pre tail : Word)
    (ha : (pre ++ tail).admissible) :
    ∀ᵐ hs ∂runBackward tail
        (Measure.dirac (List.replicate
          (activeCount (pre ++ tail).toSigns (pre ++ tail).length).toNat 0)),
      hs.length = (activeCount pre.toSigns pre.length).toNat := by
  have hm := ReverseOrdered.map_lawAfter_heightProfile (pre ++ tail) ha tail.length
    (by simp)
  simp only [List.length_append, Nat.add_sub_cancel_right, List.drop_left] at hm
  simp only [List.length_append]
  rw [← hm]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  have hl := ReverseOrdered.lawAfter_rootOrder_length (pre ++ tail).toSigns
    (pre ++ tail).length tail.length
    ((admissible_iff_le_extinctionTime _).mp ha) (by simp)
  simp only [List.length_append, Nat.add_sub_cancel_right] at hl
  filter_upwards [hl] with F hF
  rw [ReverseOrdered.heightProfile_length, hF]
  simp only [activeCount_append_left pre tail le_rfl]

/-- The stochastic half of Theorem 1.3, for the genuine finite-word height
law. Every common-tail and reverse/forward law identification is supplied by
the construction theorems; no coupling or marginal assumption is used. -/
theorem first_peak_deletion_heightLE (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    HeightLE (List.replicate (k - 1) true ++ tail)
      (List.replicate k true ++ [false] ++ tail) := by
  let long : Word := List.replicate k true ++ [false] ++ tail
  let short : Word := List.replicate (k - 1) true ++ tail
  let μ := runBackward tail (Measure.dirac
    (List.replicate (activeCount long.toSigns long.length).toNat 0))
  have hshort : short.admissible := first_peak_deletion_admissible k hk tail ha
  have hterminal : activeCount long.toSigns long.length =
      activeCount short.toSigns short.length := by
    simpa only [long, short, List.length_append, List.length_replicate,
      List.length_singleton] using first_peak_deletion_activeCount k hk tail tail.length
  have hlength : ∀ᵐ hs ∂μ, hs.length = k := by
    have hl := runBackward_tail_length (List.replicate k true ++ [false]) tail ha
    simpa only [μ, long, List.length_append, List.length_replicate,
      List.length_singleton, first_peak_prefix_activeCount, Int.toNat_natCast] using hl
  have hshortLaw : short.heightLaw = μ.bind finishLaw := by
    rw [heightLaw_eq_runBackward short hshort, ← hterminal]
    change (runBackward (List.replicate (k - 1) true ++ tail)
      (Measure.dirac (List.replicate (activeCount long.toSigns long.length).toNat 0))).map
      (fun hs => hs.toFinset.sup id) = _
    rw [runBackward_append, map_runBackward_replicate_true]
    apply Measure.bind_congr_right
    filter_upwards [hlength] with hs hhs
    simp only [finishLaw, hhs]
  have hlongLaw : long.heightLaw = μ.bind (fun hs => finishLaw (hs ++ [0])) := by
    rw [heightLaw_eq_runBackward long ha]
    change (runBackward ((List.replicate k true ++ [false]) ++ tail)
      (Measure.dirac (List.replicate (activeCount long.toSigns long.length).toNat 0))).map
      (fun hs => hs.toFinset.sup id) = _
    rw [runBackward_append, runBackward_append, map_runBackward_replicate_true]
    simp only [runBackward]
    rw [Measure.bind_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [hlength] with hs hhs
    rw [profileTransition_false, Measure.dirac_bind measurable_from_top]
    simp only [finishLaw, List.length_append, List.length_singleton, hhs,
      Nat.add_sub_cancel]
  intro h
  change short.heightLaw {z | h ≤ z} ≤ long.heightLaw {z | h ≤ z}
  rw [hshortLaw, hlongLaw,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  exact lintegral_mono (fun hs => finishLaw_tail_le_append_zero hs h)

end Word

/-- Theorem 1.3 with exactly the source-facing signature: admissibility of
the shortened schedule and stochastic domination are both conclusions. -/
theorem firstPairDeletionClaim : FirstPairDeletionClaim := by
  intro k hk tail
  dsimp only
  intro ha
  exact ⟨Word.first_peak_deletion_admissible k hk tail ha,
    Word.first_peak_deletion_heightLE k hk tail ha⟩

end FreezingGrowth
