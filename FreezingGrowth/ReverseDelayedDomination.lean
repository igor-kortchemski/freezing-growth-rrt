module

public import FreezingGrowth.ReverseFirstUseGraft

/-! The pathwise component-height invariant of Algorithm 3. Once the
distinguished singleton has been used, the actual longer forest dominates
the aligned actual shorter forest. No shorter marginal law is assumed. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical

namespace RootedForest

variable {V : Type*} [DecidableEq V]

theorem componentHeight_le_singleton_receiver (F : RootedForest V) {d v r : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) (hr : r ∈ F.roots) :
    F.componentHeight r ≤
      ((F.adjoin d hd).joinChoice (d, v)).componentHeight (Equiv.swap d v r) := by
  have hpair := adjoin_receiver_pair_valid F hd hv
  have hdv : d ≠ v := (Finset.mem_offDiag.mp hpair).2.2
  have hrd : r ≠ d := fun he => hd (he ▸ (mem_roots.mp hr).1)
  rw [joinChoice, dite_eq_left hpair]
  by_cases hrv : r = v
  · subst r
    rw [Equiv.swap_apply_right, componentHeight_join_receiver,
      componentHeight_adjoin_new, componentHeight_adjoin_other F hd hdv.symm]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne hrd hrv,
      componentHeight_join_other _ _ _ _ hrd hrv,
      componentHeight_adjoin_other F hd hrd]

theorem componentHeight_le_singleton_child (F : RootedForest V) {d v r : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) (hr : r ∈ F.roots) :
    F.componentHeight r ≤ ((F.adjoin d hd).joinChoice (v, d)).componentHeight r := by
  have hpair := adjoin_child_pair_valid F hd hv
  have hvd : v ≠ d := (Finset.mem_offDiag.mp hpair).2.2
  have hrd : r ≠ d := fun he => hd (he ▸ (mem_roots.mp hr).1)
  rw [joinChoice, dite_eq_left hpair]
  by_cases hrv : r = v
  · subst r
    rw [componentHeight_join_receiver, componentHeight_adjoin_other F hd hvd,
      componentHeight_adjoin_new]
    exact le_max_left _ _
  · rw [componentHeight_join_other _ _ _ _ hrv hrd,
      componentHeight_adjoin_other F hd hrd]

end RootedForest

namespace ReverseOrdered

theorem FirstUseGraft.heightProfile_le {F : Forest} {i : ℕ} {z : InitializationSample}
    (hi : Sum.inr i ∉ F.forest.vertices) (h : FirstUseGraft F i z) :
    ReverseHeightList.LE (heightProfile z.shorter) (heightProfile z.longer) := by
  obtain ⟨hs, q, hq | hq⟩ := h
  · rw [hs]
    unfold heightProfile ReverseHeightList.LE
    rw [hq.2.2, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro r hr
    rw [Function.comp_apply, hq.2.1, Reverse.insertLabel, dite_eq_right hi]
    exact RootedForest.componentHeight_le_singleton_receiver F.forest hi
      (rootEnumeration F q).property ((mem_rootOrder F r).mp hr)
  · rw [hs]
    unfold heightProfile ReverseHeightList.LE
    rw [hq.2.2, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro r hr
    rw [hq.2.1, Reverse.insertLabel, dite_eq_right hi]
    exact RootedForest.componentHeight_le_singleton_child F.forest hi
      (rootEnumeration F q).property ((mem_rootOrder F r).mp hr)

def UsedHeightDomination (z : InitializationSample) : Prop :=
  z.used = true → ReverseHeightList.LE (heightProfile z.shorter) (heightProfile z.longer)

theorem initializationLaw_ae_usedHeightDomination (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    ∀ᵐ z ∂initializationLaw F i, UsedHeightDomination z := by
  filter_upwards [initializationLaw_ae_firstUseGraft F hi] with z hz
  intro hu
  exact FirstUseGraft.heightProfile_le hi (hz hu)

/-- The exact finite-position height update of the actual ordered graph graft. -/
theorem heightProfile_joinPositions (F : Forest) {p : ℕ × ℕ}
    (hp : LegalPositions F p) :
    heightProfile (joinPositions F p) =
      ReverseHeightList.graft (heightProfile F) p.1 p.2 := by
  let a : Fin F.forest.roots.card := ⟨p.1, hp.1⟩
  let b : Fin F.forest.roots.card := ⟨p.2, hp.2.1⟩
  have hab : a ≠ b := fun he => hp.2.2 (congrArg Fin.val he)
  have he := joinPositions_fin F (a, b) hab
  rw [he]
  unfold RootedForest.indexedPair
  rw [rootEnumeration_get, rootEnumeration_get]
  exact heightProfile_joinChoice F
    ⟨p.1, by simpa only [rootOrder_length] using hp.1⟩
    ⟨p.2, by simpa only [rootOrder_length] using hp.2.1⟩
    (fun he => hp.2.2 (congrArg Fin.val he))

theorem synchronizedChoice_usedHeightDomination {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = true) (hd : UsedHeightDomination z)
    (p : ℕ × ℕ) (hp : p.1 < N ∧ p.2 < N ∧ p.1 ≠ p.2) :
    UsedHeightDomination (synchronizedChoice z p) := by
  intro _
  change ReverseHeightList.LE (heightProfile (joinPositions z.shorter p))
    (heightProfile (joinPositions z.longer p))
  rw [heightProfile_joinPositions z.shorter (by simpa only [LegalPositions, hz.shorter_card] using hp),
    heightProfile_joinPositions z.longer (by simpa only [LegalPositions, hz.longer_card] using hp)]
  exact ReverseHeightList.graft_mono (hd hu) p.1 p.2

theorem delayedTransition_ae_usedHeightDomination {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) (hd : UsedHeightDomination z) :
    ∀ᵐ z' ∂delayedTransition i z, UsedHeightDomination z' := by
  rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN)]
  cases hu : z.used with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact initializationLaw_ae_usedHeightDomination (consumeDelayed z) hz.consume_fresh
  | true =>
    simp only [↓reduceIte, synchronizedLaw]
    apply (ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete).mpr
    filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag
      (Finset.range z.shorter.forest.roots.card)] with p hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    have ha' : p.1 < N := by simpa only [Finset.mem_range, hz.shorter_card] using ha
    have hb' : p.2 < N := by simpa only [Finset.mem_range, hz.shorter_card] using hb
    exact synchronizedChoice_usedHeightDomination hz hu hd p ⟨ha', hb', hab⟩

theorem delayedLawAfter_ae_usedHeightDomination (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    ∀ᵐ z ∂delayedLawAfter F i t, UsedHeightDomination z := by
  induction t with
  | zero => exact initializationLaw_ae_usedHeightDomination F hi
  | succ t ih =>
    rw [ae_iff, delayedLawAfter, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [delayedLawAfter_ae_valid F hi t (by omega), ih (by omega)] with z hz hd
    simpa only [Pi.zero_apply] using
      ae_iff.mp (delayedTransition_ae_usedHeightDomination hz (by omega) hd)

theorem delayedLawAfter_terminal_heightProfile_le (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    ∀ᵐ z ∂delayedLawAfter F i (F.forest.roots.card - 1),
      ReverseHeightList.LE (heightProfile z.shorter) (heightProfile z.longer) := by
  filter_upwards [delayedLawAfter_ae_usedHeightDomination F hi _ le_rfl,
    delayedLawAfter_terminal_used F hi hF] with z hd hu
  exact hd hu

theorem sourceDelayedLaw_ae_usedHeightDomination (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail))
    (t : ℕ) (ht : t ≤ k - 1) :
    ∀ᵐ z ∂sourceDelayedLaw k tail t, UsedHeightDomination z := by
  rw [ae_iff, sourceDelayedLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  exact ae_iff.mp (delayedLawAfter_ae_usedHeightDomination F hF.1 t
    (by simpa only [hF.2] using ht))

/-- Source C8's terminal pathwise comparison on the actual joint construction.
Its use as a stochastic comparison additionally needs the two marginal laws. -/
theorem sourceDelayedLaw_terminal_maxDepth_le (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ z ∂sourceDelayedLaw k tail (k - 1),
      z.shorter.forest.maxDepth ≤ z.longer.forest.maxDepth := by
  filter_upwards [sourceDelayedLaw_ae_usedHeightDomination k tail ha _ le_rfl,
    sourceDelayedLaw_terminal_used k hk tail ha] with z hd hu
  have hh := ReverseHeightList.le_maximum (hd hu)
  simpa only [heightProfile_max] using hh

end ReverseOrdered
end FreezingGrowth
