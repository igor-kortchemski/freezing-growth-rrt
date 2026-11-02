module

public import FreezingGrowth.ReverseDelayedDynamics
public import FreezingGrowth.ReverseHeightInitialization

/-! Exact labelled graft geometry when the distinguished singleton is first
used. Original sampled positions are retained, and the comparison is between
complete rooted forests, rather than only their heights. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical

namespace RootedForest

variable {V : Type*} [DecidableEq V]

theorem adjoin_receiver_pair_valid (F : RootedForest V) {d v : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) :
    (d, v) ∈ (F.adjoin d hd).roots.offDiag := by
  rw [adjoin_roots]
  have hdv : d ≠ v := by
    intro he
    apply hd
    rw [he]
    exact (mem_roots.mp hv).1
  exact Finset.mem_offDiag.mpr ⟨Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem hv, hdv⟩

theorem adjoin_child_pair_valid (F : RootedForest V) {d v : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) :
    (v, d) ∈ (F.adjoin d hd).roots.offDiag := by
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp (adjoin_receiver_pair_valid F hd hv)
  exact Finset.mem_offDiag.mpr ⟨hb, ha, hab.symm⟩

theorem adjoin_joinChoice_graph (F : RootedForest V) {d v : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) :
    ((F.adjoin d hd).joinChoice (d, v)).graph = F.graph ⊔ SimpleGraph.edge d v ∧
    ((F.adjoin d hd).joinChoice (v, d)).graph = F.graph ⊔ SimpleGraph.edge v d := by
  constructor
  · rw [joinChoice, dite_eq_left (adjoin_receiver_pair_valid F hd hv), join_graph,
      adjoin_graph]
  · rw [joinChoice, dite_eq_left (adjoin_child_pair_valid F hd hv), join_graph,
      adjoin_graph]

/-- Outside the selected old component, every rooted-tree field is unchanged
in both orientations of the singleton graft. -/
theorem adjoin_joinChoice_other_data (F : RootedForest V) {d v w : V}
    (hd : d ∉ F.vertices) (hv : v ∈ F.roots) (hw : w ∈ F.vertices)
    (hroot : F.root w ≠ v) :
    (((F.adjoin d hd).joinChoice (d, v)).parent w = F.parent w ∧
      ((F.adjoin d hd).joinChoice (d, v)).root w = F.root w ∧
      ((F.adjoin d hd).joinChoice (d, v)).depth w = F.depth w) ∧
    (((F.adjoin d hd).joinChoice (v, d)).parent w = F.parent w ∧
      ((F.adjoin d hd).joinChoice (v, d)).root w = F.root w ∧
      ((F.adjoin d hd).joinChoice (v, d)).depth w = F.depth w) := by
  have hwd : w ≠ d := fun he => hd (he ▸ hw)
  have hrd : F.root w ≠ d := fun he => hd (he ▸ F.root_mem w hw)
  have hwv : w ≠ v := by
    intro he
    subst w
    exact hroot (mem_roots.mp hv).2
  constructor
  · rw [joinChoice, dite_eq_left (adjoin_receiver_pair_valid F hd hv)]
    simp [join, adjoin, hwd, hwv, hroot]
  · rw [joinChoice, dite_eq_left (adjoin_child_pair_valid F hd hv)]
    simp [join, adjoin, hwd, hrd]

end RootedForest

namespace ReverseOrdered

/-- The source's two possible complete rooted grafts at the unique positive
original position. The other components keep their positions. -/
def FirstUseGraft (F : Forest) (i : ℕ) (z : InitializationSample) : Prop :=
  z.shorter = F ∧ ∃ q : Fin F.forest.roots.card,
    let v := (rootEnumeration F q).val
    (z.delayedPair = (0, q.val + 1) ∧
      z.longer.forest = (Reverse.insertLabel F.forest i).joinChoice (.inr i, v) ∧
      z.longer.rootOrder = F.rootOrder.map (Equiv.swap (.inr i) v)) ∨
    (z.delayedPair = (q.val + 1, 0) ∧
      z.longer.forest = (Reverse.insertLabel F.forest i).joinChoice (v, .inr i) ∧
      z.longer.rootOrder = F.rootOrder)

theorem FirstUseGraft.original_positions {F : Forest} {i : ℕ} {z : InitializationSample}
    (h : FirstUseGraft F i z) :
    (z.delayedPair.1 = 0 ∨ z.delayedPair.2 = 0) ∧
      1 ≤ max z.delayedPair.1 z.delayedPair.2 ∧
      max z.delayedPair.1 z.delayedPair.2 ≤ F.forest.roots.card := by
  obtain ⟨_, q, hq | hq⟩ := h
  · rw [hq.1]
    dsimp only
    omega
  · rw [hq.1]
    dsimp only
    omega

theorem initializationChoice_firstUseGraft (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin (prependLabel F i).forest.roots.card × Fin (prependLabel F i).forest.roots.card)
    (hp : p.1 ≠ p.2) (hu : (initializationChoice F i p).used = true) :
    FirstUseGraft F i (initializationChoice F i p) := by
  have hzero : p.1.val = 0 ∨ p.2.val = 0 := by
    simpa only [initializationChoice, decide_eq_true_eq] using hu
  have hne : p.1.val ≠ p.2.val := fun he => hp (Fin.ext he)
  have hpair := indexedPair_valid (prependLabel F i) p hp
  refine ⟨rfl, ?_⟩
  rcases hzero with ha | hb
  · have hb : 0 < p.2.val := by omega
    let q := lowerPositiveIndex F hi p.2 hb
    have hq : p.2.val = q.val + 1 := by dsimp [q, lowerPositiveIndex]; omega
    have hqa : (rootEnumeration (prependLabel F i) p.1).val = .inr i :=
      (rootEnumeration_prepend_eq F hi p.1).mpr ha
    have hqb : (rootEnumeration (prependLabel F i) p.2).val =
        (rootEnumeration F q).val := by
      rw [← prependIndex_lowerPositiveIndex F hi p.2 hb]
      exact rootEnumeration_prepend_index F hi q
    have he : (prependLabel F i).forest.indexedPair (rootEnumeration (prependLabel F i)) p =
        (.inr i, (rootEnumeration F q).val) := Prod.ext hqa hqb
    refine ⟨q, Or.inl ⟨?_, ?_, ?_⟩⟩
    · change (p.1.val, p.2.val) = (0, q.val + 1)
      exact Prod.ext ha hq
    · change (distinguishedJoinChoice _ _ _).forest = _
      rw [he, distinguishedJoinChoice_forest, prependLabel_forest]
    · change (distinguishedJoinChoice _ _ _).rootOrder = _
      rw [he]
      exact distinguishedJoinChoice_receiver_rootOrder _ (prependLabel_rootOrder F hi)
        (he ▸ hpair)
  · have ha : 0 < p.1.val := by omega
    let q := lowerPositiveIndex F hi p.1 ha
    have hq : p.1.val = q.val + 1 := by dsimp [q, lowerPositiveIndex]; omega
    have hqa : (rootEnumeration (prependLabel F i) p.1).val =
        (rootEnumeration F q).val := by
      rw [← prependIndex_lowerPositiveIndex F hi p.1 ha]
      exact rootEnumeration_prepend_index F hi q
    have hqb : (rootEnumeration (prependLabel F i) p.2).val = .inr i :=
      (rootEnumeration_prepend_eq F hi p.2).mpr hb
    have he : (prependLabel F i).forest.indexedPair (rootEnumeration (prependLabel F i)) p =
        ((rootEnumeration F q).val, .inr i) := Prod.ext hqa hqb
    refine ⟨q, Or.inr ⟨?_, ?_, ?_⟩⟩
    · change (p.1.val, p.2.val) = (q.val + 1, 0)
      exact Prod.ext hq hb
    · change (distinguishedJoinChoice _ _ _).forest = _
      rw [he, distinguishedJoinChoice_forest, prependLabel_forest]
    · change (distinguishedJoinChoice _ _ _).rootOrder = _
      rw [he]
      exact distinguishedJoinChoice_child_rootOrder _ (prependLabel_rootOrder F hi)
        (he ▸ hpair)

theorem initializationLaw_ae_firstUseGraft (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    ∀ᵐ z ∂initializationLaw F i, z.used = true → FirstUseGraft F i z := by
  unfold initializationLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete).mpr
  have hp : ∀ᵐ p ∂uniformRootPair
      (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)),
      p ∈ (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)).offDiag := by
    rw [ae_iff]
    simp [uniformRootPair, Measure.uniformOfFinset_apply]
  filter_upwards [hp] with p hp
  exact initializationChoice_firstUseGraft F hi p (Finset.mem_offDiag.mp hp).2.2

/-- At a genuine first use after a pending phase, the shorter forest has
already consumed its old delayed pair, exactly as in Algorithm 3. -/
theorem delayedTransition_ae_firstUseGraft {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) (hu : z.used = false) :
    ∀ᵐ z' ∂delayedTransition i z,
      z'.used = true → FirstUseGraft (consumeDelayed z) i z' := by
  rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN), hu]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact initializationLaw_ae_firstUseGraft (consumeDelayed z) hz.consume_fresh

end ReverseOrdered
end FreezingGrowth
