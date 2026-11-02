module

public import FreezingGrowth.TwoSeedGraftProcess
public import FreezingGrowth.TaggedGraftSource

/-! The genuine two intermediate transitions are retained as complete States. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical ENNReal

theorem transitionLaw_singleton (s : Forward.State) (t u : ℕ) (b : Bool)
    (ha : s.active = {u}) :
    Forward.transitionLaw s t b = Measure.dirac (Forward.step s t b u) := by
  rw [Forward.transitionLaw, ite_eq_left (by rw [ha]; simp), ha]
  simp [Measure.uniformOfFinset]

theorem orderedPair_freeze (s : Forward.State) (T : ℕ) (hc : s.active.card = 2) :
    (uniformRootPair s.active).map (fun p => Forward.freeze s (T + 1) p.2) =
      Forward.transitionLaw s (T + 1) false := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
  have ha : a ∈ s.active := by rw [hs]; simp
  have hb : b ∈ s.active := by rw [hs]; simp
  rw [transition_pair s (T + 1) false hs hab, hs, uniformRootPair_pair a b hab,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _)]
  simp only [Forward.step, ite_eq_left ha, ite_eq_left hb, Bool.false_eq_true, ↓reduceIte]
  rw [add_comm]

def freezeAttachHistory (h : FiniteMarkov.History Forward.State) (T u v : ℕ) :
    FiniteMarkov.History Forward.State :=
  (h.push (Forward.freeze h.current (T + 1) v)).push
    (Forward.attach (Forward.freeze h.current (T + 1) v) (T + 2) u)

def attachFreezeHistory (h : FiniteMarkov.History Forward.State) (T u v : ℕ) (c : Fin 3) :
    FiniteMarkov.History Forward.State :=
  (h.push (Forward.attach h.current (T + 1) u)).push (casePrefix h.current T u v c)

/-- Ordered-pair freezing followed by the forced sole-parent attachment has
its exact two-step history law, including the intermediate frozen State. -/
theorem orderedPair_freezeAttachHistory (h : FiniteMarkov.History Forward.State)
    (T : ℕ) (hc : h.current.active.card = 2) :
    (uniformRootPair h.current.active).map (fun p => freezeAttachHistory h T p.1 p.2) =
      (Forward.transitionLaw h.current (T + 1) false).bind (fun q =>
        (Forward.transitionLaw q (T + 2) true).map (fun r => (h.push q).push r)) := by
  rw [← orderedPair_freeze h.current T hc,
    Measure.bind_map (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    ← Measure.bind_dirac_eq_map _ (measurable_of_countable _)]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag h.current.active] with p hp
  have ha := active_eq_pair_of_card_two hc hp
  have hne := (Finset.mem_offDiag.mp hp).2.2
  have hs : (Forward.freeze h.current (T + 1) p.2).active = {p.1} := by
    change h.current.active.erase p.2 = {p.1}
    rw [ha]
    ext a
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [transitionLaw_singleton _ _ _ _ hs, Measure.map_dirac' measurable_from_top]
  simp only [Forward.step, hs, Finset.mem_singleton, ↓reduceIte]
  rfl

/-- The independent tag chooses the actual frozen vertex after the genuine
uniform attachment, retaining both inserted States in the same history. -/
theorem orderedPair_attachFreezeHistory (h : FiniteMarkov.History Forward.State) {T : ℕ}
    (hs : Forward.ValidAt T h.current) (hc : h.current.active.card = 2) :
    (uniformRootPair h.current.active).bind (fun p =>
      TwoSeedCoupling.threeCaseLaw.map (attachFreezeHistory h T p.1 p.2)) =
      (Forward.transitionLaw h.current (T + 1) true).bind (fun q =>
        (Forward.transitionLaw q (T + 2) false).map (fun r => (h.push q).push r)) := by
  rw [← orderedPair_attachment h.current T hc,
    Measure.bind_map (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag h.current.active] with p hp
  have ha := active_eq_pair_of_card_two hc hp
  have hne := (Finset.mem_offDiag.mp hp).2.2
  rw [← threeCaseLaw_casePrefix hs ha hne,
    Measure.map_map measurable_from_top (measurable_of_countable _)]
  rfl

end FreezingGrowth.TwoSeedGraft
