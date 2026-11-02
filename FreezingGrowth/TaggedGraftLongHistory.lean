module

public import FreezingGrowth.TaggedGraftHistory

/-! The actual full attach/freeze path on the shared original-prefix space. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

noncomputable def taggedOldPrefixLaw (xs : Word) :
    Measure (FiniteMarkov.History Forward.State) :=
  (oldHistoryPairLaw xs).bind (fun o => TwoSeedCoupling.threeCaseLaw.map
    (attachFreezeHistory o.history xs.length o.first o.second))

theorem taggedOldPrefixLaw_eq (xs : Word)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    taggedOldPrefixLaw xs = prefixHistoryLaw (xs ++ [true,false]) := by
  have hh : ∀ᵐ h ∂prefixHistoryLaw xs,
      Forward.ValidAt xs.length h.current ∧ h.current.active.card = 2 := by
    have hv := (Forward.treeLaw_valid xs.toSigns xs.length).and hc
    rw [← prefixHistoryLaw_current xs] at hv
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hv
  rw [taggedOldPrefixLaw, oldHistoryPairLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    prefixHistoryLaw_append_two]
  apply Measure.bind_congr_right
  filter_upwards [hh] with h hh
  rw [Measure.bind_map (measurable_of_countable _).aemeasurable
    measurable_from_top.aemeasurable]
  exact orderedPair_attachFreezeHistory h hh.1 hh.2

private theorem master_tag_comm (n : ℕ)
    (f : Forward.State → Fin 3 → FiniteMarkov.History Forward.State) :
    (Forward.treeLaw RRT.allAttach (n + 1)).bind
        (fun r => TwoSeedCoupling.threeCaseLaw.map (f r)) =
      TwoSeedCoupling.threeCaseLaw.bind
        (fun c => (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => f r c)) := by
  calc
    _ = (Forward.treeLaw RRT.allAttach (n + 1)).bind
        (fun r => TwoSeedCoupling.threeCaseLaw.bind (fun c => Measure.dirac (f r c))) := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun r =>
        (Measure.bind_dirac_eq_map _ (measurable_of_countable _)).symm)
    _ = TwoSeedCoupling.threeCaseLaw.bind
        (fun c => (Forward.treeLaw RRT.allAttach (n + 1)).bind
          (fun r => Measure.dirac (f r c))) :=
      Measure.bind_comm (measurable_from_prod_countable_left (fun _ => measurable_from_top))
    _ = _ := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun c => Measure.bind_dirac_eq_map _ measurable_from_top)

/-- Exact full attach/freeze word history, retaining both intermediate States
and the entire common original prefix on the same probability space. -/
theorem taggedHistoryLaw_longHistory (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (taggedHistoryLaw xs n).map (TaggedHistorySample.longHistory xs.length n) =
      prefixHistoryLaw ((xs ++ [true,false]) ++ List.replicate n true) := by
  rw [taggedHistoryLaw, historySampleLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    prefixHistoryLaw_attachSuffix, ← taggedOldPrefixLaw_eq xs hc, taggedOldPrefixLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [oldHistoryPairLaw_ae_parameters xs hc] with o ho
  rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  have hleft : (Forward.treeLaw RRT.allAttach (n + 1)).bind
      (fun r => (TwoSeedCoupling.threeCaseLaw.map
        (fun c => (⟨(⟨o,r⟩ : HistorySample),c⟩ : TaggedHistorySample))).map
          (TaggedHistorySample.longHistory xs.length n)) =
      (Forward.treeLaw RRT.allAttach (n + 1)).bind (fun r =>
        TwoSeedCoupling.threeCaseLaw.map (fun c =>
          TaggedHistorySample.longHistory xs.length n ⟨⟨o,r⟩,c⟩)) := by
    apply Measure.bind_congr_right
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only
      rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
      rfl)
  rw [Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, hleft, master_tag_comm]
  rw [Measure.bind_map (measurable_of_countable _).aemeasurable
    measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun c => by
    dsimp only
    have hsuffix := masterTree_caseHistory_law ho.1 ho.2.1 ho.2.2 n c
    have hm := congrArg (fun μ => μ.map
      (FiniteMarkov.History.merge
        (attachFreezeHistory o.history xs.length o.first o.second c))) hsuffix
    rw [Measure.map_map measurable_from_top measurable_from_top] at hm
    simpa [TaggedHistorySample.longHistory, TaggedHistorySample.longPrefixHistory,
      HistorySample.base, attachFreezeHistory, Function.comp_def,
      FiniteMarkov.History.push,
      List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hm)

end FreezingGrowth.TwoSeedGraft
