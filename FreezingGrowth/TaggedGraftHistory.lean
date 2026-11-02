module

public import FreezingGrowth.TwoSeedGraftLongHistory
public import FreezingGrowth.TaggedGraftSource

/-! The tagged graft retains the literal whole original prefix and both
intermediate attachment/freezing states, in addition to the shared master. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

structure TaggedHistorySample where
  base : HistorySample
  tag : Fin 3

instance : MeasurableSpace TaggedHistorySample := ⊤
instance : DiscreteMeasurableSpace TaggedHistorySample := ⟨fun _ => trivial⟩

noncomputable def taggedHistoryLaw (xs : Word) (n : ℕ) : Measure TaggedHistorySample :=
  (historySampleLaw xs n).bind (fun z =>
    TwoSeedCoupling.threeCaseLaw.map (fun c => ⟨z,c⟩))

def TaggedHistorySample.toTaggedSample (z : TaggedHistorySample) : TaggedSample :=
  ⟨z.base.base,z.tag⟩

def TaggedHistorySample.longPrefixHistory (T : ℕ) (z : TaggedHistorySample) :
    FiniteMarkov.History Forward.State :=
  (z.base.old.history.push
    (Forward.attach z.base.old.history.current (T + 1) z.base.old.first)).push
      (casePrefix z.base.old.history.current T z.base.old.first z.base.old.second z.tag)

def TaggedHistorySample.longHistory (T n : ℕ) (z : TaggedHistorySample) :
    FiniteMarkov.History Forward.State :=
  FiniteMarkov.History.merge (z.longPrefixHistory T) (caseHistory T n z.tag z.base.base)

/-- The uniform tag is independent of the whole old trajectory, ordered pair,
and actual master tree, together. -/
theorem taggedHistoryLaw_joint (xs : Word) (n : ℕ) :
    (taggedHistoryLaw xs n).map (fun z => (z.base, z.tag)) =
      (historySampleLaw xs n).prod TwoSeedCoupling.threeCaseLaw := by
  rw [taggedHistoryLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, Measure.prod_eq_of_sfinite]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    rfl)

theorem taggedHistoryLaw_base (xs : Word) (n : ℕ) :
    (taggedHistoryLaw xs n).map TaggedHistorySample.base = historySampleLaw xs n := by
  rw [taggedHistoryLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  calc
    _ = (historySampleLaw xs n).bind Measure.dirac := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only
        rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
        change TwoSeedCoupling.threeCaseLaw.map (fun _ => z) = _
        rw [Measure.map_const, measure_univ, one_smul])
    _ = _ := Measure.bind_dirac

theorem taggedHistoryLaw_toTaggedSample (xs : Word) (n : ℕ) :
    (taggedHistoryLaw xs n).map TaggedHistorySample.toTaggedSample = taggedSampleLaw xs n := by
  rw [taggedHistoryLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, taggedSampleLaw, taggedLaw,
    ← historySampleLaw_base xs n,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    rfl)

theorem taggedHistoryLaw_history (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (taggedHistoryLaw xs n).map (fun z => z.base.old.history) = prefixHistoryLaw xs := by
  rw [← historySampleLaw_history xs n hc, ← taggedHistoryLaw_base xs n,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

theorem taggedHistoryLaw_baselineHistory (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (taggedHistoryLaw xs n).map (fun z => z.base.baselineHistory xs.length n) =
      prefixHistoryLaw (xs ++ List.replicate n true) := by
  rw [← historySampleLaw_baselineHistory xs n hc, ← taggedHistoryLaw_base xs n,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

end FreezingGrowth.TwoSeedGraft
