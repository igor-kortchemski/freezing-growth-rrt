module

public import FreezingGrowth.TwoSeedGraftLong
public import FreezingGrowth.TwoSurvivorTreeLaw
public import FreezingGrowth.RRTSplitLaw
public import FreezingGrowth.FiniteMarkovHistoryConcat

/-! The entire common original prefix, its ordered active pair, and the fresh
master tree. Independence is stated jointly with all old history data. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

noncomputable def prefixHistoryLaw (xs : Word) :
    Measure (FiniteMarkov.History Forward.State) :=
  FiniteMarkov.historyLaw (Measure.dirac Forward.initial)
    (fun j s => Forward.transitionLaw s (j + 1) (xs.toSigns (j + 1))) xs.length

structure OldHistoryData where
  history : FiniteMarkov.History Forward.State
  first : ℕ
  second : ℕ

instance : MeasurableSpace OldHistoryData := ⊤
instance : DiscreteMeasurableSpace OldHistoryData := ⟨fun _ => trivial⟩

structure HistorySample where
  old : OldHistoryData
  master : Forward.State

instance : MeasurableSpace HistorySample := ⊤
instance : DiscreteMeasurableSpace HistorySample := ⟨fun _ => trivial⟩

def HistorySample.base (z : HistorySample) : Sample :=
  ⟨z.old.history.current, z.old.first, z.old.second, z.master⟩

noncomputable def oldHistoryPairLaw (xs : Word) : Measure OldHistoryData :=
  (prefixHistoryLaw xs).bind (fun h =>
    (uniformRootPair h.current.active).map (fun p => ⟨h, p.1, p.2⟩))

noncomputable def historySampleLaw (xs : Word) (n : ℕ) : Measure HistorySample :=
  (oldHistoryPairLaw xs).bind (fun o =>
    (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => ⟨o, r⟩))

def OldHistoryData.treePair (o : OldHistoryData) : Forward.TreePairSample :=
  Forward.treePairSample o.history.current (o.first, o.second)

def HistorySample.baselineHistory (T n : ℕ) (z : HistorySample) :
    FiniteMarkov.History Forward.State :=
  FiniteMarkov.History.merge z.old.history
    (replayHistory z.old.history.current T z.old.first z.old.second z.master.parent n)

def HistorySample.longPrefixHistory (T : ℕ) (z : HistorySample) :
    FiniteMarkov.History Forward.State :=
  (z.old.history.push (Forward.freeze z.old.history.current (T + 1) z.old.second)).push
    (longPrefixState T z.base)

def HistorySample.longHistory (T n : ℕ) (z : HistorySample) :
    FiniteMarkov.History Forward.State :=
  FiniteMarkov.History.merge (z.longPrefixHistory T)
    (replayHistory (longPrefixState T z.base) (T + 2) (T + 2)
      z.old.first z.master.parent n)

theorem runLaw_forward (x : SignSequence) (n : ℕ) :
    FiniteMarkov.runLaw (Measure.dirac Forward.initial)
      (fun j s => Forward.transitionLaw s (j + 1) (x (j + 1))) n =
      Forward.treeLaw x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [FiniteMarkov.runLaw, ih]; rfl

theorem prefixHistoryLaw_current (xs : Word) :
    (prefixHistoryLaw xs).map FiniteMarkov.History.current =
      Forward.treeLaw xs.toSigns xs.length := by
  rw [prefixHistoryLaw, FiniteMarkov.historyLaw_current, runLaw_forward]

/-- Independence from the entire original trajectory and the ordered pair. -/
theorem historySampleLaw_joint (xs : Word) (n : ℕ) :
    (historySampleLaw xs n).map (fun z => (z.old, z.master)) =
      (oldHistoryPairLaw xs).prod (Forward.treeLaw RRT.allAttach (n + 1)) := by
  rw [historySampleLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, Measure.prod_eq_of_sfinite]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun o => by
    dsimp only
    rw [Measure.map_map measurable_from_top measurable_from_top]
    rfl)

theorem historySampleLaw_old (xs : Word) (n : ℕ) :
    (historySampleLaw xs n).map HistorySample.old = oldHistoryPairLaw xs := by
  rw [historySampleLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  calc
    _ = (oldHistoryPairLaw xs).bind Measure.dirac := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun o => by
        dsimp only
        rw [Measure.map_map measurable_from_top measurable_from_top]
        change (Forward.treeLaw RRT.allAttach (n + 1)).map (fun _ => o) = _
        rw [Measure.map_const, measure_univ, one_smul])
    _ = _ := Measure.bind_dirac

theorem oldHistoryPairLaw_history (xs : Word)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (oldHistoryPairLaw xs).map OldHistoryData.history = prefixHistoryLaw xs := by
  have hh : ∀ᵐ h ∂prefixHistoryLaw xs, h.current.active.card = 2 := by
    rw [← prefixHistoryLaw_current xs] at hc
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hc
  rw [oldHistoryPairLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  calc
    _ = (prefixHistoryLaw xs).bind Measure.dirac := by
      apply Measure.bind_congr_right
      filter_upwards [hh] with h hh
      let := uniformRootPair_isProbabilityMeasure h.current.active (by omega)
      rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
      change (uniformRootPair h.current.active).map (fun _ => h) = _
      rw [Measure.map_const, measure_univ, one_smul]
    _ = _ := Measure.bind_dirac

theorem historySampleLaw_history (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (historySampleLaw xs n).map (fun z => z.old.history) = prefixHistoryLaw xs := by
  rw [← oldHistoryPairLaw_history xs hc, ← historySampleLaw_old xs n,
    Measure.map_map measurable_from_top measurable_from_top]
  rfl

theorem historySampleLaw_base (xs : Word) (n : ℕ) :
    (historySampleLaw xs n).map HistorySample.base = sampleLaw xs n := by
  rw [historySampleLaw, oldHistoryPairLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    sampleLaw, ← prefixHistoryLaw_current xs,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => by
    dsimp only
    rw [Measure.bind_map (measurable_of_countable _).aemeasurable
      measurable_from_top.aemeasurable,
      Measure.map_bind (measurable_of_countable _).aemeasurable
        measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    exact Filter.Eventually.of_forall (fun p => by
      dsimp only
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl))

theorem oldHistoryPairLaw_treePair (xs : Word) :
    (oldHistoryPairLaw xs).map OldHistoryData.treePair =
      Forward.treePairLaw xs.toSigns xs.length := by
  rw [oldHistoryPairLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable,
    Forward.treePairLaw, ← prefixHistoryLaw_current xs,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => by
    dsimp only
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    rfl)

/-- The full old tree and ordered vertices are independent of the size and
both complete component States, whose conditional law is the actual RRT law. -/
theorem historySampleLaw_treePair_split (xs : Word) (n : ℕ) :
    (historySampleLaw xs n).map
        (fun z => (z.old.treePair, RRTSplit.firstEdgeSplit n z.master)) =
      (Forward.treePairLaw xs.toSigns xs.length).prod (RRTSplit.mixtureLaw n) := by
  have h := congrArg
    (fun μ => μ.map (Prod.map OldHistoryData.treePair (RRTSplit.firstEdgeSplit n)))
    (historySampleLaw_joint xs n)
  rw [Measure.map_map (by fun_prop) measurable_from_top,
    ← Measure.map_prod_map _ _ measurable_from_top measurable_from_top,
    oldHistoryPairLaw_treePair, RRTSplit.treeLaw_firstEdgeSplit] at h
  exact h

theorem oldHistoryPairLaw_ae_parameters (xs : Word)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ o ∂oldHistoryPairLaw xs,
      Forward.ValidAt xs.length o.history.current ∧
        o.history.current.active = {o.first,o.second} ∧ o.first ≠ o.second := by
  have hv : ∀ᵐ h ∂prefixHistoryLaw xs,
      Forward.ValidAt xs.length h.current ∧ h.current.active.card = 2 := by
    have hv := (Forward.treeLaw_valid xs.toSigns xs.length).and hc
    rw [← prefixHistoryLaw_current xs] at hv
    exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hv
  rw [ae_iff, oldHistoryPairLaw,
    Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [hv] with h hv
  apply ae_iff.mp
  apply (ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete).mpr
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag h.current.active] with p hp
  exact ⟨hv.1, active_eq_pair_of_card_two hv.2 hp, (Finset.mem_offDiag.mp hp).2.2⟩

end FreezingGrowth.TwoSeedGraft
