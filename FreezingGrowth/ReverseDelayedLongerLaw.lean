module

public import FreezingGrowth.ReverseDelayedDynamics
public import FreezingGrowth.ReverseHeightDynamics
public import FreezingGrowth.FiniteMarkovHistory

/-! Exact projected transitions and whole finite longer-forest histories.
The delayed pair's law relative to the shorter history is not assumed here. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

def longerForest (z : InitializationSample) : Reverse.Forest := z.longer.forest

theorem joinPositions_graphLaw (F : Forest) (hF : 2 ≤ F.forest.roots.card) :
    (uniformRootPair (Finset.range F.forest.roots.card)).map
      (fun p => (joinPositions F p).forest) = F.forest.joinLaw := by
  rw [← ReverseHeightList.map_uniformRootPair_finPairValues F.forest.roots.card,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  calc
    _ = (uniformRootPair (Finset.univ : Finset (Fin F.forest.roots.card))).map
        (fun p => F.forest.joinChoice (F.forest.indexedPair (rootEnumeration F) p)) := by
      apply Measure.map_congr
      filter_upwards [ReverseHeightList.uniformFinPair_ae_distinct F.forest.roots.card] with p hp
      change (joinPositions F (p.1.val, p.2.val)).forest = _
      rw [joinPositions_fin F p hp, joinChoice_forest]
    _ = _ := by
      simpa only [RootedForest.indexedJoinLaw, ite_eq_left hF] using
        F.forest.indexedJoinLaw_eq_joinLaw (rootEnumeration F)

theorem synchronizedLaw_longer {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) :
    (synchronizedLaw z).map longerForest = z.longer.forest.joinLaw := by
  rw [synchronizedLaw, Measure.map_map measurable_from_top (measurable_of_countable _)]
  change (uniformRootPair (Finset.range z.shorter.forest.roots.card)).map
    (fun p => (joinPositions z.longer p).forest) = _
  rw [hz.shorter_card, ← hz.longer_card]
  exact joinPositions_graphLaw z.longer (by simpa only [hz.longer_card] using hN)

/-- The neighbouring-phase delayed match of source C6: the shorter forest
first consumes the old stored pair, deterministically. -/
theorem delayedTransition_pending_shorter {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) (hu : z.used = false) :
    (delayedTransition i z).map InitializationSample.shorter = Measure.dirac (consumeDelayed z) := by
  rw [delayedTransition_pending_eq hz hN hu, pendingDirectLaw_eq_initialization hz hu]
  have hc := hz.consume_card hu
  exact initializationLaw_shorter (consumeDelayed z) hz.consume_fresh (by omega)

/-- Source C6 at each actual nonterminal phase: in the pending case, the
neighbouring shorter forest is exactly the longer forest with its isolated
distinguished head removed, through the explicit consumed-pair construction. -/
theorem sourceDelayedLaw_pending_shorter (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail))
    (t : ℕ) (ht : t < k - 1) :
    ∀ᵐ z ∂sourceDelayedLaw k tail t, z.used = false →
      z.longer = prependLabel (consumeDelayed z) k ∧
      (delayedTransition k z).map InitializationSample.shorter =
        Measure.dirac (consumeDelayed z) := by
  filter_upwards [sourceDelayedLaw_ae_valid k tail ha t ht.le] with z hz
  intro hu
  obtain ⟨_, _, _, _, _, hmatch⟩ := hz.pending hu
  exact ⟨hmatch, delayedTransition_pending_shorter hz (by omega) hu⟩

/-- Conditional on the full current joint state, the first forest has exactly
the ordinary Algorithm 2 graph transition. This is stronger than a one-time marginal. -/
theorem delayedTransition_longer {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) :
    (delayedTransition i z).map longerForest = z.longer.forest.joinLaw := by
  cases hu : z.used with
  | false =>
    rw [delayedTransition_pending_eq hz hN hu, pendingDirectLaw_eq_initialization hz hu]
    have hc := hz.consume_card hu
    have hh := initializationLaw_longer_forest (consumeDelayed z) hz.consume_fresh (by omega)
    obtain ⟨_, _, _, _, _, hmatch⟩ := hz.pending hu
    change (initializationLaw (consumeDelayed z) i).map (fun z => z.longer.forest) = _
    rw [hh, hmatch, prependLabel_forest]
  | true =>
    rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN), hu]
    simp only [↓reduceIte]
    exact synchronizedLaw_longer hz hN

theorem finiteRunLaw_delayed (F : Forest) (i t : ℕ) :
    FiniteMarkov.runLaw (initializationLaw F i) (fun _ => delayedTransition i) t =
      delayedLawAfter F i t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [FiniteMarkov.runLaw, delayedLawAfter, ih]

noncomputable def delayedHistoryLaw (F : Forest) (i t : ℕ) :
    Measure (FiniteMarkov.History InitializationSample) :=
  FiniteMarkov.historyLaw (initializationLaw F i) (fun _ => delayedTransition i) t

/-- The entire first-forest history after initialization has the ordinary
coalescent law, including all dependence between its consecutive states. -/
theorem delayedHistoryLaw_longer (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card)
    (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    (delayedHistoryLaw F i t).map (FiniteMarkov.History.map longerForest) =
      FiniteMarkov.historyLaw ((Reverse.insertLabel F.forest i).joinLaw)
        (fun _ G => G.joinLaw) t := by
  have hh := FiniteMarkov.map_historyLaw (initializationLaw F i)
    (fun _ => delayedTransition i) (fun _ (G : Reverse.Forest) => G.joinLaw) longerForest t
    (by
      intro j hj
      rw [finiteRunLaw_delayed]
      filter_upwards [delayedLawAfter_ae_valid F hi j (by omega)] with z hz
      exact delayedTransition_longer hz (by omega))
  have hinit : (initializationLaw F i).map longerForest =
      (Reverse.insertLabel F.forest i).joinLaw := initializationLaw_longer_forest F hi hF
  rw [hinit] at hh
  exact hh

end FreezingGrowth.ReverseOrdered
