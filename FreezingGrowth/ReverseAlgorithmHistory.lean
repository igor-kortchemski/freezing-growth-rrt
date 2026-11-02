module

public import FreezingGrowth.ReverseDelayedLongerLaw
public import FreezingGrowth.FiniteMarkovHistoryConcat

/-! Full finite histories of the actual ordered and graph-valued Algorithm 2.
Their horizon hold agrees exactly with the existing finite-phase laws. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

noncomputable def orderedStepAfter (x : SignSequence) (n t : ℕ) (F : Forest) : Measure Forest :=
  if t < n then transitionLaw x (n - (t + 1)) F else Measure.dirac F

noncomputable def graphStepAfter (x : SignSequence) (n t : ℕ) (F : Reverse.Forest) :
    Measure Reverse.Forest :=
  if t < n then Reverse.transitionLaw x (n - (t + 1)) F else Measure.dirac F

theorem runLaw_orderedStepAfter (x : SignSequence) (n t : ℕ) :
    FiniteMarkov.runLaw (Measure.dirac (initial x n)) (orderedStepAfter x n) t =
      lawAfter x n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [FiniteMarkov.runLaw, ih, lawAfter]
    by_cases ht : t < n
    · have he : orderedStepAfter x n t = transitionLaw x (n - (t + 1)) := by
        funext F
        exact ite_eq_left ht
      rw [he, ite_eq_left ht]
    · have he : orderedStepAfter x n t = Measure.dirac := by
        funext F
        exact ite_eq_right ht
      rw [he, ite_eq_right ht, Measure.bind_dirac]

theorem runLaw_graphStepAfter (x : SignSequence) (n t : ℕ) :
    FiniteMarkov.runLaw (Measure.dirac (Reverse.initial x n)) (graphStepAfter x n) t =
      Reverse.lawAfter x n t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [FiniteMarkov.runLaw, ih, Reverse.lawAfter]
    by_cases ht : t < n
    · have he : graphStepAfter x n t = Reverse.transitionLaw x (n - (t + 1)) := by
        funext F
        exact ite_eq_left ht
      rw [he, ite_eq_left ht]
    · have he : graphStepAfter x n t = Measure.dirac := by
        funext F
        exact ite_eq_right ht
      rw [he, ite_eq_right ht, Measure.bind_dirac]

noncomputable def orderedHistoryLaw (x : SignSequence) (n t : ℕ) :
    Measure (FiniteMarkov.History Forest) :=
  FiniteMarkov.historyLaw (Measure.dirac (initial x n)) (orderedStepAfter x n) t

noncomputable def graphHistoryLaw (x : SignSequence) (n t : ℕ) :
    Measure (FiniteMarkov.History Reverse.Forest) :=
  FiniteMarkov.historyLaw (Measure.dirac (Reverse.initial x n)) (graphStepAfter x n) t

theorem orderedHistoryLaw_current (x : SignSequence) (n t : ℕ) :
    (orderedHistoryLaw x n t).map FiniteMarkov.History.current = lawAfter x n t := by
  rw [orderedHistoryLaw, FiniteMarkov.historyLaw_current, runLaw_orderedStepAfter]

theorem graphHistoryLaw_current (x : SignSequence) (n t : ℕ) :
    (graphHistoryLaw x n t).map FiniteMarkov.History.current = Reverse.lawAfter x n t := by
  rw [graphHistoryLaw, FiniteMarkov.historyLaw_current, runLaw_graphStepAfter]

theorem map_orderedStepAfter (x : SignSequence) (n t : ℕ) (F : Forest) :
    (orderedStepAfter x n t F).map Forest.forest = graphStepAfter x n t F.forest := by
  by_cases ht : t < n
  · simp only [orderedStepAfter, graphStepAfter, ite_eq_left ht]
    exact map_transitionLaw x _ F
  · simp only [orderedStepAfter, graphStepAfter, ite_eq_right ht]
    exact Measure.map_dirac' measurable_from_top _

/-- The whole ordered Algorithm 2 history projects to its full labelled
graph history, not only to individual phases. -/
theorem orderedHistoryLaw_graph (x : SignSequence) (n t : ℕ) :
    (orderedHistoryLaw x n t).map (FiniteMarkov.History.map Forest.forest) =
      graphHistoryLaw x n t := by
  have hh := FiniteMarkov.map_historyLaw (Measure.dirac (initial x n))
    (orderedStepAfter x n) (graphStepAfter x n) Forest.forest t
    (fun j _ => Filter.Eventually.of_forall (map_orderedStepAfter x n j))
  have hinit : (Measure.dirac (initial x n)).map Forest.forest =
      Measure.dirac (Reverse.initial x n) := Measure.map_dirac' measurable_from_top _
  rw [hinit] at hh
  exact hh

/-- Source-tail histories retain the actual incoming ordered forest and its past. -/
theorem sourceTailHistory_parameters (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ h ∂orderedHistoryLaw (Word.toSigns (List.replicate k true ++ [false] ++ tail))
      (List.replicate k true ++ [false] ++ tail).length tail.length,
      Sum.inr k ∉ h.current.forest.vertices ∧ h.current.forest.roots.card = k := by
  have hh := initializationTailLaw_parameters k tail ha
  change ∀ᵐ F ∂lawAfter _ _ _, _ at hh
  rw [← orderedHistoryLaw_current] at hh
  exact (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mp hh

end FreezingGrowth.ReverseOrdered
