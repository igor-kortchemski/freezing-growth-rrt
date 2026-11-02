module

public import FreezingGrowth.ReverseAlgorithmHistory

/-! The whole first-process history in Algorithm 3, including its actual
common tail and both initialization stages, has Algorithm 2's labelled-graph law. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical

def reversePeakWord (k : ℕ) (tail : Word) : Word :=
  List.replicate k true ++ [false] ++ tail

theorem reversePeakWord_length (k : ℕ) (tail : Word) :
    (reversePeakWord k tail).length = k + 1 + tail.length := by
  simp only [reversePeakWord, List.length_append, List.length_replicate, List.length_singleton]

theorem reversePeakWord_freeze (k : ℕ) (tail : Word) :
    (reversePeakWord k tail).toSigns (k + 1) = false := by
  simp [reversePeakWord, List.append_assoc, Word.toSigns_succ]

theorem reversePeakWord_attach (k : ℕ) (tail : Word) {j : ℕ} (hj : j < k) :
    (reversePeakWord k tail).toSigns (j + 1) = true := by
  change Word.toSigns ((List.replicate k true ++ [false]) ++ tail) (j + 1) = true
  rw [List.append_assoc, Word.toSigns_append_left (List.replicate k true) ([false] ++ tail)
    (by simpa using hj)]
  simp [Word.toSigns_succ, List.getElem?_replicate_of_lt hj]

theorem graphStepAfter_source_freeze (k : ℕ) (tail : Word) (F : Reverse.Forest) :
    graphStepAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
      tail.length F = Measure.dirac (Reverse.insertLabel F k) := by
  have hlt : tail.length < (reversePeakWord k tail).length := by
    rw [reversePeakWord_length]
    omega
  have hi : (reversePeakWord k tail).length - (tail.length + 1) = k := by
    rw [reversePeakWord_length]
    omega
  rw [graphStepAfter, ite_eq_left hlt, hi, Reverse.transitionLaw, reversePeakWord_freeze]
  simp

theorem graphStepAfter_source_join (k : ℕ) (tail : Word) {j : ℕ} (hj : j < k)
    (F : Reverse.Forest) :
    graphStepAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
      (tail.length + 1 + j) F = F.joinLaw := by
  have hlt : tail.length + 1 + j < (reversePeakWord k tail).length := by
    rw [reversePeakWord_length]
    omega
  have hi : (reversePeakWord k tail).length - (tail.length + 1 + j + 1) = k - (j + 1) := by
    rw [reversePeakWord_length]
    omega
  rw [graphStepAfter, ite_eq_left hlt, hi, Reverse.transitionLaw,
    reversePeakWord_attach k tail (by omega : k - (j + 1) < k)]
  simp

def withInitializationPast (F : Forest) (i : ℕ)
    (h : FiniteMarkov.History InitializationSample) : FiniteMarkov.History Reverse.Forest :=
  (FiniteMarkov.History.map longerForest h).appendPast
    [Reverse.insertLabel F.forest i, F.forest]

/-- The complete conditional prefix history, with the pre-freeze and
pre-graft states explicitly retained. -/
theorem delayedHistoryLaw_with_initialization (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (F : Forest) (hi : Sum.inr k ∉ F.forest.vertices) (hF : F.forest.roots.card = k) :
    FiniteMarkov.historyLaw (Measure.dirac F.forest)
        (fun j => graphStepAfter (reversePeakWord k tail).toSigns
          (reversePeakWord k tail).length (tail.length + j)) (k + 1) =
      (delayedHistoryLaw F k (k - 1)).map (withInitializationPast F k) := by
  let K : ℕ → Reverse.Forest → Measure Reverse.Forest := fun j =>
    graphStepAfter (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
      (tail.length + j)
  have hfirst : K 0 F.forest = Measure.dirac (Reverse.insertLabel F.forest k) := by
    simpa only [K, Nat.add_zero] using graphStepAfter_source_freeze k tail F.forest
  have hrest : FiniteMarkov.historyLaw (Measure.dirac (Reverse.insertLabel F.forest k))
      (fun j => K (j + 1)) k =
      FiniteMarkov.historyLaw (Measure.dirac (Reverse.insertLabel F.forest k))
        (fun _ G => G.joinLaw) k := by
    apply FiniteMarkov.historyLaw_congr
    intro j hj G
    simpa only [K, Nat.add_assoc, Nat.add_comm 1 j] using
      graphStepAfter_source_join k tail hj G
  have hh := FiniteMarkov.historyLaw_dirac_succ F.forest K k
  rw [hfirst, hrest] at hh
  have hk' : k = k - 1 + 1 := by omega
  have hnext := FiniteMarkov.historyLaw_dirac_succ (Reverse.insertLabel F.forest k)
    (fun _ (G : Reverse.Forest) => G.joinLaw) (k - 1)
  rw [← hk'] at hnext
  rw [hnext] at hh
  have hproject := delayedHistoryLaw_longer F hi (by omega) (k - 1)
    (by simpa only [hF] using (le_rfl : k - 1 ≤ k - 1))
  rw [← hproject] at hh
  rw [Measure.map_map measurable_from_top measurable_from_top,
    Measure.map_map measurable_from_top measurable_from_top] at hh
  calc
    _ = _ := hh
    _ = _ := by
      congr 1
      funext h
      cases h
      simp [withInitializationPast, FiniteMarkov.History.map,
        FiniteMarkov.History.appendPast, Function.comp_def, List.append_assoc]

def extendSourceLongerHistory (k : ℕ) (tailHistory : FiniteMarkov.History Forest)
    (h : FiniteMarkov.History InitializationSample) : FiniteMarkov.History Reverse.Forest :=
  (FiniteMarkov.History.map longerForest h).appendPast
    (Reverse.insertLabel tailHistory.current.forest k :: tailHistory.current.forest ::
      tailHistory.past.map Forest.forest)

/-- Sample the actual common-tail history first, then the fresh initialization
and delayed choices conditionally on its current ordered forest. -/
noncomputable def sourceLongerHistoryLaw (k : ℕ) (tail : Word) :
    Measure (FiniteMarkov.History Reverse.Forest) :=
  (orderedHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
    tail.length).bind (fun h =>
      (delayedHistoryLaw h.current k (k - 1)).map (extendSourceLongerHistory k h))

/-- Source C4: the entire first forest sequence, with all dependencies between
phases and the actual common tail, has Algorithm 2's full labelled-graph law. -/
theorem sourceLongerHistoryLaw_eq (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : (reversePeakWord k tail).admissible) :
    sourceLongerHistoryLaw k tail =
      graphHistoryLaw (reversePeakWord k tail).toSigns (reversePeakWord k tail).length
        (reversePeakWord k tail).length := by
  let x := (reversePeakWord k tail).toSigns
  let n := (reversePeakWord k tail).length
  have hn : n = tail.length + (k + 1) := by
    dsimp [n]
    rw [reversePeakWord_length]
    omega
  have hsplit : graphHistoryLaw x n n =
      (graphHistoryLaw x n tail.length).bind (fun h =>
        (FiniteMarkov.historyLaw (Measure.dirac h.current)
          (fun j => graphStepAfter x n (tail.length + j)) (k + 1)).map
            (FiniteMarkov.History.merge h)) := by
    change FiniteMarkov.historyLaw _ _ n = _
    conv_lhs => arg 3; rw [hn]
    exact FiniteMarkov.historyLaw_add (Measure.dirac (Reverse.initial x n))
      (graphStepAfter x n) tail.length (k + 1)
  rw [hsplit, ← orderedHistoryLaw_graph x n tail.length,
    Measure.bind_map (m := orderedHistoryLaw x n tail.length)
      (f := FiniteMarkov.History.map Forest.forest)
      (g := fun h : FiniteMarkov.History Reverse.Forest =>
        (FiniteMarkov.historyLaw (Measure.dirac h.current)
          (fun j => graphStepAfter x n (tail.length + j)) (k + 1)).map
            (FiniteMarkov.History.merge h))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  unfold sourceLongerHistoryLaw
  apply Measure.bind_congr_right
  filter_upwards [sourceTailHistory_parameters k tail ha] with h hF
  change (delayedHistoryLaw h.current k (k - 1)).map (extendSourceLongerHistory k h) =
    (FiniteMarkov.historyLaw (Measure.dirac h.current.forest)
      (fun j => graphStepAfter x n (tail.length + j)) (k + 1)).map
      (FiniteMarkov.History.merge (FiniteMarkov.History.map Forest.forest h))
  dsimp only [x, n]
  rw [delayedHistoryLaw_with_initialization k hk tail h.current hF.1 hF.2,
    Measure.map_map measurable_from_top measurable_from_top]
  congr 1
  funext g
  cases h
  cases g
  simp [extendSourceLongerHistory, withInitializationPast, FiniteMarkov.History.map,
    FiniteMarkov.History.merge, FiniteMarkov.History.appendPast,
    List.append_assoc]

end FreezingGrowth.ReverseOrdered
