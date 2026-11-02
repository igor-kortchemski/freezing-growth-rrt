module

public import FreezingGrowth.TwoSeedGraftLaw
public import FreezingGrowth.FiniteMarkovHistory

/-! One actual master parent array couples every prefix of the full-state
two-seed attachment process, including all dependence between its stages. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

def replayHistory (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ) : ℕ → FiniteMarkov.History Forward.State
  | 0 => FiniteMarkov.History.start s
  | n + 1 => (replayHistory s T u v p n).push (replay s T u v p (n + 1))

theorem replayHistory_current (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ) (n : ℕ) :
    (replayHistory s T u v p n).current = replay s T u v p n := by
  cases n <;> rfl

theorem replayHistory_congr (s : Forward.State) (T u v n : ℕ) {p q : ℕ → ℕ}
    (hpq : ∀ j, 2 ≤ j → j ≤ n + 1 → p j = q j) :
    replayHistory s T u v p n = replayHistory s T u v q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replayHistory, replayHistory, ih (fun j hj hj' => hpq j hj (by omega)),
      replay_congr s T u v (n + 1) hpq]

theorem replayHistory_attach (s r : Forward.State) (T u v n a : ℕ) :
    replayHistory s T u v (Forward.attach r (n + 2) a).parent (n + 1) =
      (replayHistory s T u v r.parent n).push
        (Forward.attach (replay s T u v r.parent n) (T + n + 1) (embedding T u v a)) := by
  have hpre : replayHistory s T u v (Forward.attach r (n + 2) a).parent n =
      replayHistory s T u v r.parent n := by
    apply replayHistory_congr
    intro j _ hj
    exact Function.update_of_ne (by omega) _ _
  rw [replayHistory, hpre, replay_attach]

theorem map_transition_replayHistory (s r : Forward.State) {T u v n : ℕ}
    (hu : u ≤ T) (hv : v ≤ T) (huv : u ≠ v) (hs : s.active = {u, v})
    (hr : r.active = Finset.range (n + 2)) :
    (Forward.transitionLaw r (n + 2) true).map
        (fun q => replayHistory s T u v q.parent (n + 1)) =
      (Forward.transitionLaw (replay s T u v r.parent n) (T + n + 1) true).map
        (fun q => (replayHistory s T u v r.parent n).push q) := by
  have hrne : r.active.Nonempty := by rw [hr]; exact ⟨0, by simp⟩
  have hp : ∀ᵐ q ∂Forward.transitionLaw r (n + 2) true,
      replayHistory s T u v q.parent (n + 1) =
        (replayHistory s T u v r.parent n).push (replay s T u v q.parent (n + 1)) := by
    apply Forward.transitionLaw_ae
    · intro he
      exact False.elim (hrne.ne_empty he)
    · intro a ha
      simp only [Forward.step, ite_eq_left ha, ↓reduceIte]
      rw [replayHistory_attach, replay_attach]
  have he : (Forward.transitionLaw r (n + 2) true).map
      (fun q => replayHistory s T u v q.parent (n + 1)) =
      ((Forward.transitionLaw r (n + 2) true).map
        (fun q => replay s T u v q.parent (n + 1))).map
          (fun q => (replayHistory s T u v r.parent n).push q) := by
    rw [Measure.map_map measurable_from_top measurable_from_top]
    exact Measure.map_congr hp
  rw [he, map_transition_replay s r hu hv huv hs hr]

/-- The actual master law realizes the entire attachment history. -/
theorem masterTree_replayHistory_law (s : Forward.State) {T u v : ℕ}
    (hu : u ≤ T) (hv : v ≤ T) (huv : u ≠ v) (hs : s.active = {u, v}) (n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => replayHistory s T u v r.parent n) =
      FiniteMarkov.historyLaw (Measure.dirac s)
        (fun j q => Forward.transitionLaw q (T + j + 1) true) n := by
  induction n with
  | zero =>
    rw [RRTSplit.treeLaw_one, Measure.map_dirac' measurable_from_top,
      FiniteMarkov.historyLaw, Measure.map_dirac' measurable_from_top]
    rfl
  | succ n ih =>
    change ((Forward.treeLaw RRT.allAttach (n + 1)).bind
      (fun r => Forward.transitionLaw r (n + 2) true)).map
        (fun r => replayHistory s T u v r.parent (n + 1)) = _
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      FiniteMarkov.historyLaw]
    calc
      _ = (Forward.treeLaw RRT.allAttach (n + 1)).bind (fun r =>
          (Forward.transitionLaw (replay s T u v r.parent n) (T + n + 1) true).map
            (fun q => (replayHistory s T u v r.parent n).push q)) := by
        apply Measure.bind_congr_right
        filter_upwards [RRTSplit.treeLaw_split_describes n] with r hr
        exact map_transition_replayHistory s r hu hv huv hs hr.active
      _ = ((Forward.treeLaw RRT.allAttach (n + 1)).map
          (fun r => replayHistory s T u v r.parent n)).bind (fun h =>
            (Forward.transitionLaw h.current (T + n + 1) true).map (fun q => h.push q)) := by
        have hh := (Measure.bind_map (m := Forward.treeLaw RRT.allAttach (n + 1))
          (f := fun r => replayHistory s T u v r.parent n)
          (g := fun h => (Forward.transitionLaw h.current (T + n + 1) true).map (fun q => h.push q))
          measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
        simpa only [replayHistory_current] using hh
      _ = _ := by rw [ih]

end FreezingGrowth.TwoSeedGraft
