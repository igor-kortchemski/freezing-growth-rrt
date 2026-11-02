module

public import FreezingGrowth.TwoSeedGraftHistory
public import FreezingGrowth.TwoSeedGraftWord

/-! Prefix laws for replaying an initial segment of a larger actual master RRT.
The next master attachment changes only its own parent coordinate, which the
shorter replay and replay history do not inspect. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

theorem masterTree_replay_prefix_succ (s : Forward.State) (T u v n m : ℕ)
    (hm : n + 1 ≤ m) :
    (Forward.treeLaw RRT.allAttach (m + 1)).map
        (fun r => replay s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach m).map
        (fun r => replay s T u v r.parent n) := by
  change ((Forward.treeLaw RRT.allAttach m).bind
      (fun r => Forward.transitionLaw r (m + 1) true)).map
        (fun r => replay s T u v r.parent n) = _
  rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = (Forward.treeLaw RRT.allAttach m).bind (fun r =>
        Measure.dirac (replay s T u v r.parent n)) := by
      apply Measure.bind_congr_right
      apply Filter.Eventually.of_forall
      intro r
      have hp : ∀ᵐ q ∂Forward.transitionLaw r (m + 1) true,
          replay s T u v q.parent n = replay s T u v r.parent n := by
        apply Forward.transitionLaw_ae
        · intro _
          rfl
        · intro a ha
          simp only [Forward.step, ite_eq_left ha, ↓reduceIte]
          apply replay_congr
          intro j hj hj'
          exact Function.update_of_ne (by omega) _ _
      calc
        (Forward.transitionLaw r (m + 1) true).map
            (fun q => replay s T u v q.parent n) =
          (Forward.transitionLaw r (m + 1) true).map
            (fun _ => replay s T u v r.parent n) := Measure.map_congr hp
        _ = Measure.dirac (replay s T u v r.parent n) := by simp
    _ = (Forward.treeLaw RRT.allAttach m).map
        (fun r => replay s T u v r.parent n) :=
          Measure.bind_dirac_eq_map _ measurable_from_top

theorem masterTree_replayHistory_prefix_succ (s : Forward.State) (T u v n m : ℕ)
    (hm : n + 1 ≤ m) :
    (Forward.treeLaw RRT.allAttach (m + 1)).map
        (fun r => replayHistory s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach m).map
        (fun r => replayHistory s T u v r.parent n) := by
  change ((Forward.treeLaw RRT.allAttach m).bind
      (fun r => Forward.transitionLaw r (m + 1) true)).map
        (fun r => replayHistory s T u v r.parent n) = _
  rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = (Forward.treeLaw RRT.allAttach m).bind (fun r =>
        Measure.dirac (replayHistory s T u v r.parent n)) := by
      apply Measure.bind_congr_right
      apply Filter.Eventually.of_forall
      intro r
      have hp : ∀ᵐ q ∂Forward.transitionLaw r (m + 1) true,
          replayHistory s T u v q.parent n = replayHistory s T u v r.parent n := by
        apply Forward.transitionLaw_ae
        · intro _
          rfl
        · intro a ha
          simp only [Forward.step, ite_eq_left ha, ↓reduceIte]
          apply replayHistory_congr
          intro j hj hj'
          exact Function.update_of_ne (by omega) _ _
      calc
        (Forward.transitionLaw r (m + 1) true).map
            (fun q => replayHistory s T u v q.parent n) =
          (Forward.transitionLaw r (m + 1) true).map
            (fun _ => replayHistory s T u v r.parent n) := Measure.map_congr hp
        _ = Measure.dirac (replayHistory s T u v r.parent n) := by simp
    _ = (Forward.treeLaw RRT.allAttach m).map
        (fun r => replayHistory s T u v r.parent n) :=
          Measure.bind_dirac_eq_map _ measurable_from_top

theorem masterTree_replay_prefix_law (s : Forward.State) (T u v n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 2)).map
        (fun r => replay s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => replay s T u v r.parent n) := by
  simpa using masterTree_replay_prefix_succ s T u v n (n + 1) (by omega)

theorem masterTree_replayHistory_prefix_law (s : Forward.State) (T u v n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 2)).map
        (fun r => replayHistory s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => replayHistory s T u v r.parent n) := by
  simpa using masterTree_replayHistory_prefix_succ s T u v n (n + 1) (by omega)

theorem masterTree_replay_prefix_of_le (s : Forward.State) (T u v n m : ℕ)
    (hm : n + 1 ≤ m) :
    (Forward.treeLaw RRT.allAttach m).map
        (fun r => replay s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => replay s T u v r.parent n) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hnm : n = m
    · subst m
      rfl
    · have hle : n + 1 ≤ m := by omega
      calc
        (Forward.treeLaw RRT.allAttach (m + 1)).map
            (fun r => replay s T u v r.parent n) =
          (Forward.treeLaw RRT.allAttach m).map
            (fun r => replay s T u v r.parent n) :=
              masterTree_replay_prefix_succ s T u v n m hle
        _ = (Forward.treeLaw RRT.allAttach (n + 1)).map
              (fun r => replay s T u v r.parent n) := ih hle

theorem masterTree_replayHistory_prefix_of_le (s : Forward.State) (T u v n m : ℕ)
    (hm : n + 1 ≤ m) :
    (Forward.treeLaw RRT.allAttach m).map
        (fun r => replayHistory s T u v r.parent n) =
      (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => replayHistory s T u v r.parent n) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hnm : n = m
    · subst m
      rfl
    · have hle : n + 1 ≤ m := by omega
      calc
        (Forward.treeLaw RRT.allAttach (m + 1)).map
            (fun r => replayHistory s T u v r.parent n) =
          (Forward.treeLaw RRT.allAttach m).map
            (fun r => replayHistory s T u v r.parent n) :=
              masterTree_replayHistory_prefix_succ s T u v n m hle
        _ = (Forward.treeLaw RRT.allAttach (n + 1)).map
              (fun r => replayHistory s T u v r.parent n) := ih hle

theorem word_two_seed_master_law_of_le (xs : Word) (n m : ℕ)
    (u v : Forward.State → ℕ)
    (hseed : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length,
      s.active = {u s, v s} ∧ u s ≠ v s)
    (hm : n + 1 ≤ m) :
    Forward.treeLaw (xs ++ List.replicate n true).toSigns
        (xs ++ List.replicate n true).length =
      (Forward.treeLaw xs.toSigns xs.length).bind (fun s =>
        (Forward.treeLaw RRT.allAttach m).map
          (fun r => replay s xs.length (u s) (v s) r.parent n)) := by
  rw [word_two_seed_master_law xs n u v hseed]
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro s
  exact (masterTree_replay_prefix_of_le s xs.length (u s) (v s) n m hm).symm

end FreezingGrowth.TwoSeedGraft
