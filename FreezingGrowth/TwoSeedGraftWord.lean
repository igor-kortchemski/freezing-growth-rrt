module

public import FreezingGrowth.TwoSeedGraftLaw
public import FreezingGrowth.FirstPeakDeletion
public import FreezingGrowth.FiniteLaw

/-! The master graft's continuation law is the actual appended-word law. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

theorem treeLaw_bind_continuation (x : SignSequence) (T n : ℕ)
    (hx : ∀ j < n, x (T + j + 1) = true) :
    Forward.treeLaw x (T + n) =
      (Forward.treeLaw x T).bind (fun s => continuationLaw s T n) := by
  induction n with
  | zero => simp only [Nat.add_zero, continuationLaw, Measure.bind_dirac]
  | succ n ih =>
    rw [Nat.add_succ, Forward.treeLaw, hx n (by omega),
      ih (fun j hj => hx j (by omega))]
    change ((Forward.treeLaw x T).bind (fun s => continuationLaw s T n)).bind
        (fun q => Forward.transitionLaw q (T + n + 1) true) =
      (Forward.treeLaw x T).bind (fun s => (continuationLaw s T n).bind
        (fun q => Forward.transitionLaw q (T + n + 1) true))
    exact Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable

theorem word_bind_continuation (xs : Word) (n : ℕ) :
    Forward.treeLaw (xs ++ List.replicate n true).toSigns (xs ++ List.replicate n true).length =
      (Forward.treeLaw xs.toSigns xs.length).bind (fun s => continuationLaw s xs.length n) := by
  have hx : ∀ j < n, (xs ++ List.replicate n true).toSigns (xs.length + j + 1) = true := by
    intro j hj
    rw [Word.toSigns_append_right]
    simp only [Word.toSigns_succ, List.getElem?_replicate_of_lt hj, Option.getD_some]
  rw [List.length_append, List.length_replicate, treeLaw_bind_continuation _ _ _ hx]
  have hp : Forward.treeLaw (xs ++ List.replicate n true).toSigns xs.length =
      Forward.treeLaw xs.toSigns xs.length :=
    Forward.treeLaw_congr (fun i hi => Word.toSigns_append_left xs _ hi)
  rw [hp]

/-- A fresh master RRT has the full appended-word tree law, with the actual
birth identifiers and the old frozen data retained. -/
theorem word_two_seed_master_law (xs : Word) (n : ℕ) (u v : Forward.State → ℕ)
    (hseed : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length,
      s.active = {u s, v s} ∧ u s ≠ v s) :
    Forward.treeLaw (xs ++ List.replicate n true).toSigns (xs ++ List.replicate n true).length =
      (Forward.treeLaw xs.toSigns xs.length).bind (fun s =>
        (Forward.treeLaw RRT.allAttach (n + 1)).map
          (fun r => replay s xs.length (u s) (v s) r.parent n)) := by
  rw [word_bind_continuation]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length, hseed] with s hs hseed
  have hu : u s ∈ s.active := by rw [hseed.1]; simp
  have hv : v s ∈ s.active := by rw [hseed.1]; simp
  exact (masterTree_replay_law s (hs.vertices_le _ (hs.active_subset hu))
    (hs.vertices_le _ (hs.active_subset hv)) hseed.2 hseed.1 n).symm

end FreezingGrowth.TwoSeedGraft
