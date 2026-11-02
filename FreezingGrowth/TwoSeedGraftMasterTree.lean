module

public import FreezingGrowth.TwoSeedGraftMasterPrefix
public import FreezingGrowth.TwoSeedGraftGeometry

/-! The initial edge and its replayed continuation recover the actual RRT
prefix on the very same master parent array. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

def masterTreeBase : Forward.State := Forward.attach Forward.initial 1 0

def masterPrefix (k : ℕ) (r : Forward.State) : Forward.State :=
  replay masterTreeBase 1 0 1 r.parent k

theorem masterTreeBase_active : masterTreeBase.active = {0, 1} := by
  simp [masterTreeBase, Forward.attach, Forward.initial, Finset.pair_comm]

theorem masterTreeBase_parent (a : ℕ) (ha : a ≤ 1) :
    masterTreeBase.parent a = Forward.initial.parent a := by
  cases a with
  | zero => simp [masterTreeBase, Forward.attach, Forward.initial]
  | succ a =>
    have ha' : a = 0 := by omega
    subst a
    simp [masterTreeBase, Forward.attach, Forward.initial]

theorem masterPrefix_parent_new (k : ℕ) (r : Forward.State) (a : ℕ)
    (ha₂ : 2 ≤ a) (haₖ : a ≤ k + 1) :
    (masterPrefix k r).parent a = r.parent a := by
  have hj : a - 2 < k := by omega
  have h := replay_parent_new masterTreeBase 1 0 1 r.parent k (a - 2) hj
  have hindex : 1 + (a - 2) + 1 = a := by omega
  have hemb : embedding 1 0 1 = id := by
    funext x
    cases x with
    | zero => rfl
    | succ x => cases x <;> simp [embedding]; omega
  rw [hindex] at h
  rw [hemb] at h
  rw [Nat.sub_add_cancel ha₂] at h
  simpa [masterPrefix] using h

theorem masterPrefix_split_eq (k : ℕ) (r : Forward.State) :
    RRTSplit.split k (masterPrefix k r) = RRTSplit.split k r := by
  apply RRTSplit.replay_congr
  intro i hi₂ hiₖ
  exact masterPrefix_parent_new k r i hi₂ hiₖ

theorem continuationLaw_masterTreeBase (k : ℕ) :
    continuationLaw masterTreeBase 1 k = Forward.treeLaw RRT.allAttach (k + 1) := by
  have hx : ∀ j < k, RRT.allAttach (1 + j + 1) = true := by
    intro j hj
    simp [RRT.allAttach]
  have h := treeLaw_bind_continuation RRT.allAttach 1 k hx
  rw [show 1 + k = k + 1 by omega, RRTSplit.treeLaw_one,
    Measure.dirac_bind measurable_from_top] at h
  simpa [masterTreeBase] using h.symm

theorem masterPrefix_law (k m : ℕ) (hm : k + 1 ≤ m) :
    (Forward.treeLaw RRT.allAttach m).map (masterPrefix k) =
      Forward.treeLaw RRT.allAttach (k + 1) := by
  change (Forward.treeLaw RRT.allAttach m).map
      (fun r => replay masterTreeBase 1 0 1 r.parent k) = _
  rw [masterTree_replay_prefix_of_le masterTreeBase 1 0 1 k m hm]
  rw [masterTree_replay_law masterTreeBase (T := 1) (u := 0) (v := 1)
    (by omega) le_rfl (by decide)
    masterTreeBase_active k, continuationLaw_masterTreeBase]

end FreezingGrowth.TwoSeedGraft
