module

public import FreezingGrowth.RRTSplitGraph
public import FreezingGrowth.Height
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# First-edge split on the actual recursive-tree support

The deterministic replay describes every state sampled from the existing
forward law. In particular its complete local states, partition, original
birth labels, and depth offsets are proved properties of the actual tree.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory
open scoped Classical ENNReal

/-- The first attachment is forced. -/
theorem treeLaw_one : Forward.treeLaw RRT.allAttach 1 =
    Measure.dirac (Forward.attach Forward.initial 1 0) := by
  rw [Forward.treeLaw, Forward.treeLaw, Measure.dirac_bind measurable_from_top]
  simp [Forward.transitionLaw, Forward.initial, Measure.uniformOfFinset,
    Forward.step, RRT.allAttach, Measure.map_dirac' measurable_from_top]

/-- The full canonical split invariant holds on the genuine forward support. -/
theorem treeLaw_split_describes (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw RRT.allAttach (n + 1), Describes n s (split n s) := by
  induction n with
  | zero =>
    rw [treeLaw_one]
    refine (ae_dirac_iff (by trivial)).mpr ?_
    simpa only [split, replay] using initial_describes
  | succ n ih =>
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [Forward.treeLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂Forward.treeLaw RRT.allAttach (n + 1) := by
        apply lintegral_congr_ae
        filter_upwards [ih] with s hs
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply Forward.transitionLaw_ae
        · intro he
          have hzero : 0 ∈ s.active := by rw [hs.active]; simp
          simp [he] at hzero
        · intro v hv
          have hv' : v < n + 2 := by simpa only [hs.active, Finset.mem_range] using hv
          have h := hs.attach hv'
          rw [← split_attach s n v] at h
          simpa only [RRT.allAttach, Forward.step, ite_eq_left hv, ite_true,
            Nat.add_assoc] using h
      _ = 1 := by simp

theorem WellFormed.length_sum {n : ℕ} {p : Parts} (hp : WellFormed n p) :
    p.rootSide.labels.length + p.childSide.labels.length = n + 2 := by
  have hd : Disjoint p.rootSide.labels.toFinset p.childSide.labels.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hp.disjoint (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hw)
  have hc := congrArg Finset.card hp.cover
  simpa only [Finset.card_union_of_disjoint hd,
    List.toFinset_card_of_nodup hp.root.nodup,
    List.toFinset_card_of_nodup hp.child.nodup, Finset.card_range] using hc

/-- The two local edge counts add to the original edge count minus one. -/
theorem WellFormed.edges_sum {n : ℕ} {p : Parts} (hp : WellFormed n p) :
    (p.rootSide.labels.length - 1) + (p.childSide.labels.length - 1) = n := by
  have := hp.length_sum
  have := hp.root.length_pos
  have := hp.child.length_pos
  omega

theorem Describes.root_label_mem {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) {i : ℕ} (hi : i < p.rootSide.labels.length) :
    p.rootSide.label i ∈ s.vertices := by
  rw [hs.vertices]
  exact Finset.mem_range.mpr (hs.formed.root_lt _ (p.rootSide.label_mem hi))

theorem Describes.child_label_mem {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) {i : ℕ} (hi : i < p.childSide.labels.length) :
    p.childSide.label i ∈ s.vertices := by
  rw [hs.vertices]
  exact Finset.mem_range.mpr (hs.formed.child_lt _ (p.childSide.label_mem hi))

/-- The maximum height uses the actual root component and the depth-reset
child component. The first removed edge contributes exactly one. -/
theorem Describes.height_eq {n : ℕ} {s : Forward.State} {p : Parts}
    (hs : Describes n s p) :
    Forward.treeHeight s = max (Forward.treeHeight p.rootSide.tree)
      (Forward.treeHeight p.childSide.tree + 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v hv
    have hv' : v < n + 2 := by simpa only [hs.vertices, Finset.mem_range] using hv
    rcases hs.formed.mem_or hv' with hr | hc
    · have hi := List.idxOf_lt_length_of_mem hr
      have hd := hs.root_height _ hi
      rw [Component.label_idxOf hr] at hd
      rw [hd]
      exact (Forward.height_le_treeHeight (by
        rw [hs.formed.root.vertices]
        exact Finset.mem_range.mpr hi)).trans (le_max_left _ _)
    · have hi := List.idxOf_lt_length_of_mem hc
      have hd := hs.child_height _ hi
      rw [Component.label_idxOf hc] at hd
      rw [hd]
      exact (Nat.add_le_add_right (Forward.height_le_treeHeight (by
        rw [hs.formed.child.vertices]
        exact Finset.mem_range.mpr hi)) 1).trans (le_max_right _ _)
  · apply max_le
    · apply Finset.sup_le
      intro i hi
      have hi' : i < p.rootSide.labels.length := by
        simpa only [hs.formed.root.vertices, Finset.mem_range] using hi
      rw [← hs.root_height i hi']
      exact Forward.height_le_treeHeight (hs.root_label_mem hi')
    · have hpos : 1 ≤ Forward.treeHeight s := by
        have h := Forward.height_le_treeHeight (hs.child_label_mem hs.formed.child.length_pos)
        rw [hs.child_height 0 hs.formed.child.length_pos,
          hs.formed.child.valid.height_root] at h
        exact h
      have hbound : Forward.treeHeight p.childSide.tree ≤ Forward.treeHeight s - 1 := by
        apply Finset.sup_le
        intro i hi
        have hi' : i < p.childSide.labels.length := by
          simpa only [hs.formed.child.vertices, Finset.mem_range] using hi
        have h := Forward.height_le_treeHeight (hs.child_label_mem hi')
        rw [hs.child_height i hi'] at h
        omega
      omega

/-- Source height decomposition under the same sampled full tree. -/
theorem treeLaw_height_split (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw RRT.allAttach (n + 1),
      Forward.treeHeight s = max (Forward.treeHeight (split n s).rootSide.tree)
        (Forward.treeHeight (split n s).childSide.tree + 1) :=
  (treeLaw_split_describes n).mono fun _ hs => hs.height_eq

end FreezingGrowth.RRTSplit
