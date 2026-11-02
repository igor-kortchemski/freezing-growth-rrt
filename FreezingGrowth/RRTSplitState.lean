module

public import FreezingGrowth.RRTUniformDepth
public import FreezingGrowth.ReverseForwardStateDefaults
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Nodup

/-!
# Canonical components obtained by deleting the first recursive-tree edge

The source's vertices 1 and 2 have birth identifiers 0 and 1 here. Replaying
an actual parent's array in birth order assigns each subsequent vertex to its
parent's component. The labels in each component retain their increasing birth
order, while its existing `Forward.State` uses the local labels 0, 1, ... .
The right component starts at height zero; its global height has offset one.

These are deterministic definitions. Their on-support graph characterization
and joint probability law are proved separately, not assumed in this encoding.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory
open scoped Classical

/-- A local tree with its original birth labels, in local-label order. -/
structure Component where
  labels : List ℕ
  tree : Forward.State

namespace Component

def initial (r : ℕ) : Component := ⟨[r], Forward.initial⟩

/-- The original birth identifier represented by a local vertex. The default
is irrelevant on the proved finite vertex set. -/
def label (c : Component) (i : ℕ) : ℕ := c.labels[i]?.getD 0

/-- Append the fresh global vertex to its parent's component. -/
def attach (c : Component) (t v : ℕ) : Component :=
  ⟨c.labels ++ [t], Forward.attach c.tree c.labels.length (c.labels.idxOf v)⟩

structure WellFormed (r : ℕ) (c : Component) : Prop where
  ordered : c.labels.Pairwise (· < ·)
  rooted : ∃ tail, c.labels = r :: tail
  valid : Forward.ValidAt (c.labels.length - 1) c.tree
  vertices : c.tree.vertices = Finset.range c.labels.length
  active : c.tree.active = Finset.range c.labels.length
  defaults : Forward.CanonicalDefaults c.tree
  frozen : c.tree.frozenAt = fun _ => none

theorem initial_wellFormed (r : ℕ) : WellFormed r (initial r) := by
  refine ⟨by simp [initial], ⟨[], rfl⟩, ?_, ?_, ?_, ?_, rfl⟩
  · simpa only [initial, List.length_singleton, Nat.sub_self] using Forward.initial_valid
  · simp [initial, Forward.initial]
  · simp [initial, Forward.initial]
  · exact Forward.initial_canonical_defaults

theorem WellFormed.length_pos {r : ℕ} {c : Component} (hc : WellFormed r c) :
    0 < c.labels.length := by
  obtain ⟨tail, ht⟩ := hc.rooted
  simp [ht]

theorem WellFormed.nodup {r : ℕ} {c : Component} (hc : WellFormed r c) :
    c.labels.Nodup := hc.ordered.imp (fun h => ne_of_lt h)

theorem label_idxOf {c : Component} {v : ℕ} (hv : v ∈ c.labels) :
    c.label (c.labels.idxOf v) = v := by
  simp [label, List.getElem?_idxOf hv]

theorem label_attach_old (c : Component) (t v i : ℕ) (hi : i < c.labels.length) :
    (c.attach t v).label i = c.label i := by
  simp only [label, Component.attach, List.getElem?_append_left hi]

@[simp] theorem label_attach_new (c : Component) (t v : ℕ) :
    (c.attach t v).label c.labels.length = t := by
  simp [label, Component.attach]

theorem WellFormed.label_zero {r : ℕ} {c : Component} (hc : WellFormed r c) :
    c.label 0 = r := by
  obtain ⟨tail, ht⟩ := hc.rooted
  simp [label, ht]

theorem WellFormed.label_injective {r : ℕ} {c : Component} (hc : WellFormed r c) :
    Set.InjOn c.label (Finset.range c.labels.length) := by
  intro i hi j hj he
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  simp only [label, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj',
    Option.getD_some] at he
  exact (hc.nodup.getElem_inj_iff (hi := hi') (hj := hj')).mp he

theorem WellFormed.attach {r : ℕ} {c : Component} (hc : WellFormed r c)
    {t v : ℕ} (hv : v ∈ c.labels) (ht : ∀ u ∈ c.labels, u < t) :
    WellFormed r (c.attach t v) := by
  have hlen : c.labels.length - 1 + 1 = c.labels.length := by
    have := hc.length_pos
    omega
  have hvA : c.labels.idxOf v ∈ c.tree.active := by
    rw [hc.active]
    exact Finset.mem_range.mpr (List.idxOf_lt_length_of_mem hv)
  have hvalid := hc.valid.attach hvA
  rw [hlen] at hvalid
  have hdefaults := hc.defaults.attach (c.labels.length - 1) (c.labels.idxOf v)
  rw [hlen] at hdefaults
  refine ⟨?_, ?_, ?_, ?_, ?_, hdefaults, ?_⟩
  · simpa only [Component.attach, List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq, and_true, true_and] using And.intro hc.ordered ht
  · obtain ⟨tail, htail⟩ := hc.rooted
    exact ⟨tail ++ [t], by simp only [Component.attach, htail, List.cons_append]⟩
  · simpa only [Component.attach, List.length_append, List.length_singleton,
      Nat.add_sub_cancel] using hvalid
  · simp [Component.attach, Forward.attach, hc.vertices, Finset.range_add_one]
  · simp [Component.attach, Forward.attach, hc.active, Finset.range_add_one]
  · funext i
    simp [Component.attach, Forward.attach, hc.frozen]

end Component

/-- The two ordered components, with the original root first. -/
structure Parts where
  rootSide : Component
  childSide : Component

def initial : Parts := ⟨Component.initial 0, Component.initial 1⟩

/-- A fresh vertex follows its parent's component. Every use in the law proof
is supported on the disjoint union of the two label lists. -/
def grow (p : Parts) (t v : ℕ) : Parts :=
  if v ∈ p.rootSide.labels then
    ⟨p.rootSide.attach t v, p.childSide⟩
  else ⟨p.rootSide, p.childSide.attach t v⟩

/-- Replay the `n` births after the forced first edge. -/
def replay (parent : ℕ → ℕ) : ℕ → Parts
  | 0 => initial
  | n + 1 => grow (replay parent n) (n + 2) (parent (n + 2))

/-- Deterministic canonical split of an `(n+1)`-edge state. The characterization
on the actual recursive-tree support is required before using its tree meaning. -/
def split (n : ℕ) (s : Forward.State) : Parts := replay s.parent n

/-- The root component's edge count and the two complete local tree states. -/
def observable (p : Parts) : ℕ × Forward.State × Forward.State :=
  (p.rootSide.labels.length - 1, p.rootSide.tree, p.childSide.tree)

def firstEdgeSplit (n : ℕ) (s : Forward.State) : ℕ × Forward.State × Forward.State :=
  observable (split n s)

theorem replay_congr {parent parent' : ℕ → ℕ} (n : ℕ)
    (h : ∀ i, 2 ≤ i → i ≤ n + 1 → parent i = parent' i) :
    replay parent n = replay parent' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replay]
    rw [ih (fun i hi hi' => h i hi (by omega)), h (n + 2) (by omega) (by omega)]

theorem split_attach_prefix (s : Forward.State) (n v : ℕ) :
    split n (Forward.attach s (n + 2) v) = split n s := by
  apply replay_congr
  intro i _ hi
  exact Function.update_of_ne (by omega) _ _

/-- The split evolves by the actual newly selected parent. -/
theorem split_attach (s : Forward.State) (n v : ℕ) :
    split (n + 1) (Forward.attach s (n + 2) v) = grow (split n s) (n + 2) v := by
  change grow (split n (Forward.attach s (n + 2) v)) (n + 2)
    ((Forward.attach s (n + 2) v).parent (n + 2)) = _
  rw [split_attach_prefix]
  simp only [Forward.attach, Function.update_self]

/-- The lists record a partition of all actual birth identifiers. -/
structure WellFormed (n : ℕ) (p : Parts) : Prop where
  root : p.rootSide.WellFormed 0
  child : p.childSide.WellFormed 1
  disjoint : List.Disjoint p.rootSide.labels p.childSide.labels
  cover : p.rootSide.labels.toFinset ∪ p.childSide.labels.toFinset = Finset.range (n + 2)

theorem initial_wellFormed : WellFormed 0 initial := by
  refine ⟨Component.initial_wellFormed 0, Component.initial_wellFormed 1, ?_, ?_⟩
  · simp [initial, Component.initial]
  · simpa [initial, Component.initial, Finset.range_add_one] using Finset.pair_comm 0 1

theorem WellFormed.mem_or {n : ℕ} {p : Parts} (hp : WellFormed n p) {v : ℕ}
    (hv : v < n + 2) : v ∈ p.rootSide.labels ∨ v ∈ p.childSide.labels := by
  have hm : v ∈ p.rootSide.labels.toFinset ∪ p.childSide.labels.toFinset := by
    rw [hp.cover]
    exact Finset.mem_range.mpr hv
  simpa only [Finset.mem_union, List.mem_toFinset] using hm

theorem WellFormed.root_lt {n : ℕ} {p : Parts} (hp : WellFormed n p) :
    ∀ v ∈ p.rootSide.labels, v < n + 2 := by
  intro v hv
  apply Finset.mem_range.mp
  rw [← hp.cover]
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr hv)

theorem WellFormed.child_lt {n : ℕ} {p : Parts} (hp : WellFormed n p) :
    ∀ v ∈ p.childSide.labels, v < n + 2 := by
  intro v hv
  apply Finset.mem_range.mp
  rw [← hp.cover]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hv)

theorem WellFormed.grow {n : ℕ} {p : Parts} (hp : WellFormed n p) {v : ℕ}
    (hv : v < n + 2) : WellFormed (n + 1) (grow p (n + 2) v) := by
  have hroot : n + 2 ∉ p.rootSide.labels := fun h => (hp.root_lt _ h).false
  have hchild : n + 2 ∉ p.childSide.labels := fun h => (hp.child_lt _ h).false
  by_cases hr : v ∈ p.rootSide.labels
  · rw [RRTSplit.grow, ite_eq_left hr]
    refine ⟨hp.root.attach hr hp.root_lt, hp.child, ?_, ?_⟩
    · intro u hu hu'
      simp only [Component.attach, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact hp.disjoint hu hu'
      · exact hchild hu'
    · ext u
      have hcov := Finset.ext_iff.mp hp.cover u
      simp only [Component.attach, List.toFinset_append, List.toFinset_cons,
        List.toFinset_nil, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty,
        or_false, List.mem_toFinset, Finset.mem_range] at hcov ⊢
      have h3 : u < n + 1 + 2 ↔ u < n + 2 ∨ u = n + 2 := by omega
      rw [h3, ← hcov]
      tauto
  · have hc : v ∈ p.childSide.labels := (hp.mem_or hv).resolve_left hr
    rw [RRTSplit.grow, ite_eq_right hr]
    refine ⟨hp.root, hp.child.attach hc hp.child_lt, ?_, ?_⟩
    · intro u hu hu'
      simp only [Component.attach, List.mem_append, List.mem_singleton] at hu'
      rcases hu' with hu' | rfl
      · exact hp.disjoint hu hu'
      · exact hroot hu
    · simp only [Component.attach, List.toFinset_append, List.toFinset_cons,
        List.toFinset_nil, Finset.union_empty, Finset.union_insert, hp.cover,
        Nat.add_assoc, Nat.reduceAdd, Finset.range_add_one]

end FreezingGrowth.RRTSplit
