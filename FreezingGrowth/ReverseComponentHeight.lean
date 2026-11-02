module

public import FreezingGrowth.ReverseOrderedHeightBridge

/-!
# The genuine component-height observable under grafting

These deterministic identities supply the height projection and synchronized
grafting monotonicity needed in Algorithm 3. Each component height is the
maximum actual distance to that component's root; it is not a substitute
state whose connection to the forest is assumed.
-/

@[expose] public section

namespace FreezingGrowth.RootedForest

open scoped Classical

variable {V : Type*} [DecidableEq V]

def componentVertices (F : RootedForest V) (r : V) : Finset V :=
  F.vertices.filter (fun v => F.root v = r)

def componentHeight (F : RootedForest V) (r : V) : ℕ :=
  (F.componentVertices r).sup F.depth

theorem componentHeight_eq_max_distance (F : RootedForest V) (r : V) :
    F.componentHeight r =
      (F.componentVertices r).sup (fun v => F.graph.dist r v) := by
  apply Finset.sup_congr rfl
  intro v hv
  obtain ⟨hv, hr⟩ := Finset.mem_filter.mp hv
  simpa only [hr] using F.depth_eq_dist hv

theorem depth_le_componentHeight (F : RootedForest V) {v r : V}
    (hv : v ∈ F.vertices) (hr : F.root v = r) : F.depth v ≤ F.componentHeight r :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨hv, hr⟩)

theorem componentHeight_attained (F : RootedForest V) {r : V} (hr : r ∈ F.roots) :
    ∃ v ∈ F.vertices, F.root v = r ∧ F.depth v = F.componentHeight r := by
  have hne : (F.componentVertices r).Nonempty :=
    ⟨r, Finset.mem_filter.mpr (mem_roots.mp hr)⟩
  obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_sup (F.componentVertices r) hne F.depth
  obtain ⟨hv, hvroot⟩ := Finset.mem_filter.mp hv
  exact ⟨v, hv, hvroot, he.symm⟩

/-- Grafting component `b` below root `a` updates exactly the receiver's
height by the source formula `max (H a) (H b + 1)`. -/
theorem componentHeight_join_receiver (F : RootedForest V) {a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).componentHeight a =
      max (F.componentHeight a) (F.componentHeight b + 1) := by
  apply le_antisymm
  · apply Finset.sup_le
    intro v hv
    obtain ⟨hv, hr⟩ := Finset.mem_filter.mp hv
    change v ∈ F.vertices at hv
    change (if F.root v = b then a else F.root v) = a at hr
    by_cases hvb : F.root v = b
    · rw [join_depth, ite_eq_left hvb]
      exact (Nat.add_le_add_right (F.depth_le_componentHeight hv hvb) 1).trans
        (le_max_right _ _)
    · have hva : F.root v = a := by simpa only [ite_eq_right hvb] using hr
      rw [join_depth, ite_eq_right hvb, Nat.add_zero]
      exact (F.depth_le_componentHeight hv hva).trans (le_max_left _ _)
  · apply max_le
    · obtain ⟨v, hv, hr, hd⟩ := F.componentHeight_attained ha
      have hroot : (F.join a b ha hb hab).root v = a := by simp [join, hr, hab]
      have hh := (F.join a b ha hb hab).depth_le_componentHeight hv hroot
      simpa only [join_depth, hr, ite_eq_right hab, Nat.add_zero, hd] using hh
    · obtain ⟨v, hv, hr, hd⟩ := F.componentHeight_attained hb
      have hroot : (F.join a b ha hb hab).root v = a := by simp [join, hr]
      have hh := (F.join a b ha hb hab).depth_le_componentHeight hv hroot
      simpa only [join_depth, hr, ↓reduceIte, hd] using hh

theorem componentVertices_join_other (F : RootedForest V) {a b c : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    (F.join a b ha hb hab).componentVertices c = F.componentVertices c := by
  ext v
  simp only [componentVertices, Finset.mem_filter]
  change (v ∈ F.vertices ∧ (if F.root v = b then a else F.root v) = c) ↔
    (v ∈ F.vertices ∧ F.root v = c)
  by_cases hvb : F.root v = b
  · simp only [hvb, ↓reduceIte, hca.symm, hcb.symm, and_false]
  · rw [ite_eq_right hvb]

/-- Every other surviving component retains its actual height. -/
theorem componentHeight_join_other (F : RootedForest V) {a b c : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    (F.join a b ha hb hab).componentHeight c = F.componentHeight c := by
  unfold componentHeight
  rw [componentVertices_join_other F ha hb hab hca hcb]
  apply Finset.sup_congr rfl
  intro v hv
  have hr := (Finset.mem_filter.mp hv).2
  rw [join_depth, hr, ite_eq_right hcb, Nat.add_zero]

/-- Taking the maximum of all component heights gives the forest maximum. -/
theorem sup_componentHeight (F : RootedForest V) :
    F.roots.sup F.componentHeight = F.maxDepth := by
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    apply Finset.sup_le
    intro v hv
    exact Finset.le_sup (Finset.mem_filter.mp hv).1
  · apply Finset.sup_le
    intro v hv
    exact (F.depth_le_componentHeight hv rfl).trans
      (Finset.le_sup (F.root_mem_roots hv))

/-- The scalar update used by a synchronized graft is monotone in both
grafted component heights. -/
theorem graft_height_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    max a (b + 1) ≤ max a' (b' + 1) :=
  max_le_max ha (Nat.add_le_add_right hb 1)

end FreezingGrowth.RootedForest

namespace FreezingGrowth.ReverseOrdered

open scoped Classical

/-- The actual ordered list of maximum component-root distances. -/
def heightProfile (F : Forest) : List ℕ := F.rootOrder.map F.forest.componentHeight

@[simp] theorem heightProfile_length (F : Forest) :
    (heightProfile F).length = F.rootOrder.length := by simp [heightProfile]

/-- The height-list observable retains the exact maximum height. -/
theorem heightProfile_max (F : Forest) :
    (heightProfile F).toFinset.sup id = F.forest.maxDepth := by
  unfold heightProfile
  have hm : (F.rootOrder.map F.forest.componentHeight).toFinset =
      F.forest.roots.image F.forest.componentHeight := by
    ext h
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, mem_rootOrder F]
  rw [hm, Finset.sup_image]
  exact F.forest.sup_componentHeight

end FreezingGrowth.ReverseOrdered
