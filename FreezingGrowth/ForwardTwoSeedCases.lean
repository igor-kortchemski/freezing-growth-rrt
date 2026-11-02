module

public import FreezingGrowth.AttachFreezeSeeds

/-! Vertex-identity tags for the three freezing cases after an attachment from
two active vertices. Tags distinguish the new child, its parent, and the other
old vertex even when their depths coincide. These are exact conditional
choice/profile laws, not a coupling of the full labelled trees after growth. -/

@[expose] public section
namespace FreezingGrowth.Forward

open MeasureTheory
open scoped Classical ENNReal

/-- Case zero freezes the new child, case one its parent, and case two the
other old active vertex. The third interpretation is used on the active support. -/
def twoSeedFreezeTag (child parent chosen : ℕ) : Fin 3 :=
  if chosen = child then 0 else if chosen = parent then 1 else 2

noncomputable def twoSeedTaggedFreezeLaw (s : State) (n parent : ℕ) :
    Measure (Fin 3 × HeightProfile) :=
  (Measure.uniformOfFinset (attach s (n + 1) parent).active).map
    (fun w => (twoSeedFreezeTag (n + 1) parent w,
      HeightProfile.ofState (freeze (attach s (n + 1) parent) (n + 2) w)))

private theorem uniformOfFinset_three {α : Type*} [MeasurableSpace α] [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Measure.uniformOfFinset ({a, b, c} : Finset α) = (3 : ℝ≥0∞)⁻¹ •
      (Measure.dirac a + Measure.dirac b + Measure.dirac c) := by
  simp [Measure.uniformOfFinset, hab, hac, hbc, smul_add, add_assoc]

theorem ofState_of_active_pair (s : State) (u v : ℕ)
    (hactive : s.active = {u, v}) (huv : u ≠ v) :
    HeightProfile.ofState s = ⟨{s.height u, s.height v}, treeHeight s⟩ := by
  apply HeightProfile.ext
  · simp [HeightProfile.ofState, hactive, huv, Multiset.insert_eq_cons]
  · rfl

private theorem twoSeed_fresh {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) : u ≠ n + 1 ∧ v ≠ n + 1 := by
  have hu : u ∈ s.active := by rw [hactive]; simp
  have hv : v ∈ s.active := by rw [hactive]; simp
  have hu' := hs.vertices_le u (hs.active_subset hu)
  have hv' := hs.vertices_le v (hs.active_subset hv)
  omega

theorem twoSeed_child_frozen_profile {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    HeightProfile.ofState (freeze (attach s (n + 1) u) (n + 2) (n + 1)) =
      ⟨{s.height u, s.height v}, max (treeHeight s) (s.height u + 1)⟩ := by
  rw [HeightProfile.ofState_freeze _ _ (by simp [attach]),
    HeightProfile.ofState_attach hs u, ofState_of_active_pair s u v hactive huv]
  change HeightProfile.freeze
      ⟨{s.height u + 1, s.height u, s.height v}, max (treeHeight s) (s.height u + 1)⟩
      ((attach s (n + 1) u).height (n + 1)) = _
  simp only [attach, Function.update_self, HeightProfile.freeze_triple_first]

theorem twoSeed_parent_frozen_profile {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    HeightProfile.ofState (freeze (attach s (n + 1) u) (n + 2) u) =
      ⟨{s.height u + 1, s.height v}, max (treeHeight s) (s.height u + 1)⟩ := by
  have hu : u ∈ (attach s (n + 1) u).active := by simp [attach, hactive]
  have hune := (twoSeed_fresh hs hactive).1
  rw [HeightProfile.ofState_freeze _ _ hu, HeightProfile.ofState_attach hs u,
    ofState_of_active_pair s u v hactive huv]
  change HeightProfile.freeze
      ⟨{s.height u + 1, s.height u, s.height v}, max (treeHeight s) (s.height u + 1)⟩
      ((attach s (n + 1) u).height u) = _
  simp only [attach, Function.update_of_ne hune, HeightProfile.freeze_triple_second]

theorem twoSeed_other_frozen_profile {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    HeightProfile.ofState (freeze (attach s (n + 1) u) (n + 2) v) =
      ⟨{s.height u, s.height u + 1}, max (treeHeight s) (s.height u + 1)⟩ := by
  have hv : v ∈ (attach s (n + 1) u).active := by simp [attach, hactive]
  have hvne := (twoSeed_fresh hs hactive).2
  rw [HeightProfile.ofState_freeze _ _ hv, HeightProfile.ofState_attach hs u,
    ofState_of_active_pair s u v hactive huv]
  change HeightProfile.freeze
      ⟨{s.height u + 1, s.height u, s.height v}, max (treeHeight s) (s.height u + 1)⟩
      ((attach s (n + 1) u).height v) = _
  simp only [attach, Function.update_of_ne hvne, HeightProfile.freeze_triple_third]
  congr 1
  exact Multiset.pair_comm _ _

/-- The case tag and the resulting height profile have this exact joint law.
Distinct vertex IDs are required; distinct depths are not. -/
theorem twoSeedTaggedFreezeLaw_eq {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    twoSeedTaggedFreezeLaw s n u = (3 : ℝ≥0∞)⁻¹ •
      (Measure.dirac ((0 : Fin 3),
          (⟨{s.height u, s.height v}, max (treeHeight s) (s.height u + 1)⟩ : HeightProfile)) +
        Measure.dirac ((1 : Fin 3),
          (⟨{s.height u + 1, s.height v}, max (treeHeight s) (s.height u + 1)⟩ : HeightProfile)) +
        Measure.dirac ((2 : Fin 3),
          (⟨{s.height u, s.height u + 1}, max (treeHeight s) (s.height u + 1)⟩ : HeightProfile))) := by
  obtain ⟨hune, hvne⟩ := twoSeed_fresh hs hactive
  have hset : (attach s (n + 1) u).active = {n + 1, u, v} := by simp [attach, hactive]
  have hf : Measurable (fun w => (twoSeedFreezeTag (n + 1) u w,
      HeightProfile.ofState (freeze (attach s (n + 1) u) (n + 2) w))) :=
    measurable_of_countable _
  unfold twoSeedTaggedFreezeLaw
  rw [hset, uniformOfFinset_three _ _ _ hune.symm hvne.symm huv,
    Measure.map_smul _ hf.aemeasurable,
    Measure.map_add _ _ hf, Measure.map_add _ _ hf,
    Measure.map_dirac' hf, Measure.map_dirac' hf, Measure.map_dirac' hf,
    twoSeed_child_frozen_profile hs hactive huv,
    twoSeed_parent_frozen_profile hs hactive huv,
    twoSeed_other_frozen_profile hs hactive huv]
  simp [twoSeedFreezeTag, hune, hvne, huv.symm]

/-- For every valid original state and chosen parent, the case marginal is the
same uniform law on three tags. This is the fixed-state conditional assertion. -/
theorem twoSeedTaggedFreezeLaw_tag {n : ℕ} {s : State} (hs : ValidAt n s)
    {u v : ℕ} (hactive : s.active = {u, v}) (huv : u ≠ v) :
    (twoSeedTaggedFreezeLaw s n u).map Prod.fst =
      Measure.uniformOfFinset (Finset.univ : Finset (Fin 3)) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp
  rw [twoSeedTaggedFreezeLaw_eq hs hactive huv,
    Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
    Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst,
    Measure.map_dirac' measurable_fst, hu,
    uniformOfFinset_three (0 : Fin 3) 1 2 (by norm_num) (by norm_num) (by norm_num)]

end FreezingGrowth.Forward
