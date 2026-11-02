module

public import FreezingGrowth.TwoSeedGraftPrefix
public import FreezingGrowth.TaggedTwoSeedHeightModel

/-! The three source attach/freeze cases as complete labelled states.  The
frozen child in case zero remains in the graph, with its parent and timestamp.
The two surviving roots are ordered as in the source, including child-first
order in case two. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical ENNReal

def caseChosen (T u v : ℕ) (c : Fin 3) : ℕ :=
  if c = 0 then T + 1 else if c = 1 then u else v

def caseSeeds (T u v : ℕ) (c : Fin 3) : ℕ × ℕ :=
  if c = 0 then (u, v) else if c = 1 then (T + 1, v) else (T + 1, u)

def casePrefix (s : Forward.State) (T u v : ℕ) (c : Fin 3) : Forward.State :=
  Forward.freeze (Forward.attach s (T + 1) u) (T + 2) (caseChosen T u v c)

def caseState (T n : ℕ) (c : Fin 3) (z : Sample) : Forward.State :=
  replay (casePrefix z.initial T z.first z.second c) (T + 2)
    (caseSeeds T z.first z.second c).1 (caseSeeds T z.first z.second c).2 z.master.parent n

theorem casePrefix_valid {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (c : Fin 3) :
    Forward.ValidAt (T + 2) (casePrefix s T u v c) := by
  have hu : u ∈ s.active := by rw [ha]; simp
  exact (hs.attach hu).freeze _

theorem casePrefix_seeds {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v) (c : Fin 3) :
    (casePrefix s T u v c).active =
        {(caseSeeds T u v c).1, (caseSeeds T u v c).2} ∧
      (caseSeeds T u v c).1 ≠ (caseSeeds T u v c).2 := by
  have hu : u ≤ T := hs.vertices_le u (hs.active_subset (by rw [ha]; simp))
  have hv : v ≤ T := hs.vertices_le v (hs.active_subset (by rw [ha]; simp))
  have hut : u ≠ T + 1 := by omega
  have hvt : v ≠ T + 1 := by omega
  fin_cases c
  · simp [casePrefix, caseSeeds, caseChosen, Forward.freeze, Forward.attach, ha,
      huv, hut.symm, hvt.symm]
  · constructor
    · change (insert (T + 1) s.active).erase u = {T + 1, v}
      rw [ha]
      ext j
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · norm_num [caseSeeds, hvt.symm]
  · constructor
    · change (insert (T + 1) s.active).erase v = {T + 1, u}
      rw [ha]
      ext j
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · norm_num [caseSeeds, hut.symm]

theorem casePrefix_graph (s : Forward.State) (T u v : ℕ) (c : Fin 3) :
    (casePrefix s T u v c).graph = s.graph ⊔ SimpleGraph.edge u (T + 1) := rfl

theorem casePrefix_vertices (s : Forward.State) (T u v : ℕ) (c : Fin 3) :
    (casePrefix s T u v c).vertices = insert (T + 1) s.vertices := rfl

theorem casePrefix_parent (s : Forward.State) (T u v : ℕ) (c : Fin 3) :
    (casePrefix s T u v c).parent = Function.update s.parent (T + 1) u := rfl

theorem casePrefix_frozenAt (s : Forward.State) (T u v : ℕ) (c : Fin 3) :
    (casePrefix s T u v c).frozenAt =
      Function.update (Function.update s.frozenAt (T + 1) none)
        (caseChosen T u v c) (some (T + 2)) := rfl

/-- Even when the child itself is frozen, it remains a real labelled vertex. -/
theorem caseZero_retained_child (s : Forward.State) (T u v : ℕ) :
    T + 1 ∈ (casePrefix s T u v 0).vertices ∧
      (casePrefix s T u v 0).parent (T + 1) = u ∧
      (casePrefix s T u v 0).frozenAt (T + 1) = some (T + 2) := by
  simp [casePrefix, caseChosen, Forward.freeze, Forward.attach]

private theorem uniform_three {α : Type*} [MeasurableSpace α] [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Measure.uniformOfFinset ({a, b, c} : Finset α) = (3 : ℝ≥0∞)⁻¹ •
      (Measure.dirac a + Measure.dirac b + Measure.dirac c) := by
  simp [Measure.uniformOfFinset, hab, hac, hbc, smul_add, add_assoc]

/-- A fresh uniform case chooses exactly the actual uniform active vertex. -/
theorem threeCaseLaw_caseChosen {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v) :
    TwoSeedCoupling.threeCaseLaw.map (caseChosen T u v) =
      Measure.uniformOfFinset (Forward.attach s (T + 1) u).active := by
  have hu : u ≤ T := hs.vertices_le u (hs.active_subset (by rw [ha]; simp))
  have hv : v ≤ T := hs.vertices_le v (hs.active_subset (by rw [ha]; simp))
  have hut : T + 1 ≠ u := by omega
  have hvt : T + 1 ≠ v := by omega
  rw [TwoSeedCoupling.threeCaseLaw_eq,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _)]
  change _ = Measure.uniformOfFinset (insert (T + 1) s.active)
  rw [ha, uniform_three (T + 1) u v hut hvt huv]
  norm_num [caseChosen]

theorem caseChosen_tag {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v) (c : Fin 3) :
    Forward.twoSeedFreezeTag (T + 1) u (caseChosen T u v c) = c := by
  have hu : u ≤ T := hs.vertices_le u (hs.active_subset (by rw [ha]; simp))
  have hv : v ≤ T := hs.vertices_le v (hs.active_subset (by rw [ha]; simp))
  have hut : u ≠ T + 1 := by omega
  have hvt : v ≠ T + 1 := by omega
  fin_cases c <;> norm_num [caseChosen, Forward.twoSeedFreezeTag, hut, hvt, huv.symm]

theorem threeCaseLaw_casePrefix {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v) :
    TwoSeedCoupling.threeCaseLaw.map (casePrefix s T u v) =
      Forward.transitionLaw (Forward.attach s (T + 1) u) (T + 2) false := by
  have hne : (Forward.attach s (T + 1) u).active.Nonempty := by simp [Forward.attach]
  rw [Forward.transitionLaw, ite_eq_left hne, ← threeCaseLaw_caseChosen hs ha huv,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.map_congr
  apply Filter.Eventually.of_forall
  intro c
  have hm : caseChosen T u v c ∈ (Forward.attach s (T + 1) u).active := by
    fin_cases c <;> norm_num [caseChosen, Forward.attach, ha]
  simp only [Function.comp_def, Forward.step, ite_eq_left hm, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The actual master produces the complete conditional continuation in each
case, with the source's specified surviving-root order. -/
theorem masterTree_caseState_law {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v)
    (n : ℕ) (c : Fin 3) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => caseState T n c ⟨s, u, v, r⟩) =
      continuationLaw (casePrefix s T u v c) (T + 2) n := by
  have hp := casePrefix_valid hs ha c
  obtain ⟨hactive, hne⟩ := casePrefix_seeds hs ha huv c
  change (Forward.treeLaw RRT.allAttach (n + 1)).map
    (fun r => replay (casePrefix s T u v c) (T + 2)
      (caseSeeds T u v c).1 (caseSeeds T u v c).2 r.parent n) = _
  apply masterTree_replay_law
  · exact hp.vertices_le _ (hp.active_subset (by rw [hactive]; simp))
  · exact hp.vertices_le _ (hp.active_subset (by rw [hactive]; simp))
  · exact hne
  · exact hactive

theorem caseState_graph {T n : ℕ} {z : Sample} (hz : Parameters T n z) (c : Fin 3) :
    (caseState T n c z).graph =
      (z.initial.graph ⊔ SimpleGraph.edge z.first (T + 1)) ⊔
        ((RRTSplit.split n z.master).rootSide.mappedGraph.map
            (embedding (T + 2) (caseSeeds T z.first z.second c).1
              (caseSeeds T z.first z.second c).2) ⊔
          (RRTSplit.split n z.master).childSide.mappedGraph.map
            (embedding (T + 2) (caseSeeds T z.first z.second c).1
              (caseSeeds T z.first z.second c).2)) := by
  exact replay_graph_split _ _ _ _ _ _ hz.2.2.2.1 hz.2.2.2.2

/-- The preliminary attachment/freezing data survive the whole continuation. -/
theorem caseState_old_data (T n : ℕ) (c : Fin 3) (z : Sample) (a : ℕ) (ha : a ≤ T + 2) :
    (caseState T n c z).parent a = (casePrefix z.initial T z.first z.second c).parent a ∧
      (caseState T n c z).height a = (casePrefix z.initial T z.first z.second c).height a ∧
      (caseState T n c z).frozenAt a =
        (casePrefix z.initial T z.first z.second c).frozenAt a := by
  exact ⟨replay_parent_old _ _ _ _ _ _ _ ha,
    replay_height_old _ _ _ _ _ _ _ ha, replay_frozenAt_old _ _ _ _ _ _ _ ha⟩

end FreezingGrowth.TwoSeedGraft
