module

public import FreezingGrowth.TaggedGraftCoupling
public import FreezingGrowth.TwoSurvivorGap

/-! Source instantiation of the full-tree attach/freeze coupling, together with
the actual joint attachment history driven by the shared master parent array. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

def caseHistory (T n : ℕ) (c : Fin 3) (z : Sample) : FiniteMarkov.History Forward.State :=
  replayHistory (casePrefix z.initial T z.first z.second c) (T + 2)
    (caseSeeds T z.first z.second c).1 (caseSeeds T z.first z.second c).2 z.master.parent n

theorem caseHistory_current (T n : ℕ) (c : Fin 3) (z : Sample) :
    (caseHistory T n c z).current = caseState T n c z :=
  replayHistory_current _ _ _ _ _ _

/-- The whole suffix trajectory has Algorithm 1's conditional law in each
case, not merely its terminal coordinate. -/
theorem masterTree_caseHistory_law {s : Forward.State} {T u v : ℕ}
    (hs : Forward.ValidAt T s) (ha : s.active = {u, v}) (huv : u ≠ v)
    (n : ℕ) (c : Fin 3) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map
        (fun r => caseHistory T n c ⟨s, u, v, r⟩) =
      FiniteMarkov.historyLaw (Measure.dirac (casePrefix s T u v c))
        (fun j q => Forward.transitionLaw q (T + 2 + j + 1) true) n := by
  have hp := casePrefix_valid hs ha c
  obtain ⟨hactive, hne⟩ := casePrefix_seeds hs ha huv c
  change (Forward.treeLaw RRT.allAttach (n + 1)).map
    (fun r => replayHistory (casePrefix s T u v c) (T + 2)
      (caseSeeds T u v c).1 (caseSeeds T u v c).2 r.parent n) = _
  apply masterTree_replayHistory_law
  · exact hp.vertices_le _ (hp.active_subset (by rw [hactive]; simp))
  · exact hp.vertices_le _ (hp.active_subset (by rw [hactive]; simp))
  · exact hne
  · exact hactive

theorem taggedSampleLaw_ae_parameters (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ z ∂taggedSampleLaw xs n, Parameters xs.length n z.base := by
  have h := sampleLaw_ae_parameters xs n hc
  rw [← taggedLaw_base (sampleLaw xs n)] at h
  exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp h

/-- On a single sample all three grafts use the same actual master split.
The child frozen in case zero is retained in the displayed preliminary graph. -/
theorem taggedSampleLaw_all_case_graphs (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    ∀ᵐ z ∂taggedSampleLaw xs n, ∀ c : Fin 3,
      (caseState xs.length n c z.base).graph =
        (z.base.initial.graph ⊔ SimpleGraph.edge z.base.first (xs.length + 1)) ⊔
          ((RRTSplit.split n z.base.master).rootSide.mappedGraph.map
              (embedding (xs.length + 2) (caseSeeds xs.length z.base.first z.base.second c).1
                (caseSeeds xs.length z.base.first z.base.second c).2) ⊔
            (RRTSplit.split n z.base.master).childSide.mappedGraph.map
              (embedding (xs.length + 2) (caseSeeds xs.length z.base.first z.base.second c).1
                (caseSeeds xs.length z.base.first z.base.second c).2)) := by
  filter_upwards [taggedSampleLaw_ae_parameters xs n hc] with z hz c
  exact caseState_graph hz c

/-- Exact labels and the new vertices' parent assignments retain the actual
global birth order of the master, without an additional random shuffle. -/
theorem caseState_new_data (T n : ℕ) (c : Fin 3) (z : Sample) (j : ℕ) (hj : j < n) :
    (caseState T n c z).parent (T + 2 + j + 1) =
        embedding (T + 2) (caseSeeds T z.first z.second c).1
          (caseSeeds T z.first z.second c).2 (z.master.parent (j + 2)) ∧
      (caseState T n c z).frozenAt (T + 2 + j + 1) = none :=
  ⟨replay_parent_new _ _ _ _ _ _ _ hj, replay_frozenAt_new _ _ _ _ _ _ _ hj⟩

/-- The source's full attach/freeze construction, specialized to its actual
two-survivor prefix. Both complete labelled terminal states have their exact
finite-word laws on this one probability space. -/
theorem source_attachFreeze_full_state_coupling (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    IsProbabilityMeasure (taggedSampleLaw (twoActivePrefix m) n) ∧
      (taggedSampleLaw (twoActivePrefix m) n).map
          (taggedBaseline (twoActivePrefix m).length n) =
        Forward.treeLaw (twoActivePrefix m ++ List.replicate n true).toSigns
          (twoActivePrefix m ++ List.replicate n true).length ∧
      (taggedSampleLaw (twoActivePrefix m) n).map
          (taggedLong (twoActivePrefix m).length n) =
        Forward.treeLaw ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true).toSigns
          ((twoActivePrefix m ++ [true, false]) ++ List.replicate n true).length :=
  tagged_full_state_coupling _ n (twoActivePrefix_active_card m hm)

theorem source_attachFreeze_tag_independence (m n : ℕ) :
    (taggedSampleLaw (twoActivePrefix m) n).map (fun z => (z.base, z.tag)) =
      (sampleLaw (twoActivePrefix m) n).prod TwoSeedCoupling.threeCaseLaw :=
  taggedLaw_joint _

end FreezingGrowth.TwoSeedGraft
