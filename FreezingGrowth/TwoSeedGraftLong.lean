module

public import FreezingGrowth.TwoSeedGraftPrefix

/-! The longer word's full-State marginal on the same master-graft sample. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

theorem stateSampleLaw_long (s : Forward.State) {T : ℕ} (hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) (n : ℕ) :
    (stateSampleLaw s n).map (longState T n) =
      ((Forward.transitionLaw s (T + 1) false).bind
        (fun q => Forward.transitionLaw q (T + 2) true)).bind
          (fun q => continuationLaw q (T + 2) n) := by
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hc
  rw [freeze_attach_pair s T hsab hab,
    Measure.bind_map (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    stateSampleLaw, Measure.map_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  have hu : p.1 ≤ T := hs.vertices_le _ (hs.active_subset ha)
  have hpair := active_eq_pair_of_card_two hc hp
  let q := Forward.attach (Forward.freeze s (T + 1) p.2) (T + 2) p.1
  have hq : q.active = {T + 2, p.1} := by
    ext j
    simp only [q, Forward.attach, Forward.freeze, hpair, Finset.mem_insert,
      Finset.mem_erase, Finset.mem_singleton]
    aesop
  rw [Measure.map_map measurable_from_top measurable_from_top]
  change (Forward.treeLaw RRT.allAttach (n + 1)).map
    (fun r => replay q (T + 2) (T + 2) p.1 r.parent n) = continuationLaw q (T + 2) n
  exact masterTree_replay_law q le_rfl (by omega) (by omega) hq n

theorem freezeAttach_prefix_law (xs : Word) :
    Forward.treeLaw (xs ++ [false, true]).toSigns (xs ++ [false, true]).length =
      (Forward.treeLaw xs.toSigns xs.length).bind (fun s =>
        (Forward.transitionLaw s (xs.length + 1) false).bind
          (fun q => Forward.transitionLaw q (xs.length + 2) true)) := by
  let x := (xs ++ [false, true]).toSigns
  have hf : x (xs.length + 1) = false := by
    simpa only [x, Nat.add_zero, Word.toSigns_succ, List.getElem?_cons_zero, Option.getD_some] using
      Word.toSigns_append_right xs [false, true] 0
  have ht : x (xs.length + 2) = true := by
    simpa only [x, Word.toSigns_succ, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some] using
      Word.toSigns_append_right xs [false, true] 1
  have hp : Forward.treeLaw x xs.length = Forward.treeLaw xs.toSigns xs.length :=
    Forward.treeLaw_congr (fun i hi => Word.toSigns_append_left xs [false, true] hi)
  rw [List.length_append]
  change Forward.treeLaw x ((xs.length + 1) + 1) = _
  rw [Forward.treeLaw, ht, Forward.treeLaw, hf, hp,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]

theorem sampleLaw_long (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (sampleLaw xs n).map (longState xs.length n) =
      Forward.treeLaw ((xs ++ [false, true]) ++ List.replicate n true).toSigns
        ((xs ++ [false, true]) ++ List.replicate n true).length := by
  have hlen : (xs ++ [false, true]).length = xs.length + 2 := by simp
  rw [sampleLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    word_bind_continuation, freezeAttach_prefix_law, hlen,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length, hc] with s hs hc
  exact stateSampleLaw_long s hs hc n

/-- Both original finite-word tree laws are realized on one actual sample. -/
theorem full_state_coupling (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (sampleLaw xs n).map (baselineState xs.length n) =
        Forward.treeLaw (xs ++ List.replicate n true).toSigns (xs ++ List.replicate n true).length ∧
      (sampleLaw xs n).map (longState xs.length n) =
        Forward.treeLaw ((xs ++ [false, true]) ++ List.replicate n true).toSigns
          ((xs ++ [false, true]) ++ List.replicate n true).length :=
  ⟨sampleLaw_baseline xs n hc, sampleLaw_long xs n hc⟩

end FreezingGrowth.TwoSeedGraft
