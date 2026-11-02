module

public import FreezingGrowth.TaggedGraftBranches

/-! The complete labelled attach/freeze coupling. One old state, one ordered
active pair, and one independent master tree are shared by the baseline and
all three branches. A separate independent uniform case selects the actual
attach/freeze word. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical ENNReal

structure TaggedSample where
  base : Sample
  tag : Fin 3

instance : MeasurableSpace TaggedSample := ⊤
instance : DiscreteMeasurableSpace TaggedSample := ⟨fun _ => trivial⟩

noncomputable def taggedLaw (μ : Measure Sample) : Measure TaggedSample :=
  μ.bind (fun z => TwoSeedCoupling.threeCaseLaw.map (fun c => ⟨z, c⟩))

noncomputable def taggedSampleLaw (xs : Word) (n : ℕ) : Measure TaggedSample :=
  taggedLaw (sampleLaw xs n)

def taggedBaseline (T n : ℕ) (z : TaggedSample) : Forward.State := baselineState T n z.base

def taggedLong (T n : ℕ) (z : TaggedSample) : Forward.State := caseState T n z.tag z.base

theorem taggedLaw_probability (μ : Measure Sample) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (taggedLaw μ) := by
  unfold taggedLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  exact Filter.Eventually.of_forall (fun z =>
    Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance)

theorem taggedLaw_base (μ : Measure Sample) : (taggedLaw μ).map TaggedSample.base = μ := by
  rw [taggedLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = μ.bind Measure.dirac := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only
        rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
        change TwoSeedCoupling.threeCaseLaw.map (fun _ => z) = Measure.dirac z
        rw [Measure.map_const, measure_univ, one_smul])
    _ = μ := Measure.bind_dirac

/-- The tag is independent of the entire old-state/pair/master sample. -/
theorem taggedLaw_joint (μ : Measure Sample) :
    (taggedLaw μ).map (fun z => (z.base, z.tag)) = μ.prod TwoSeedCoupling.threeCaseLaw := by
  rw [taggedLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.prod_eq_of_sfinite]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    rfl)

theorem taggedLaw_map (μ : Measure Sample) (f : Sample → Fin 3 → Forward.State) :
    (taggedLaw μ).map (fun z => f z.base z.tag) =
      μ.bind (fun z => TwoSeedCoupling.threeCaseLaw.map (f z)) := by
  rw [taggedLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    rfl)

private theorem bind_case_master (n : ℕ) (f : Forward.State → Fin 3 → Forward.State) :
    (Forward.treeLaw RRT.allAttach (n + 1)).bind
        (fun r => TwoSeedCoupling.threeCaseLaw.map (f r)) =
      TwoSeedCoupling.threeCaseLaw.bind
        (fun c => (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => f r c)) := by
  calc
    _ = (Forward.treeLaw RRT.allAttach (n + 1)).bind
        (fun r => TwoSeedCoupling.threeCaseLaw.bind (fun c => Measure.dirac (f r c))) := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun r =>
        (Measure.bind_dirac_eq_map _ (measurable_of_countable _)).symm)
    _ = TwoSeedCoupling.threeCaseLaw.bind
        (fun c => (Forward.treeLaw RRT.allAttach (n + 1)).bind (fun r => Measure.dirac (f r c))) :=
      Measure.bind_comm (measurable_from_prod_countable_left (fun _ => measurable_from_top))
    _ = _ := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun c => Measure.bind_dirac_eq_map _ measurable_from_top)

theorem orderedPair_attachment (s : Forward.State) (T : ℕ) (hc : s.active.card = 2) :
    (uniformRootPair s.active).map (fun p => Forward.attach s (T + 1) p.1) =
      Forward.transitionLaw s (T + 1) true := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
  have ha : a ∈ s.active := by rw [hs]; simp
  have hb : b ∈ s.active := by rw [hs]; simp
  rw [transition_pair s (T + 1) true hs hab, hs, uniformRootPair_pair a b hab,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _), Measure.map_dirac' (measurable_of_countable _)]
  simp only [Forward.step, ite_eq_left ha, ite_eq_left hb, ↓reduceIte]

theorem attach_freeze_pair (s : Forward.State) {T : ℕ} (hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) :
    (uniformRootPair s.active).bind
        (fun p => TwoSeedCoupling.threeCaseLaw.map (casePrefix s T p.1 p.2)) =
      (Forward.transitionLaw s (T + 1) true).bind
        (fun q => Forward.transitionLaw q (T + 2) false) := by
  rw [← orderedPair_attachment s T hc,
    Measure.bind_map (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
  exact threeCaseLaw_casePrefix hs (active_eq_pair_of_card_two hc hp) (Finset.mem_offDiag.mp hp).2.2

theorem stateTaggedLaw_long (s : Forward.State) {T : ℕ} (hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) (n : ℕ) :
    (taggedLaw (stateSampleLaw s n)).map (taggedLong T n) =
      ((Forward.transitionLaw s (T + 1) true).bind
        (fun q => Forward.transitionLaw q (T + 2) false)).bind
          (fun q => continuationLaw q (T + 2) n) := by
  change (taggedLaw (stateSampleLaw s n)).map (fun z => caseState T n z.tag z.base) = _
  rw [taggedLaw_map _ (fun z c => caseState T n c z), stateSampleLaw,
    Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    ← attach_freeze_pair s hs hc,
    Measure.bind_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag s.active] with p hp
  have ha := active_eq_pair_of_card_two hc hp
  have hne := (Finset.mem_offDiag.mp hp).2.2
  rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.bind_map (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable,
    bind_case_master]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun c => masterTree_caseState_law hs ha hne n c)

theorem attachFreeze_prefix_law (xs : Word) :
    Forward.treeLaw (xs ++ [true, false]).toSigns (xs ++ [true, false]).length =
      (Forward.treeLaw xs.toSigns xs.length).bind (fun s =>
        (Forward.transitionLaw s (xs.length + 1) true).bind
          (fun q => Forward.transitionLaw q (xs.length + 2) false)) := by
  let x := (xs ++ [true, false]).toSigns
  have ht : x (xs.length + 1) = true := by
    simpa only [x, Nat.add_zero, Word.toSigns_succ, List.getElem?_cons_zero, Option.getD_some] using
      Word.toSigns_append_right xs [true, false] 0
  have hf : x (xs.length + 2) = false := by
    simpa only [x, Word.toSigns_succ, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some] using
      Word.toSigns_append_right xs [true, false] 1
  have hp : Forward.treeLaw x xs.length = Forward.treeLaw xs.toSigns xs.length :=
    Forward.treeLaw_congr (fun i hi => Word.toSigns_append_left xs [true, false] hi)
  rw [List.length_append]
  change Forward.treeLaw x ((xs.length + 1) + 1) = _
  rw [Forward.treeLaw, hf, Forward.treeLaw, ht, hp,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]

theorem taggedSampleLaw_long (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (taggedSampleLaw xs n).map (taggedLong xs.length n) =
      Forward.treeLaw ((xs ++ [true, false]) ++ List.replicate n true).toSigns
        ((xs ++ [true, false]) ++ List.replicate n true).length := by
  have hlen : (xs ++ [true, false]).length = xs.length + 2 := by simp
  change (taggedLaw (sampleLaw xs n)).map (fun z => caseState xs.length n z.tag z.base) = _
  rw [taggedLaw_map _ (fun z c => caseState xs.length n c z), sampleLaw,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    word_bind_continuation, attachFreeze_prefix_law, hlen,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length, hc] with s hs hc
  rw [← taggedLaw_map _ (fun z c => caseState xs.length n c z)]
  exact stateTaggedLaw_long s hs hc n

theorem taggedSampleLaw_baseline (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    (taggedSampleLaw xs n).map (taggedBaseline xs.length n) =
      Forward.treeLaw (xs ++ List.replicate n true).toSigns
        (xs ++ List.replicate n true).length := by
  have h := congrArg (fun μ => μ.map (baselineState xs.length n)) (taggedLaw_base (sampleLaw xs n))
  rw [Measure.map_map measurable_from_top measurable_from_top, sampleLaw_baseline xs n hc] at h
  exact h

/-- Both actual full labelled tree laws, with all frozen data, are realized on
the same old-state/pair/master/tag space. -/
theorem tagged_full_state_coupling (xs : Word) (n : ℕ)
    (hc : ∀ᵐ s ∂Forward.treeLaw xs.toSigns xs.length, s.active.card = 2) :
    IsProbabilityMeasure (taggedSampleLaw xs n) ∧
      (taggedSampleLaw xs n).map (taggedBaseline xs.length n) =
        Forward.treeLaw (xs ++ List.replicate n true).toSigns
          (xs ++ List.replicate n true).length ∧
      (taggedSampleLaw xs n).map (taggedLong xs.length n) =
        Forward.treeLaw ((xs ++ [true, false]) ++ List.replicate n true).toSigns
          ((xs ++ [true, false]) ++ List.replicate n true).length := by
  let := sampleLaw_probability xs n (hc.mono (fun _ h => by omega))
  exact ⟨taggedLaw_probability _, taggedSampleLaw_baseline xs n hc, taggedSampleLaw_long xs n hc⟩

end FreezingGrowth.TwoSeedGraft
