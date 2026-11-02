module

public import FreezingGrowth.RRTSplitLumping
public import FreezingGrowth.ReverseIndexedKernel

/-! A full-state two-seed continuation driven by one actual master RRT.
The forced first edge is omitted. The remaining births retain their global
order, so no independent shuffle of component labels is introduced. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical

def embedding (T u v : ℕ) : ℕ → ℕ
  | 0 => u
  | 1 => v
  | j + 2 => T + j + 1

theorem embedding_injective {T u v : ℕ} (hu : u ≤ T) (hv : v ≤ T) (huv : u ≠ v) :
    Function.Injective (embedding T u v) := by
  intro a b he
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;>
    simp only [embedding] at he <;> omega

def replay (s : Forward.State) (T u v : ℕ) (parent : ℕ → ℕ) : ℕ → Forward.State
  | 0 => s
  | n + 1 => Forward.attach (replay s T u v parent n) (T + n + 1)
      (embedding T u v (parent (n + 2)))

theorem replay_congr (s : Forward.State) (T u v n : ℕ) {p q : ℕ → ℕ}
    (hpq : ∀ j, 2 ≤ j → j ≤ n + 1 → p j = q j) :
    replay s T u v p n = replay s T u v q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replay, replay, ih (fun j hj hj' => hpq j hj (by omega)), hpq (n + 2) (by omega) le_rfl]

theorem replay_attach (s r : Forward.State) (T u v n a : ℕ) :
    replay s T u v (Forward.attach r (n + 2) a).parent (n + 1) =
      Forward.attach (replay s T u v r.parent n) (T + n + 1) (embedding T u v a) := by
  have hpre : replay s T u v (Forward.attach r (n + 2) a).parent n =
      replay s T u v r.parent n := by
    apply replay_congr
    intro j _ hj
    exact Function.update_of_ne (by omega) _ _
  rw [replay, hpre]
  simp only [Forward.attach, Function.update_self]

theorem replay_active (s : Forward.State) (T u v : ℕ) (hs : s.active = {u, v})
    (p : ℕ → ℕ) (n : ℕ) :
    (replay s T u v p n).active = (Finset.range (n + 2)).image (embedding T u v) := by
  induction n with
  | zero => simp [replay, hs, Finset.range_add_one, embedding, Finset.pair_comm]
  | succ n ih =>
    change insert (T + n + 1) (replay s T u v p n).active = _
    have hrange : Finset.range (n + 1 + 2) = insert (n + 2) (Finset.range (n + 2)) := by
      convert (Finset.range_add_one (n := n + 2)) using 1
    rw [ih, hrange, Finset.image_insert]
    rfl

noncomputable def continuationLaw (s : Forward.State) (T : ℕ) : ℕ → Measure Forward.State
  | 0 => Measure.dirac s
  | n + 1 => (continuationLaw s T n).bind (fun q => Forward.transitionLaw q (T + n + 1) true)

instance continuationLaw_probability (s : Forward.State) (T n : ℕ) :
    IsProbabilityMeasure (continuationLaw s T n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac s))
  | succ n ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall (fun q => Forward.transitionLaw_probability q _ true))

theorem map_transition_replay (s r : Forward.State) {T u v n : ℕ}
    (hu : u ≤ T) (hv : v ≤ T) (huv : u ≠ v) (hs : s.active = {u, v})
    (hr : r.active = Finset.range (n + 2)) :
    (Forward.transitionLaw r (n + 2) true).map
        (fun q => replay s T u v q.parent (n + 1)) =
      Forward.transitionLaw (replay s T u v r.parent n) (T + n + 1) true := by
  let q := replay s T u v r.parent n
  let e := embedding T u v
  have hqa : q.active = (Finset.range (n + 2)).image e := replay_active s T u v hs r.parent n
  have hrne : r.active.Nonempty := by rw [hr]; exact ⟨0, by simp⟩
  have hqne : q.active.Nonempty := by
    rw [hqa]
    exact Finset.image_nonempty.mpr ⟨0, by simp⟩
  have he (a : ℕ) (ha : a ∈ Finset.range (n + 2)) : e a ∈ q.active := by
    rw [hqa]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hmaster : (Forward.transitionLaw r (n + 2) true).map
      (fun z => replay s T u v z.parent (n + 1)) =
      (Measure.uniformOfFinset (Finset.range (n + 2))).map
        (fun a => Forward.attach q (T + n + 1) (e a)) := by
    rw [Forward.transitionLaw, ite_eq_left hrne, Measure.map_map
      measurable_from_top (measurable_of_countable _), hr]
    apply Measure.map_congr
    filter_upwards [RRTSplit.uniform_ae_mem (Finset.range (n + 2))] with a ha
    have har : a ∈ r.active := by rwa [hr]
    simpa only [Function.comp_def, Forward.step, ite_eq_left har,
      ↓reduceIte, q, e] using replay_attach s r T u v n a
  have hseed : Forward.transitionLaw q (T + n + 1) true =
      (Measure.uniformOfFinset (Finset.range (n + 2))).map
        (fun a => Forward.attach q (T + n + 1) (e a)) := by
    rw [Forward.transitionLaw, ite_eq_left hqne, hqa,
      ← map_uniformOfFinset_of_injOn (Finset.range (n + 2)) e (measurable_of_countable _)
        (embedding_injective hu hv huv).injOn,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    apply Measure.map_congr
    filter_upwards [RRTSplit.uniform_ae_mem (Finset.range (n + 2))] with a ha
    simp only [Function.comp_def, Forward.step, ite_eq_left (he a ha), ↓reduceIte]
  exact hmaster.trans hseed.symm

/-- Exact full-state continuation under one independent actual master tree. -/
theorem masterTree_replay_law (s : Forward.State) {T u v : ℕ}
    (hu : u ≤ T) (hv : v ≤ T) (huv : u ≠ v) (hs : s.active = {u, v}) (n : ℕ) :
    (Forward.treeLaw RRT.allAttach (n + 1)).map (fun r => replay s T u v r.parent n) =
      continuationLaw s T n := by
  induction n with
  | zero =>
    rw [RRTSplit.treeLaw_one, Measure.map_dirac' measurable_from_top]
    rfl
  | succ n ih =>
    change ((Forward.treeLaw RRT.allAttach (n + 1)).bind
      (fun r => Forward.transitionLaw r (n + 2) true)).map
        (fun r => replay s T u v r.parent (n + 1)) = _
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      continuationLaw]
    calc
      _ = (Forward.treeLaw RRT.allAttach (n + 1)).bind
          (fun r => Forward.transitionLaw (replay s T u v r.parent n) (T + n + 1) true) := by
        apply Measure.bind_congr_right
        filter_upwards [RRTSplit.treeLaw_split_describes n] with r hr
        exact map_transition_replay s r hu hv huv hs hr.active
      _ = ((Forward.treeLaw RRT.allAttach (n + 1)).map
          (fun r => replay s T u v r.parent n)).bind
            (fun q => Forward.transitionLaw q (T + n + 1) true) :=
        (Measure.bind_map (m := Forward.treeLaw RRT.allAttach (n + 1))
          (f := fun r => replay s T u v r.parent n)
          (g := fun q => Forward.transitionLaw q (T + n + 1) true)
          measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
      _ = _ := by rw [ih]

end FreezingGrowth.TwoSeedGraft
