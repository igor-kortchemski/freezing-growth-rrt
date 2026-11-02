module

public import FreezingGrowth.ReverseShorterHistoryLaw
public import FreezingGrowth.ReverseRootedForestRelabel

/-! Full label transport of the ordered reverse algorithm. Both ordered
components and their complete rooted graphs are transported. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical

theorem uniformRootPair_map_equiv {V W : Type*} [DecidableEq V] [DecidableEq W]
    [MeasurableSpace V] [MeasurableSpace W] [MeasurableSingletonClass V]
    [MeasurableSingletonClass W] [Countable V]
    (s : Finset V) (e : V ≃ W) :
    (uniformRootPair s).map (Prod.map e e) = uniformRootPair (s.map e.toEmbedding) := by
  have hinj : Function.Injective (Prod.map e e) := (Equiv.prodCongr e e).injective
  have himage : s.offDiag.image (Prod.map e e) = (s.map e.toEmbedding).offDiag := by
    ext p
    obtain ⟨a, ha⟩ := e.surjective p.1
    obtain ⟨b, hb⟩ := e.surjective p.2
    have hp : p = (e a, e b) := Prod.ext ha.symm hb.symm
    rw [hp]
    simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, e.injective.ne_iff]
    constructor
    · rintro ⟨q, hq, he⟩
      have hqa : q.1 = a := e.injective (congrArg Prod.fst he)
      have hqb : q.2 = b := e.injective (congrArg Prod.snd he)
      simpa only [hqa, hqb] using hq
    · intro hab
      exact ⟨(a, b), hab, rfl⟩
  unfold uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _) hinj.injOn, himage]

namespace ReverseOrdered

def relabel (F : Forest) (e : Label ≃ Label) : Forest where
  forest := F.forest.relabel e
  rootOrder := F.rootOrder.map e
  rootOrder_nodup := F.rootOrder_nodup.map e.injective
  rootOrder_roots := by
    rw [RootedForest.relabel_roots]
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    simp [← mem_rootOrder F]

theorem relabel_roots_card (F : Forest) (e : Label ≃ Label) :
    (relabel F e).forest.roots.card = F.forest.roots.card := by
  simp only [relabel, RootedForest.relabel_roots, Finset.card_map]

theorem relabel_pair_mem (F : Forest) (e : Label ≃ Label) (p : Label × Label) :
    (e p.1, e p.2) ∈ (relabel F e).forest.roots.offDiag ↔ p ∈ F.forest.roots.offDiag := by
  simp [relabel, RootedForest.relabel_roots, Finset.mem_offDiag]

theorem relabel_joinChoice (F : Forest) (e : Label ≃ Label) (p : Label × Label) :
    relabel (joinChoice F p) e = joinChoice (relabel F e) (e p.1, e p.2) := by
  by_cases hp : p ∈ F.forest.roots.offDiag
  · have hp' := (relabel_pair_mem F e p).mpr hp
    rw [joinChoice, dite_eq_left hp, joinChoice, dite_eq_left hp']
    apply Forest.ext_data
    · exact F.forest.relabel_join e (Finset.mem_offDiag.mp hp).1
        (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2
    · change (F.rootOrder.filter (fun r => decide (r ≠ p.2))).map e =
        (F.rootOrder.map e).filter (fun r => decide (r ≠ e p.2))
      rw [List.filter_map]
      congr 2
      funext v
      simp only [Function.comp_apply, e.injective.ne_iff]
  · have hp' := mt (relabel_pair_mem F e p).mp hp
    simp only [joinChoice, dite_eq_right hp, dite_eq_right hp']

theorem relabel_insertLabel (F : Forest) (e : Label ≃ Label) (i j : ℕ)
    (he : e (.inr i) = .inr j) :
    relabel (insertLabel F i) e = insertLabel (relabel F e) j := by
  have hmem : Sum.inr j ∈ (relabel F e).forest.vertices ↔ Sum.inr i ∈ F.forest.vertices := by
    rw [← he]
    exact F.forest.relabel_mem_vertices e (.inr i)
  by_cases hi : Sum.inr i ∈ F.forest.vertices
  · simp only [insertLabel, dite_eq_left hi, dite_eq_left (hmem.mpr hi)]
  · have hj := mt hmem.mp hi
    rw [insertLabel, dite_eq_right hi, insertLabel, dite_eq_right hj]
    apply Forest.ext_data
    · exact (F.forest.relabel_adjoin e hi).trans (by congr 1)
    · change (F.rootOrder ++ [(Sum.inr i : Label)]).map e =
        F.rootOrder.map e ++ [(Sum.inr j : Label)]
      simp only [List.map_append, List.map_cons, List.map_nil, he]

theorem relabel_joinLaw (F : Forest) (e : Label ≃ Label) :
    (joinLaw F).map (fun G => relabel G e) = joinLaw (relabel F e) := by
  unfold joinLaw
  rw [relabel_roots_card]
  split_ifs with hF
  · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    have hr : (relabel F e).forest.roots = F.forest.roots.map e.toEmbedding :=
      RootedForest.relabel_roots F.forest e
    rw [hr, ← uniformRootPair_map_equiv F.forest.roots e,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext p
    exact relabel_joinChoice F e p
  · exact Measure.map_dirac' measurable_from_top _

theorem relabel_maxDepth (F : Forest) (e : Label ≃ Label) :
    (relabel F e).forest.maxDepth = F.forest.maxDepth := by
  simp only [RootedForest.maxDepth, relabel, RootedForest.relabel, Finset.sup_map]
  congr 1
  funext w
  change F.forest.depth (e.symm (e w)) = F.forest.depth w
  rw [Equiv.symm_apply_apply]

end ReverseOrdered
end FreezingGrowth
