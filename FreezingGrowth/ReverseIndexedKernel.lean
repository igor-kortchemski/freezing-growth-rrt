module

/- The finite-uniform pushforward lemma is adapted from the local freezing1
   companion project's CanonicalUniformSampling.lean (Apache-2.0).
   See NOTICE for provenance. -/

public import FreezingGrowth.ReverseRootedForestLaw
public import Mathlib.Data.Fintype.EquivFin

/-!
# Uniform list positions and uniform component roots

Algorithm 2 chooses an ordered pair of distinct positions in the forest list.
A bijective root enumeration turns this exactly into the root-pair kernel of
the graph-valued construction. The second selected component is attached below
the first selected root. Thus the one-step law is independent of the chosen
enumeration. The complete ordered process and delayed-pair coupling remain
separate constructions.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

/-- Injective finite relabelling preserves the actual uniform measure. -/
theorem map_uniformOfFinset_of_injOn {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DecidableEq β]
    (s : Finset α) (f : α → β) (hf : Measurable f) (hinj : Set.InjOn f s) :
    (Measure.uniformOfFinset s).map f = Measure.uniformOfFinset (s.image f) := by
  ext E hE
  rw [Measure.map_apply hf hE, Measure.uniformOfFinset_apply, Measure.uniformOfFinset_apply]
  have hfilter : (s.image f).filter (fun y => y ∈ E) =
      (s.filter fun a => f a ∈ E).image f := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, he⟩
      exact ⟨a, ⟨ha, he⟩, rfl⟩
    · rintro ⟨a, ⟨ha, he⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, he⟩
  rw [hfilter, Finset.card_image_iff.mpr hinj,
    Finset.card_image_iff.mpr (hinj.mono (by intro a ha; exact (Finset.mem_filter.mp ha).1))]
  rfl

namespace RootedForest

variable {V : Type*} [DecidableEq V]

/-- A list-position indexing of the distinct component roots. -/
abbrev RootEnumeration (F : RootedForest V) :=
  Fin F.roots.card ≃ {r // r ∈ F.roots}

/-- Interpret both indices in their original order. -/
def indexedPair (F : RootedForest V) (e : F.RootEnumeration)
    (p : Fin F.roots.card × Fin F.roots.card) : V × V :=
  ((e p.1).val, (e p.2).val)

theorem indexedPair_injective (F : RootedForest V) (e : F.RootEnumeration) :
    Function.Injective (F.indexedPair e) := by
  intro p q hp
  apply Prod.ext
  · apply e.injective
    exact Subtype.ext (congrArg Prod.fst hp)
  · apply e.injective
    exact Subtype.ext (congrArg Prod.snd hp)

/-- Distinct list positions enumerate exactly the ordered distinct root pairs. -/
theorem indexedPair_image (F : RootedForest V) (e : F.RootEnumeration) :
    ((Finset.univ : Finset (Fin F.roots.card)).offDiag.image (F.indexedPair e)) =
      F.roots.offDiag := by
  ext p
  constructor
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨_, _, hne⟩ := Finset.mem_offDiag.mp hq
    apply Finset.mem_offDiag.mpr
    refine ⟨(e q.1).property, (e q.2).property, ?_⟩
    intro he
    exact hne (e.injective (Subtype.ext he))
  · intro hp
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
    refine Finset.mem_image.mpr
      ⟨(e.symm ⟨p.1, ha⟩, e.symm ⟨p.2, hb⟩), ?_, ?_⟩
    · apply Finset.mem_offDiag.mpr
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
      intro he
      have hh := congrArg (fun i => (e i).val) he
      apply hne
      simpa using hh
    · simp [indexedPair]

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [Countable V] in
/-- Uniformly selecting distinct indices gives precisely the root-pair law. -/
theorem map_uniformRootPair_indexedPair (F : RootedForest V) (e : F.RootEnumeration) :
    (uniformRootPair (Finset.univ : Finset (Fin F.roots.card))).map (F.indexedPair e) =
      uniformRootPair F.roots := by
  unfold uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
    (F.indexedPair_injective e).injOn, F.indexedPair_image e]

/-- Algorithm 2's indexed one-step grafting operation, on an arbitrary root
enumeration. The identity branch merely totalizes illegal small-root inputs. -/
noncomputable def indexedJoinLaw (F : RootedForest V) (e : F.RootEnumeration) :
    Measure (RootedForest V) :=
  if 2 ≤ F.roots.card then
    (uniformRootPair (Finset.univ : Finset (Fin F.roots.card))).map
      (fun p => F.joinChoice (F.indexedPair e p))
  else Measure.dirac F

/-- The exact one-step projection from ordered indices to the graph kernel. -/
theorem indexedJoinLaw_eq_joinLaw (F : RootedForest V) (e : F.RootEnumeration) :
    F.indexedJoinLaw e = F.joinLaw := by
  unfold indexedJoinLaw joinLaw
  split_ifs
  · change (uniformRootPair (Finset.univ : Finset (Fin F.roots.card))).map
        (F.joinChoice ∘ F.indexedPair e) = _
    rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      F.map_uniformRootPair_indexedPair e]
  · rfl

/-- Reordering the component list cannot change the projected one-step law. -/
theorem indexedJoinLaw_order_independent (F : RootedForest V)
    (e₁ e₂ : F.RootEnumeration) : F.indexedJoinLaw e₁ = F.indexedJoinLaw e₂ := by
  rw [F.indexedJoinLaw_eq_joinLaw e₁, F.indexedJoinLaw_eq_joinLaw e₂]

end RootedForest
end FreezingGrowth
