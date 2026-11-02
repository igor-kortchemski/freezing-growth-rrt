module

public import FreezingGrowth.ReverseOrderedForest
public import FreezingGrowth.ReverseDistinguishedPair

/-! The graph-faithful initialization of Algorithm 3. The distinguished
singleton is placed first; its first use changes only the component ordering
relative to the usual graph join. The sampled list positions are retained. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

namespace RootedForest

variable {V : Type*} [DecidableEq V]

/-- The component with root `d` consists of the single vertex `d`. -/
def IsSingletonRoot (F : RootedForest V) (d : V) : Prop :=
  d ∈ F.roots ∧ ∀ v ∈ F.vertices, F.root v = d → v = d

theorem isSingletonRoot_adjoin (F : RootedForest V) {d : V} (hd : d ∉ F.vertices) :
    IsSingletonRoot (F.adjoin d hd) d := by
  constructor
  · rw [adjoin_roots]
    exact Finset.mem_insert_self _ _
  · intro v hv hr
    by_cases he : v = d
    · exact he
    · have hvold : v ∈ F.vertices := (Finset.mem_insert.mp hv).resolve_left he
      simp only [adjoin, he, ↓reduceIte] at hr
      exact False.elim (hd (hr ▸ F.root_mem v hvold))

theorem isSingletonRoot_join_iff (F : RootedForest V) {d a b : V}
    (hd : F.IsSingletonRoot d) (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b) :
    (F.join a b ha hb hab).IsSingletonRoot d ↔ a ≠ d ∧ b ≠ d := by
  constructor
  · intro hj
    have hbd : b ≠ d := by
      have hh := hj.1
      rw [join_roots] at hh
      exact (Finset.mem_erase.mp hh).1.symm
    refine ⟨?_, hbd⟩
    intro had
    have hr : (F.join a b ha hb hab).root b = d := by
      simp [join, (mem_roots.mp hb).2, had]
    exact hbd (hj.2 b (mem_roots.mp hb).1 hr)
  · rintro ⟨had, hbd⟩
    constructor
    · rw [join_roots]
      exact Finset.mem_erase.mpr ⟨hbd.symm, hd.1⟩
    · intro v hv hr
      change (if F.root v = b then a else F.root v) = d at hr
      split_ifs at hr with hvb
      · exact False.elim (had hr)
      · exact hd.2 v hv hr

theorem isSingletonRoot_joinChoice_iff (F : RootedForest V) {d : V}
    (hd : F.IsSingletonRoot d) {p : V × V} (hp : p ∈ F.roots.offDiag) :
    (F.joinChoice p).IsSingletonRoot d ↔ p ∈ avoidsDistinguished d := by
  rw [joinChoice, dite_eq_left hp]
  exact isSingletonRoot_join_iff F hd (Finset.mem_offDiag.mp hp).1
    (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2

end RootedForest

namespace ReverseOrdered

abbrev Label := ℕ ⊕ ℕ

/-- The same fresh labelled singleton as Algorithm 2, at the front of the list. -/
def prependLabel (F : Forest) (i : ℕ) : Forest :=
  if h : Sum.inr i ∈ F.forest.vertices then F else
    { forest := F.forest.adjoin (.inr i) h
      rootOrder := .inr i :: F.rootOrder
      rootOrder_nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_, F.rootOrder_nodup⟩
        intro hm
        exact h (RootedForest.mem_roots.mp ((mem_rootOrder F _).mp hm)).1
      rootOrder_roots := by
        rw [RootedForest.adjoin_roots]
        simp [F.rootOrder_roots] }

theorem prependLabel_forest (F : Forest) (i : ℕ) :
    (prependLabel F i).forest = Reverse.insertLabel F.forest i := by
  unfold prependLabel Reverse.insertLabel
  split_ifs <;> rfl

theorem prependLabel_rootOrder (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    (prependLabel F i).rootOrder = .inr i :: F.rootOrder := by
  simp [prependLabel, hi]

theorem prependLabel_roots_card (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    (prependLabel F i).forest.roots.card = F.forest.roots.card + 1 := by
  simpa only [prependLabel, dite_eq_right hi] using RootedForest.adjoin_card_roots F.forest hi

private theorem swap_mem_roots_iff (F : Forest) {a b v : Label}
    (ha : a ∈ F.forest.roots) (hb : b ∈ F.forest.roots) :
    Equiv.swap a b v ∈ F.forest.roots ↔ v ∈ F.forest.roots := by
  by_cases hva : v = a
  · subst v
    simp [ha, hb]
  · by_cases hvb : v = b
    · subst v
      simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hva hvb]

/-- Swap two component positions, leaving every labelled edge unchanged. -/
def swapRootPositions (F : Forest) (a b : Label)
    (ha : a ∈ F.forest.roots) (hb : b ∈ F.forest.roots) : Forest where
  forest := F.forest
  rootOrder := F.rootOrder.map (Equiv.swap a b)
  rootOrder_nodup := List.Nodup.map (Equiv.swap a b).injective F.rootOrder_nodup
  rootOrder_roots := by
    ext v
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (swap_mem_roots_iff F ha hb).mpr ((mem_rootOrder F _).mp hu)
    · intro hv
      refine ⟨Equiv.swap a b v, (mem_rootOrder F _).mpr
        ((swap_mem_roots_iff F ha hb).mpr hv), ?_⟩
      simp

/-- Source case (ii) moves the retained zero-th root to the other chosen
component's old position. The root-to-root graph graft is unchanged. -/
def distinguishedJoinChoice (F : Forest) (d : Label) (p : Label × Label) : Forest :=
  if hp : p ∈ F.forest.roots.offDiag then
    if p.1 = d then
      joinChoice (swapRootPositions F p.1 p.2 (Finset.mem_offDiag.mp hp).1
        (Finset.mem_offDiag.mp hp).2.1) p
    else joinChoice F p
  else F

theorem distinguishedJoinChoice_forest (F : Forest) (d : Label) (p : Label × Label) :
    (distinguishedJoinChoice F d p).forest = F.forest.joinChoice p := by
  unfold distinguishedJoinChoice
  split_ifs with hp hd
  · rw [joinChoice_forest]
    rfl
  · exact joinChoice_forest F p
  · simp [RootedForest.joinChoice, hp]

theorem distinguishedJoinChoice_roots_card (F : Forest) (d : Label) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    (distinguishedJoinChoice F d p).forest.roots.card + 1 = F.forest.roots.card := by
  rw [distinguishedJoinChoice_forest, RootedForest.joinChoice, dite_eq_left hp]
  exact RootedForest.join_card_roots F.forest _ _ _

theorem distinguishedJoinChoice_singleton_iff (F : Forest) {d : Label}
    (hd : F.forest.IsSingletonRoot d) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) :
    (distinguishedJoinChoice F d p).forest.IsSingletonRoot d ↔
      p ∈ avoidsDistinguished d := by
  rw [distinguishedJoinChoice_forest]
  exact RootedForest.isSingletonRoot_joinChoice_iff F.forest hd hp

/-- In the avoidance case the distinguished component remains in position zero. -/
theorem distinguishedJoinChoice_avoids_rootOrder (F : Forest) {d : Label}
    {xs : List Label} (horder : F.rootOrder = d :: xs) {p : Label × Label}
    (hp : p ∈ F.forest.roots.offDiag) (hd : p ∈ avoidsDistinguished d) :
    (distinguishedJoinChoice F d p).rootOrder =
      d :: xs.filter (fun r => decide (r ≠ p.2)) := by
  rw [distinguishedJoinChoice, dite_eq_left hp, ite_eq_right hd.1, joinChoice_rootOrder F hp,
    horder]
  simp [hd.2.symm]

/-- If the distinguished singleton is the child, its list entry is removed. -/
theorem distinguishedJoinChoice_child_rootOrder (F : Forest) {d : Label}
    {xs : List Label} (horder : F.rootOrder = d :: xs) {a : Label}
    (hp : (a, d) ∈ F.forest.roots.offDiag) :
    (distinguishedJoinChoice F d (a, d)).rootOrder = xs := by
  have had : a ≠ d := (Finset.mem_offDiag.mp hp).2.2
  have hn : d ∉ xs := (List.nodup_cons.mp (horder ▸ F.rootOrder_nodup)).1
  rw [distinguishedJoinChoice, dite_eq_left hp, ite_eq_right had, joinChoice_rootOrder F hp,
    horder]
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  apply List.filter_eq_self.mpr
  intro v hv
  simp only [decide_eq_true_eq]
  exact fun he => hn (he ▸ hv)

/-- If the singleton receives a component, its retained root takes precisely
that component's former position; the old position zero disappears. -/
theorem distinguishedJoinChoice_receiver_rootOrder (F : Forest) {d : Label}
    {xs : List Label} (horder : F.rootOrder = d :: xs) {b : Label}
    (hp : (d, b) ∈ F.forest.roots.offDiag) :
    (distinguishedJoinChoice F d (d, b)).rootOrder = xs.map (Equiv.swap d b) := by
  have hn : d ∉ xs := (List.nodup_cons.mp (horder ▸ F.rootOrder_nodup)).1
  rw [distinguishedJoinChoice, dite_eq_left hp, ite_eq_left rfl]
  rw [joinChoice_rootOrder
    (swapRootPositions F d b (Finset.mem_offDiag.mp hp).1 (Finset.mem_offDiag.mp hp).2.1)
    (show (d, b) ∈ (swapRootPositions F d b (Finset.mem_offDiag.mp hp).1
      (Finset.mem_offDiag.mp hp).2.1).forest.roots.offDiag from hp)]
  change (F.rootOrder.map (Equiv.swap d b)).filter (fun r => decide (r ≠ b)) = _
  rw [horder]
  simp only [List.map_cons, Equiv.swap_apply_left, List.filter_cons, ne_eq,
    not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  apply List.filter_eq_self.mpr
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  simp only [decide_eq_true_eq]
  intro he
  have hwz : w = d := (Equiv.swap d b).injective
    (he.trans (Equiv.swap_apply_left d b).symm)
  exact hn (hwz ▸ hw)

noncomputable def distinguishedJoinLaw (F : Forest) (d : Label) : Measure Forest :=
  if 2 ≤ F.forest.roots.card then
    (uniformRootPair F.forest.roots).map (distinguishedJoinChoice F d)
  else Measure.dirac F

instance distinguishedJoinLaw_probability (F : Forest) (d : Label) :
    IsProbabilityMeasure (distinguishedJoinLaw F d) := by
  unfold distinguishedJoinLaw
  split_ifs with h
  · let := uniformRootPair_isProbabilityMeasure F.forest.roots h
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr
      inferInstance
  · infer_instance

/-- The order modification does not alter the one-step labelled-graph law. -/
theorem map_distinguishedJoinLaw (F : Forest) (d : Label) :
    (distinguishedJoinLaw F d).map Forest.forest = F.forest.joinLaw := by
  unfold distinguishedJoinLaw RootedForest.joinLaw
  split_ifs
  · rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 1
    funext p
    exact distinguishedJoinChoice_forest F d p
  · exact Measure.map_dirac' measurable_from_top _

structure InitializationSample where
  longer : Forest
  shorter : Forest
  used : Bool
  delayedPair : ℕ × ℕ

instance : MeasurableSpace InitializationSample := ⊤
instance : DiscreteMeasurableSpace InitializationSample := ⟨fun _ => trivial⟩

/-- The stored pair consists of the original positions, before the merge.
In the pending case these are the source's one-based shortened-list indices. -/
noncomputable def initializationChoice (F : Forest) (i : ℕ)
    (p : Fin (prependLabel F i).forest.roots.card ×
      Fin (prependLabel F i).forest.roots.card) : InitializationSample where
  longer := distinguishedJoinChoice (prependLabel F i) (.inr i)
    ((prependLabel F i).forest.indexedPair (rootEnumeration (prependLabel F i)) p)
  shorter := F
  used := decide (p.1.val = 0 ∨ p.2.val = 0)
  delayedPair := (p.1.val, p.2.val)

noncomputable def initializationLaw (F : Forest) (i : ℕ) : Measure InitializationSample :=
  (uniformRootPair (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card))).map
    (initializationChoice F i)

theorem initializationLaw_probability (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    IsProbabilityMeasure (initializationLaw F i) := by
  have hc : 2 ≤ (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin, prependLabel_roots_card F hi] using
      (show 2 ≤ F.forest.roots.card + 1 by omega)
  let := uniformRootPair_isProbabilityMeasure _ hc
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr
    inferInstance

theorem indexedPair_valid (F : Forest) (p : Fin F.forest.roots.card × Fin F.forest.roots.card)
    (hp : p.1 ≠ p.2) :
    F.forest.indexedPair (rootEnumeration F) p ∈ F.forest.roots.offDiag := by
  refine Finset.mem_offDiag.mpr ⟨(rootEnumeration F p.1).property,
    (rootEnumeration F p.2).property, ?_⟩
  intro he
  exact hp ((rootEnumeration F).injective (Subtype.ext he))

theorem rootEnumeration_prepend_eq (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (a : Fin (prependLabel F i).forest.roots.card) :
    (rootEnumeration (prependLabel F i) a).val = .inr i ↔ a.val = 0 := by
  have hpos : 0 < (prependLabel F i).forest.roots.card := by
    rw [prependLabel_roots_card F hi]
    omega
  let z : Fin (prependLabel F i).forest.roots.card := ⟨0, hpos⟩
  have hz : (rootEnumeration (prependLabel F i) z).val = .inr i := by
    rw [rootEnumeration_get]
    simp [z, prependLabel, hi]
  constructor
  · intro he
    exact congrArg Fin.val ((rootEnumeration (prependLabel F i)).injective
      (Subtype.ext (he.trans hz.symm)))
  · intro ha
    have he : a = z := Fin.ext ha
    simpa only [he] using hz

/-- The singleton/flag invariant and forest sizes of both initialization cases.
The pair is not renumbered after the longer forest's merge. -/
theorem initializationChoice_valid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin (prependLabel F i).forest.roots.card ×
      Fin (prependLabel F i).forest.roots.card) (hp : p.1 ≠ p.2) :
    (initializationChoice F i p).shorter = F ∧
    (initializationChoice F i p).longer.forest.roots.card = F.forest.roots.card ∧
    ((initializationChoice F i p).longer.forest.IsSingletonRoot (.inr i) ↔
      (initializationChoice F i p).used = false) ∧
    (initializationChoice F i p).delayedPair.1 ≤ F.forest.roots.card ∧
    (initializationChoice F i p).delayedPair.2 ≤ F.forest.roots.card ∧
    (initializationChoice F i p).delayedPair.1 ≠
      (initializationChoice F i p).delayedPair.2 := by
  have hpair := indexedPair_valid (prependLabel F i) p hp
  have hs : (prependLabel F i).forest.IsSingletonRoot (.inr i) := by
    simpa only [prependLabel, dite_eq_right hi] using RootedForest.isSingletonRoot_adjoin F.forest hi
  have hc := distinguishedJoinChoice_roots_card (prependLabel F i) (.inr i) hpair
  rw [prependLabel_roots_card F hi] at hc
  have hfirst : p.1.val < F.forest.roots.card + 1 :=
    p.1.isLt.trans_le (prependLabel_roots_card F hi).le
  have hsecond : p.2.val < F.forest.roots.card + 1 :=
    p.2.isLt.trans_le (prependLabel_roots_card F hi).le
  refine ⟨rfl, Nat.add_right_cancel hc, ?_, by simpa only [initializationChoice] using
    (show p.1.val ≤ F.forest.roots.card by omega), by simpa only [initializationChoice] using
    (show p.2.val ≤ F.forest.roots.card by omega), ?_⟩
  · change (distinguishedJoinChoice _ _ _).forest.IsSingletonRoot _ ↔
      decide (p.1.val = 0 ∨ p.2.val = 0) = false
    rw [distinguishedJoinChoice_singleton_iff _ hs hpair]
    simp only [avoidsDistinguished, Set.mem_ofPred_eq, RootedForest.indexedPair,
      decide_eq_false_iff_not, not_or]
    exact and_congr (not_congr (rootEnumeration_prepend_eq F hi p.1))
      (not_congr (rootEnumeration_prepend_eq F hi p.2))
  · exact fun he => hp (Fin.ext he)

/-- The first process has the actual Algorithm 2 graph transition at
initialization. This is a local marginal statement, not a history-independence claim. -/
theorem initializationLaw_longer_forest (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    (initializationLaw F i).map (fun z => z.longer.forest) =
      (Reverse.insertLabel F.forest i).joinLaw := by
  have hc : 2 ≤ (prependLabel F i).forest.roots.card := by
    rw [prependLabel_roots_card F hi]
    omega
  rw [initializationLaw, Measure.map_map measurable_from_top (measurable_of_countable _)]
  change (uniformRootPair _).map (fun p => (initializationChoice F i p).longer.forest) = _
  have he : (fun p => (initializationChoice F i p).longer.forest) =
      (fun p => (prependLabel F i).forest.joinChoice
        ((prependLabel F i).forest.indexedPair (rootEnumeration (prependLabel F i)) p)) := by
    funext p
    exact distinguishedJoinChoice_forest _ _ _
  rw [he, ← prependLabel_forest F i]
  simpa only [RootedForest.indexedJoinLaw, ite_eq_left hc] using
    (prependLabel F i).forest.indexedJoinLaw_eq_joinLaw (rootEnumeration (prependLabel F i))

end ReverseOrdered
end FreezingGrowth
