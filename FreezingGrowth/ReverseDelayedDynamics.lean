module

public import FreezingGrowth.ReverseDelayedMatching
public import FreezingGrowth.ReverseInitializationValidity
public import FreezingGrowth.ReversePositionPairs

/-! The actual delayed-pair state dynamics of Algorithm 3. Stored positive
positions are consumed only by the shorter forest, before the fresh pair is
sampled. Marginal history laws are separate from these state invariants. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

namespace RootedForest

variable {V : Type*} [DecidableEq V]

theorem joinChoice_vertices (F : RootedForest V) (p : V × V) :
    (F.joinChoice p).vertices = F.vertices := by
  unfold joinChoice
  split_ifs <;> rfl

/-- Merging components cannot create a new isolated singleton component. -/
theorem isSingletonRoot_of_join (F : RootedForest V) {d a b : V}
    (ha : a ∈ F.roots) (hb : b ∈ F.roots) (hab : a ≠ b)
    (h : (F.join a b ha hb hab).IsSingletonRoot d) : F.IsSingletonRoot d := by
  have hd := h.1
  rw [join_roots] at hd
  obtain ⟨hdb, hd⟩ := Finset.mem_erase.mp hd
  refine ⟨hd, ?_⟩
  intro v hv hr
  apply h.2 v hv
  simp [join, hr, hdb]

theorem isSingletonRoot_of_joinChoice (F : RootedForest V) {d : V} (p : V × V)
    (h : (F.joinChoice p).IsSingletonRoot d) : F.IsSingletonRoot d := by
  unfold joinChoice at h
  split_ifs at h with hp
  · exact isSingletonRoot_of_join F (Finset.mem_offDiag.mp hp).1
      (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2 h
  · exact h

end RootedForest

namespace ReverseOrdered

def LegalPositions (F : Forest) (p : ℕ × ℕ) : Prop :=
  p.1 < F.forest.roots.card ∧ p.2 < F.forest.roots.card ∧ p.1 ≠ p.2

/-- Graft at the actual zero-based list positions. The identity branch is
only a totalization outside the legal finite pair sampler. -/
noncomputable def joinPositions (F : Forest) (p : ℕ × ℕ) : Forest :=
  if hp : LegalPositions F p then
    joinChoice F (F.forest.indexedPair (rootEnumeration F)
      (⟨p.1, hp.1⟩, ⟨p.2, hp.2.1⟩))
  else F

theorem joinPositions_fin (F : Forest)
    (p : Fin F.forest.roots.card × Fin F.forest.roots.card) (hp : p.1 ≠ p.2) :
    joinPositions F (p.1.val, p.2.val) =
      joinChoice F (F.forest.indexedPair (rootEnumeration F) p) := by
  have hlegal : LegalPositions F (p.1.val, p.2.val) :=
    ⟨p.1.isLt, p.2.isLt, fun he => hp (Fin.ext he)⟩
  rw [joinPositions, dite_eq_left hlegal]

theorem joinPositions_vertices (F : Forest) (p : ℕ × ℕ) :
    (joinPositions F p).forest.vertices = F.forest.vertices := by
  unfold joinPositions
  split_ifs
  · rw [joinChoice_forest, RootedForest.joinChoice_vertices]
  · rfl

theorem joinPositions_card (F : Forest) {p : ℕ × ℕ} (hp : LegalPositions F p) :
    (joinPositions F p).forest.roots.card + 1 = F.forest.roots.card := by
  let q : Fin F.forest.roots.card × Fin F.forest.roots.card :=
    (⟨p.1, hp.1⟩, ⟨p.2, hp.2.1⟩)
  have hq : q.1 ≠ q.2 := fun he => hp.2.2 (congrArg Fin.val he)
  rw [joinPositions, dite_eq_left hp, joinChoice_forest, RootedForest.joinChoice,
    dite_eq_left (indexedPair_valid F q hq)]
  exact RootedForest.join_card_roots F.forest _ _ _

theorem isSingletonRoot_of_joinPositions (F : Forest) {d : Label} (p : ℕ × ℕ)
    (h : (joinPositions F p).forest.IsSingletonRoot d) : F.forest.IsSingletonRoot d := by
  unfold joinPositions at h
  split_ifs at h
  · rw [joinChoice_forest] at h
    exact RootedForest.isSingletonRoot_of_joinChoice F.forest _ h
  · exact h

noncomputable def consumeDelayed (z : InitializationSample) : Forest :=
  joinPositions z.shorter (z.delayedPair.1 - 1, z.delayedPair.2 - 1)

/-- Full geometric and original-position invariants while the pair is delayed. -/
structure DelayedValid (i N : ℕ) (z : InitializationSample) : Prop where
  longer_card : z.longer.forest.roots.card = N
  shorter_card : z.shorter.forest.roots.card = N
  fresh : Sum.inr i ∉ z.shorter.forest.vertices
  vertices : z.longer.forest.vertices = insert (.inr i) z.shorter.forest.vertices
  singleton_iff : z.longer.forest.IsSingletonRoot (.inr i) ↔ z.used = false
  pending : z.used = false →
    0 < z.delayedPair.1 ∧ 0 < z.delayedPair.2 ∧
    z.delayedPair.1 ≤ N ∧ z.delayedPair.2 ≤ N ∧
    z.delayedPair.1 ≠ z.delayedPair.2 ∧ z.longer = prependLabel (consumeDelayed z) i

theorem DelayedValid.consume_legal {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = false) :
    LegalPositions z.shorter (z.delayedPair.1 - 1, z.delayedPair.2 - 1) := by
  obtain ⟨ha, hb, haN, hbN, hne, _⟩ := hz.pending hu
  simp only [LegalPositions, hz.shorter_card]
  omega

theorem DelayedValid.consume_card {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = false) :
    (consumeDelayed z).forest.roots.card + 1 = N := by
  simpa only [consumeDelayed, hz.shorter_card] using joinPositions_card z.shorter (hz.consume_legal hu)

theorem DelayedValid.consume_fresh {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) : Sum.inr i ∉ (consumeDelayed z).forest.vertices := by
  simpa only [consumeDelayed, joinPositions_vertices] using hz.fresh

theorem DelayedValid.used_at_one {i : ℕ} {z : InitializationSample}
    (hz : DelayedValid i 1 z) : z.used = true := by
  by_cases hu : z.used = false
  · obtain ⟨ha, hb, haN, hbN, hne, _⟩ := hz.pending hu
    omega
  · cases h : z.used <;> simp_all

theorem initializationChoice_pending_joinPositions (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin (prependLabel F i).forest.roots.card × Fin (prependLabel F i).forest.roots.card)
    (hp : p.1 ≠ p.2) (ha : 0 < p.1.val) (hb : 0 < p.2.val) :
    (initializationChoice F i p).longer =
      prependLabel (joinPositions F (p.1.val - 1, p.2.val - 1)) i := by
  let a := lowerPositiveIndex F hi p.1 ha
  let b := lowerPositiveIndex F hi p.2 hb
  have hab : a ≠ b := by
    intro he
    apply hp
    calc
      p.1 = prependIndex F hi a := (prependIndex_lowerPositiveIndex F hi p.1 ha).symm
      _ = prependIndex F hi b := congrArg (prependIndex F hi) he
      _ = p.2 := prependIndex_lowerPositiveIndex F hi p.2 hb
  have hh := (initializationChoice_pending_matching F hi (a, b) hab).1
  rw [show prependIndex F hi a = p.1 from prependIndex_lowerPositiveIndex F hi p.1 ha,
    show prependIndex F hi b = p.2 from prependIndex_lowerPositiveIndex F hi p.2 hb,
    ← joinPositions_fin F (a, b) hab] at hh
  exact hh

theorem initializationChoice_delayedValid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices)
    (p : Fin (prependLabel F i).forest.roots.card × Fin (prependLabel F i).forest.roots.card)
    (hp : p.1 ≠ p.2) : DelayedValid i F.forest.roots.card (initializationChoice F i p) := by
  have hv := initializationChoice_valid_predicate F hi p hp
  obtain ⟨hl, hs, hflag, ha, hb, hne, hpos⟩ := hv
  refine ⟨hl, hs, hi, ?_, hflag, ?_⟩
  · change (distinguishedJoinChoice _ _ _).forest.vertices = _
    rw [distinguishedJoinChoice_forest, RootedForest.joinChoice_vertices]
    simp only [prependLabel, dite_eq_right hi, RootedForest.adjoin_vertices, initializationChoice]
  · intro hu
    have hh := hpos hu
    refine ⟨hh.1, hh.2, ha, hb, hne, ?_⟩
    exact initializationChoice_pending_joinPositions F hi p hp hh.1 hh.2

theorem initializationLaw_ae_delayedValid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    ∀ᵐ z ∂initializationLaw F i, DelayedValid i F.forest.roots.card z := by
  unfold initializationLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
  have hp : ∀ᵐ p ∂uniformRootPair
      (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)),
      p ∈ (Finset.univ : Finset (Fin (prependLabel F i).forest.roots.card)).offDiag := by
    rw [ae_iff]
    simp [uniformRootPair, Measure.uniformOfFinset_apply]
  filter_upwards [hp] with p hp
  exact initializationChoice_delayedValid F hi p (Finset.mem_offDiag.mp hp).2.2

noncomputable def synchronizedChoice (z : InitializationSample) (p : ℕ × ℕ) : InitializationSample :=
  ⟨joinPositions z.longer p, joinPositions z.shorter p, true, z.delayedPair⟩

theorem synchronizedChoice_valid {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = true) (p : ℕ × ℕ)
    (hp : p.1 < N ∧ p.2 < N ∧ p.1 ≠ p.2) :
    DelayedValid i (N - 1) (synchronizedChoice z p) := by
  have hl : LegalPositions z.longer p := by simpa only [LegalPositions, hz.longer_card] using hp
  have hs : LegalPositions z.shorter p := by simpa only [LegalPositions, hz.shorter_card] using hp
  have hlong := joinPositions_card z.longer hl
  have hshort := joinPositions_card z.shorter hs
  rw [hz.longer_card] at hlong
  rw [hz.shorter_card] at hshort
  constructor
  · change (joinPositions z.longer p).forest.roots.card = N - 1
    omega
  · change (joinPositions z.shorter p).forest.roots.card = N - 1
    omega
  · simpa only [synchronizedChoice, joinPositions_vertices] using hz.fresh
  · simpa only [synchronizedChoice, joinPositions_vertices] using hz.vertices
  · change (joinPositions z.longer p).forest.IsSingletonRoot (.inr i) ↔ true = false
    constructor
    · intro hh
      have hfalse := hz.singleton_iff.mp (isSingletonRoot_of_joinPositions z.longer p hh)
      rw [hu] at hfalse
      cases hfalse
    · intro hh
      cases hh
  · intro hh
    cases hh

noncomputable def synchronizedLaw (z : InitializationSample) : Measure InitializationSample :=
  (uniformRootPair (Finset.range z.shorter.forest.roots.card)).map (synchronizedChoice z)

theorem synchronizedLaw_probability (z : InitializationSample)
    (hz : 2 ≤ z.shorter.forest.roots.card) : IsProbabilityMeasure (synchronizedLaw z) := by
  let := uniformRootPair_isProbabilityMeasure (Finset.range z.shorter.forest.roots.card)
    (by simpa using hz)
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance

theorem synchronizedLaw_ae_valid {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = true) :
    ∀ᵐ z' ∂synchronizedLaw z, DelayedValid i (N - 1) z' := by
  unfold synchronizedLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable (by trivial)).mpr
  filter_upwards [ReverseHeightList.uniformRootPair_ae_offDiag
    (Finset.range z.shorter.forest.roots.card)] with p hp
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  apply synchronizedChoice_valid hz hu p
  simpa only [Finset.mem_range, hz.shorter_card] using And.intro ha (And.intro hb hab)

/-- Only valid states are asserted to have a probability transition. In the
pending branch, exact matching identifies the re-used initialization kernel
with the source fresh graft on the current longer forest. -/
noncomputable def delayedTransition (i : ℕ) (z : InitializationSample) : Measure InitializationSample :=
  if 2 ≤ z.shorter.forest.roots.card then
    if z.used then synchronizedLaw z else initializationLaw (consumeDelayed z) i
  else Measure.dirac z

/-- The direct source pending step samples positions in the current longer
forest, after consuming the stored pair only in the comparison forest. -/
noncomputable def pendingDirectLaw (i : ℕ) (z : InitializationSample) : Measure InitializationSample :=
  (uniformRootPair (Finset.univ : Finset (Fin z.longer.forest.roots.card))).map fun p =>
    (⟨distinguishedJoinChoice z.longer (.inr i)
        (z.longer.forest.indexedPair (rootEnumeration z.longer) p),
      consumeDelayed z, decide (p.1.val = 0 ∨ p.2.val = 0), (p.1.val, p.2.val)⟩ :
        InitializationSample)

theorem pendingDirectLaw_eq_initialization {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hu : z.used = false) :
    pendingDirectLaw i z = initializationLaw (consumeDelayed z) i := by
  obtain ⟨_, _, _, _, _, hmatch⟩ := hz.pending hu
  unfold pendingDirectLaw
  rw [hmatch]
  rfl

theorem delayedTransition_pending_eq {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) (hu : z.used = false) :
    delayedTransition i z = pendingDirectLaw i z := by
  rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN), hu]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (pendingDirectLaw_eq_initialization hz hu).symm

theorem delayedTransition_probability {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) : IsProbabilityMeasure (delayedTransition i z) := by
  unfold delayedTransition
  split_ifs with hcard hused
  · exact synchronizedLaw_probability z hcard
  · have hu : z.used = false := by cases h : z.used <;> simp_all
    have hc := hz.consume_card hu
    have hN : 2 ≤ N := by simpa only [hz.shorter_card] using hcard
    exact initializationLaw_probability (consumeDelayed z) hz.consume_fresh (by omega)
  · infer_instance

theorem delayedTransition_ae_valid {i N : ℕ} {z : InitializationSample}
    (hz : DelayedValid i N z) (hN : 2 ≤ N) :
    ∀ᵐ z' ∂delayedTransition i z, DelayedValid i (N - 1) z' := by
  rw [delayedTransition, ite_eq_left (by simpa only [hz.shorter_card] using hN)]
  cases hu : z.used with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hc : (consumeDelayed z).forest.roots.card = N - 1 := by
      have hh := hz.consume_card hu
      omega
    simpa only [hc] using initializationLaw_ae_delayedValid (consumeDelayed z) hz.consume_fresh
  | true =>
    simp only [↓reduceIte]
    exact synchronizedLaw_ae_valid hz hu

/-- Actual finite iteration of the initialization and delayed transition.
The identity fallback holds the terminal one-component state fixed. -/
noncomputable def delayedLawAfter (F : Forest) (i : ℕ) : ℕ → Measure InitializationSample
  | 0 => initializationLaw F i
  | t + 1 => (delayedLawAfter F i t).bind (delayedTransition i)

theorem delayedLawAfter_ae_valid (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    ∀ᵐ z ∂delayedLawAfter F i t, DelayedValid i (F.forest.roots.card - t) z := by
  induction t with
  | zero => simpa only [delayedLawAfter, Nat.sub_zero] using initializationLaw_ae_delayedValid F hi
  | succ t ih =>
    rw [ae_iff, delayedLawAfter, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [ih (by omega)] with z hz
    have hN : 2 ≤ F.forest.roots.card - t := by omega
    have he : F.forest.roots.card - t - 1 = F.forest.roots.card - (t + 1) := by omega
    simpa only [he, Pi.zero_apply] using ae_iff.mp (delayedTransition_ae_valid hz hN)

theorem delayedLawAfter_probability (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card)
    (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) : IsProbabilityMeasure (delayedLawAfter F i t) := by
  induction t with
  | zero => exact initializationLaw_probability F hi hF
  | succ t ih =>
    let := ih (by omega)
    unfold delayedLawAfter
    apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
    filter_upwards [delayedLawAfter_ae_valid F hi t (by omega)] with z hz
    exact delayedTransition_probability hz

theorem delayedLawAfter_terminal_used (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    ∀ᵐ z ∂delayedLawAfter F i (F.forest.roots.card - 1), z.used = true := by
  have he : F.forest.roots.card - (F.forest.roots.card - 1) = 1 := by omega
  have hv := delayedLawAfter_ae_valid F hi (F.forest.roots.card - 1) le_rfl
  rw [he] at hv
  exact hv.mono (fun _ hz => hz.used_at_one)

noncomputable def sourceDelayedLaw (k : ℕ) (tail : Word) (t : ℕ) : Measure InitializationSample :=
  (initializationTailLaw k tail).bind (fun F => delayedLawAfter F k t)

/-- Full forest matching and all indices hold at each source phase; the
parameter `t` counts backwards steps after initialization, so `N=k-t`. -/
theorem sourceDelayedLaw_ae_valid (k : ℕ) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail))
    (t : ℕ) (ht : t ≤ k - 1) :
    ∀ᵐ z ∂sourceDelayedLaw k tail t, DelayedValid k (k - t) z := by
  rw [ae_iff, sourceDelayedLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  have hv := delayedLawAfter_ae_valid F hF.1 t (by simpa only [hF.2] using ht)
  exact ae_iff.mp (by simpa only [hF.2] using hv)

theorem sourceDelayedLaw_probability (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail))
    (t : ℕ) (ht : t ≤ k - 1) : IsProbabilityMeasure (sourceDelayedLaw k tail t) := by
  unfold sourceDelayedLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  exact delayedLawAfter_probability F hF.1 (by omega) t (by simpa only [hF.2] using ht)

/-- The source terminal flag is one, including the boundary `k=1`. -/
theorem sourceDelayedLaw_terminal_used (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ z ∂sourceDelayedLaw k tail (k - 1), z.used = true := by
  have hv := sourceDelayedLaw_ae_valid k tail ha (k - 1) le_rfl
  have he : k - (k - 1) = 1 := by omega
  rw [he] at hv
  exact hv.mono (fun _ hz => hz.used_at_one)

end ReverseOrdered
end FreezingGrowth
