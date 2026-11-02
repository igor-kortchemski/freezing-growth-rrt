module

public import FreezingGrowth.ReverseHeightInitialization
public import FreezingGrowth.ReverseHeightKernel

/-!
# The actual reverse construction projected to component-height dynamics

The one-step law retains ordered distinct positions, including multiplicities
of equal heights. Finite words are processed from right to left. Initial
component count is the terminal active population, which may be zero.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory
open scoped Classical

namespace ReverseHeightList

def finPairValues {n : ℕ} (p : Fin n × Fin n) : ℕ × ℕ := (p.1.val, p.2.val)

theorem map_uniformRootPair_finPairValues (n : ℕ) :
    (uniformRootPair (Finset.univ : Finset (Fin n))).map finPairValues =
      uniformRootPair (Finset.range n) := by
  have hinj : Function.Injective (@finPairValues n) := by
    intro p q he
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
  have himage : (Finset.univ : Finset (Fin n)).offDiag.image finPairValues =
      (Finset.range n).offDiag := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have hne := (Finset.mem_offDiag.mp hq).2.2
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_range.mpr q.1.isLt,
        Finset.mem_range.mpr q.2.isLt, fun he => hne (Fin.ext he)⟩
    · intro hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      refine Finset.mem_image.mpr ⟨(⟨p.1, Finset.mem_range.mp ha⟩,
        ⟨p.2, Finset.mem_range.mp hb⟩), ?_, rfl⟩
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
        fun he => hab (congrArg Fin.val he)⟩
  unfold uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _) hinj.injOn, himage]

theorem uniformFinPair_ae_distinct (n : ℕ) :
    ∀ᵐ p ∂uniformRootPair (Finset.univ : Finset (Fin n)), p.1 ≠ p.2 := by
  have hs : ∀ᵐ p ∂uniformRootPair (Finset.univ : Finset (Fin n)),
      p ∈ (Finset.univ : Finset (Fin n)).offDiag := by
    rw [ae_iff]
    simp [uniformRootPair, Measure.uniformOfFinset_apply]
  exact hs.mono (fun _ hp => (Finset.mem_offDiag.mp hp).2.2)

/-- Undo one source operation on the actual component heights. -/
noncomputable def profileTransition (b : Bool) (xs : List ℕ) : Measure (List ℕ) :=
  if b then graftLaw xs else Measure.dirac (xs ++ [0])

instance profileTransition_probability (b : Bool) (xs : List ℕ) :
    IsProbabilityMeasure (profileTransition b xs) := by
  cases b <;> simp only [profileTransition, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- Run the suffix first, as in Algorithm 2. -/
noncomputable def runBackward : Word → Measure (List ℕ) → Measure (List ℕ)
  | [], μ => μ
  | b :: bs, μ => (runBackward bs μ).bind (profileTransition b)

instance runBackward_probability (xs : Word) (μ : Measure (List ℕ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (runBackward xs μ) := by
  induction xs with
  | nil => change IsProbabilityMeasure μ; infer_instance
  | cons b bs ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall (profileTransition_probability b))

theorem runBackward_append (xs ys : Word) (μ : Measure (List ℕ)) :
    runBackward (xs ++ ys) μ = runBackward xs (runBackward ys μ) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, runBackward, ih]

/-- Executing a finite schedule commutes with mixing its initial laws. -/
theorem runBackward_bind (xs : Word) (μ : Measure (List ℕ))
    (K : List ℕ → Measure (List ℕ)) :
    runBackward xs (μ.bind K) = μ.bind (fun hs => runBackward xs (K hs)) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [runBackward, ih, Measure.bind_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    rfl

theorem runBackward_nil (μ : Measure (List ℕ)) : runBackward [] μ = μ := by
  rw [runBackward]

theorem profileTransition_true : profileTransition true = graftLaw := by
  funext xs
  simp [profileTransition]

theorem profileTransition_false (xs : List ℕ) :
    profileTransition false xs = Measure.dirac (xs ++ [0]) := by
  simp [profileTransition]

theorem runBackward_singleton_true (μ : Measure (List ℕ)) :
    runBackward [true] μ = μ.bind graftLaw := by
  rw [runBackward, runBackward_nil, profileTransition_true]

theorem finishAfter_succ_fun (k : ℕ) :
    finishAfter (k + 1) = fun xs => (graftLaw xs).bind (finishAfter k) := by
  funext xs
  rw [finishAfter]

/-- A pure attachment prefix completes exactly the prescribed number of
coalescences before observing the maximum component height. -/
theorem map_runBackward_replicate_true (k : ℕ) (μ : Measure (List ℕ)) :
    (runBackward (List.replicate k true) μ).map (fun hs => hs.toFinset.sup id) =
      μ.bind (finishAfter k) := by
  induction k generalizing μ with
  | zero =>
    have hf : finishAfter 0 = fun xs => Measure.dirac (xs.toFinset.sup id) := by
      funext xs
      rw [finishAfter]
    rw [List.replicate_zero, runBackward_nil, hf]
    exact (Measure.bind_dirac_eq_map _ measurable_from_top).symm
  | succ k ih =>
    rw [List.replicate_succ', runBackward_append, runBackward_singleton_true, ih,
      Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      finishAfter_succ_fun]

theorem runBackward_drop_succ (xs : Word) {k : ℕ} (hk : k < xs.length)
    (μ : Measure (List ℕ)) :
    runBackward (xs.drop (xs.length - (k + 1))) μ =
      (runBackward (xs.drop (xs.length - k)) μ).bind
        (profileTransition (xs.toSigns (xs.length - k))) := by
  have hj : xs.length - (k + 1) < xs.length := by omega
  have he : xs.length - (k + 1) + 1 = xs.length - k := by omega
  rw [List.drop_eq_getElem_cons hj, runBackward, he, ← he, Word.toSigns_succ,
    List.getElem?_eq_getElem hj, Option.getD_some]

end ReverseHeightList

namespace ReverseOrdered

open ReverseHeightList

/-- Projecting the actual uniform root-pair kernel gives the exact height-list
kernel, for every forest including the harmless small-count totalizations. -/
theorem map_heightProfile_joinLaw (F : Forest) :
    (joinLaw F).map heightProfile = graftLaw (heightProfile F) := by
  have hlen : (heightProfile F).length = F.forest.roots.card := by
    rw [heightProfile_length, rootOrder_length]
  by_cases hF : 2 ≤ F.forest.roots.card
  · rw [joinLaw_eq_list_indices F hF,
      Measure.map_map measurable_from_top (measurable_of_countable _),
      graftLaw, hlen, ite_eq_left hF,
      ← map_uniformRootPair_finPairValues F.forest.roots.card,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    apply Measure.map_congr
    filter_upwards [uniformFinPair_ae_distinct F.forest.roots.card] with p hp
    let a : Fin F.rootOrder.length := ⟨p.1.val, by rw [rootOrder_length]; exact p.1.isLt⟩
    let b : Fin F.rootOrder.length := ⟨p.2.val, by rw [rootOrder_length]; exact p.2.isLt⟩
    have hab : a ≠ b := by
      intro he
      have h1 : a.val = b.val := congrArg Fin.val he
      exact hp (Fin.ext h1)
    exact heightProfile_joinChoice F a b hab
  · rw [joinLaw, ite_eq_right hF, Measure.map_dirac' measurable_from_top,
      graftLaw, hlen, ite_eq_right hF]

/-- Valid reverse phases supply the fresh singleton required on freezing. -/
theorem map_heightProfile_transitionLaw {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : Reverse.ValidAt x n (i + 1) F.forest) :
    (transitionLaw x i F).map heightProfile =
      profileTransition (x (i + 1)) (heightProfile F) := by
  cases hx : x (i + 1)
  · simp only [transitionLaw, profileTransition, hx, Bool.false_eq_true, ↓reduceIte,
      Measure.map_dirac' measurable_from_top,
      heightProfile_insertLabel F i (valid_freezing_fresh hF)]
  · simpa only [transitionLaw, profileTransition, hx, ↓reduceIte] using map_heightProfile_joinLaw F

/-- The complete stopped source process is the suffix height executor. This
also retains the common-tail support needed when comparing two prefixes. -/
theorem map_lawAfter_heightProfile (xs : Word) (ha : xs.admissible) (k : ℕ)
    (hk : k ≤ xs.length) :
    (lawAfter xs.toSigns xs.length k).map heightProfile =
      runBackward (xs.drop (xs.length - k))
        (Measure.dirac (List.replicate (activeCount xs.toSigns xs.length).toNat 0)) := by
  induction k with
  | zero => simp [lawAfter, runBackward, heightProfile_initial]
  | succ k ih =>
    have hk' : k < xs.length := by omega
    have he : xs.length - (k + 1) + 1 = xs.length - k := by omega
    have hn := (Word.admissible_iff_le_extinctionTime xs).mp ha
    rw [lawAfter, ite_eq_left hk',
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      runBackward_drop_succ xs hk', ← ih (by omega),
      Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [lawAfter_valid xs.toSigns xs.length k hn (by omega)] with F hF
    have hF' : Reverse.ValidAt xs.toSigns xs.length (xs.length - (k + 1) + 1) F.forest :=
      he.symm ▸ hF
    simpa only [he] using map_heightProfile_transitionLaw hF'

end ReverseOrdered

namespace Word

/-- The finite-word height law computed by the actual reverse component
dynamics. The initial list is empty when the word ends at extinction. -/
theorem heightLaw_eq_runBackward (xs : Word) (ha : xs.admissible) :
    xs.heightLaw =
      (ReverseHeightList.runBackward xs
        (Measure.dirac (List.replicate (activeCount xs.toSigns xs.length).toNat 0))).map
          (fun hs => hs.toFinset.sup id) := by
  have hm := ReverseOrdered.map_lawAfter_heightProfile xs ha xs.length le_rfl
  simp only [Nat.sub_self, List.drop_zero] at hm
  rw [heightLaw_eq_orderedReverseHeightLaw xs ha, ← hm,
    Measure.map_map measurable_from_top measurable_from_top]
  unfold ReverseOrdered.heightLaw ReverseOrdered.treeLaw
  congr 1
  funext F
  exact (ReverseOrdered.heightProfile_max F).symm

end Word
end FreezingGrowth
