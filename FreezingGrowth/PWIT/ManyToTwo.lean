module

public import FreezingGrowth.PWIT.OffspringIntensity
public import FreezingGrowth.PWIT.RankDensity

/-!
# Generation intensity and shared ancestry

The one-path intensity sums all child ranks. The paired laws below retain the
common ancestral sample; independence starts only after distinct children.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable def generationIncrementIntensity (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.sum fun r : Fin d → ℕ => law.map (tupleIncrement r)

noncomputable def positiveOrthantVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => positiveLebesgue

instance positiveOrthantVolume_sigmaFinite (d : ℕ) :
    SigmaFinite (positiveOrthantVolume d) := by
  unfold positiveOrthantVolume
  infer_instance

theorem positiveOrthantVolume_cons (d : ℕ) :
    (positiveLebesgue.prod (positiveOrthantVolume d)).map
      (fun p : ℝ × (Fin d → ℝ) => Fin.cons p.1 p.2) = positiveOrthantVolume (d + 1) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => positiveLebesgue) 0).symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Equiv.coe_fn_mk, positiveOrthantVolume] using h.map_eq

theorem positiveOrthantVolume_append (m n : ℕ) :
    ((positiveOrthantVolume m).prod (positiveOrthantVolume n)).map
      (fun p => Fin.append p.1 p.2) = positiveOrthantVolume (m + n) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm
  let f := MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ)
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  have h₁ := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ Fin n => positiveLebesgue)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (m + n) => positiveLebesgue)
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  have he : (fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2) = f ∘ e := by
    funext p i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [f, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  rw [he]
  exact (h₂.comp h₁).map_eq

theorem generationIncrementIntensity_eq_sum_rank (d : ℕ) :
    generationIncrementIntensity d = Measure.sum (rankIncrementMeasure d) := by
  classical
  unfold generationIncrementIntensity
  simp only [map_tupleIncrement]
  rw [← Measure.sum_comp_equiv (Finset.Nat.sigmaAntidiagonalTupleEquivTuple d)]
  ext s hs
  simp only [Measure.sum_apply _ hs, Function.comp_apply,
    Finset.Nat.sigmaAntidiagonalTupleEquivTuple]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  rw [← Measure.sum_apply _ hs]
  change (Measure.sum (fun r : Finset.Nat.antidiagonalTuple d k => incrementLaw (r : Fin d → ℕ))) s = _
  rw [Measure.sum_coe_finset (Finset.Nat.antidiagonalTuple d k) incrementLaw]
  rfl

theorem tsum_rankIncrementPDF {d : ℕ} (x : Fin d → ℝ) :
    (∑' k, rankIncrementPDF d k x) =
      {x : Fin d → ℝ | ∀ i, 0 ≤ x i}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hx : ∀ i, 0 ≤ x i
  · have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
    have he (k : ℕ) : rankIncrementPDF d k x = erlangPDF k (∑ i, x i) := by
      simp only [rankIncrementPDF, ite_eq_left hx, erlangPDF, ite_eq_left hs]
      congr 1
      ring
    simp_rw [he]
    rw [tsum_erlangPDF]
    simp [hs, hx]
  · simp [rankIncrementPDF, hx]

@[fun_prop] theorem measurable_rankIncrementPDF (d k : ℕ) :
    Measurable (rankIncrementPDF d k) := by
  unfold rankIncrementPDF
  apply Measurable.ite (by measurability) <;> fun_prop

/-- The intensity of all generation-`d` increment vectors is Lebesgue measure
on the positive orthant, including the one-point zero-dimensional case. -/
theorem generationIncrementIntensity_eq (d : ℕ) :
    generationIncrementIntensity d = positiveOrthantVolume d := by
  rw [generationIncrementIntensity_eq_sum_rank]
  rw [show rankIncrementMeasure d = fun k => volume.withDensity (rankIncrementPDF d k) from
    funext (rankIncrementMeasure_eq_withDensity d)]
  rw [← withDensity_tsum (fun k => measurable_rankIncrementPDF d k)]
  have he : (∑' k, rankIncrementPDF d k) =
      {x : Fin d → ℝ | ∀ i, 0 ≤ x i}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    rw [Pi.tsum_apply (Pi.summable.mpr fun _ => ENNReal.summable)]
    exact tsum_rankIncrementPDF x
  rw [he]
  change volume.withDensity ({x : Fin d → ℝ | ∀ i, 0 ≤ x i}.indicator 1) = _
  rw [withDensity_indicator_one (by measurability)]
  have heSet : {x : Fin d → ℝ | ∀ i, 0 ≤ x i} =
      Set.univ.pi (fun _ : Fin d => Set.Ici (0 : ℝ)) := by
    ext x
    constructor
    · intro hx i _
      exact hx i
    · intro hx i
      exact hx i (Set.mem_univ i)
  rw [heSet, volume_pi, Measure.restrict_pi_pi]
  rfl

theorem tupleIncrement_cons {d : ℕ} (i : ℕ) (r : Fin d → ℕ) (ω : Sample) :
    tupleIncrement (Fin.cons i r) ω =
      Fin.cons (rootArrival i ω) (tupleIncrement r (childSample ω i)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [tupleIncrement, rootArrival_eq_childDelay]
  · simp only [tupleIncrement, List.ofFn_cons, Fin.cons_succ, Fin.val_succ,
      List.take_succ_cons]
    rfl

def prependShared {d : ℕ} (p : ℝ × ((Fin d → ℝ) × (Fin d → ℝ))) :
    (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) :=
  (Fin.cons p.1 p.2.1, Fin.cons p.1 p.2.2)

def prependDistinct {d : ℕ} (p : (ℝ × ℝ) × ((Fin d → ℝ) × (Fin d → ℝ))) :
    (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) :=
  (Fin.cons p.1.1 p.2.1, Fin.cons p.1.2 p.2.2)

@[fun_prop] theorem measurable_prependShared (d : ℕ) :
    Measurable (@prependShared d) := by
  unfold prependShared
  exact ((Measurable.of_eval fun i => Fin.cases (by fun_prop) (fun _ => by fun_prop) i).prodMk
    (Measurable.of_eval fun i => Fin.cases (by fun_prop) (fun _ => by fun_prop) i))

@[fun_prop] theorem measurable_prependDistinct (d : ℕ) :
    Measurable (@prependDistinct d) := by
  unfold prependDistinct
  exact ((Measurable.of_eval fun i => Fin.cases (by fun_prop) (fun _ => by fun_prop) i).prodMk
    (Measurable.of_eval fun i => Fin.cases (by fun_prop) (fun _ => by fun_prop) i))

private theorem prod_map_right {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B)
    [SFinite ν] {f : B → C} (hf : Measurable f) :
    μ.prod (ν.map f) = (μ.prod ν).map (Prod.map id f) := by
  simpa only [Measure.map_id] using Measure.map_prod_map μ ν measurable_id hf

private theorem prod_map_left {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B)
    [SFinite ν] {f : A → C} (hf : Measurable f) :
    (μ.map f).prod ν = (μ.prod ν).map (Prod.map f id) := by
  simpa only [Measure.map_id] using Measure.map_prod_map μ ν hf measurable_id

/-- Paths using the same first child retain the joint law of both descendants. -/
theorem tupleIncrement_same_child_joint_law {d : ℕ} (i : ℕ) (r s : Fin d → ℕ) :
    law.map (fun ω => (tupleIncrement (Fin.cons i r) ω, tupleIncrement (Fin.cons i s) ω)) =
      ((law.map (rootArrival i)).prod
        (law.map (fun ω => (tupleIncrement r ω, tupleIncrement s ω)))).map prependShared := by
  have hm : Measurable (fun ω => (tupleIncrement r ω, tupleIncrement s ω)) := by fun_prop
  rw [prod_map_right _ _ hm,
    ← rootArrival_childSample_joint_law i,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  simp only [Function.comp_apply, Prod.map_apply, id_eq, prependShared,
    tupleIncrement_cons]

/-- After distinct first children the two complete descendant samples factor.
The correlated cumulative birth times remain in their actual joint law. -/
theorem tupleIncrement_distinct_children_joint_law {d : ℕ} {i j : ℕ}
    (hij : i ≠ j) (r s : Fin d → ℕ) :
    law.map (fun ω => (tupleIncrement (Fin.cons i r) ω, tupleIncrement (Fin.cons j s) ω)) =
      ((law.map (fun ω => (rootArrival i ω, rootArrival j ω))).prod
        ((law.map (tupleIncrement r)).prod (law.map (tupleIncrement s)))).map prependDistinct := by
  rw [Measure.map_prod_map _ _ (measurable_tupleIncrement r) (measurable_tupleIncrement s),
    prod_map_right _ _ (by fun_prop),
    ← rootArrivals_childSamples_joint_law hij,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  simp only [Function.comp_apply, Prod.map_apply, id_eq, prependDistinct,
    tupleIncrement_cons]

noncomputable def generationPairIntensity (d : ℕ) :
    Measure ((Fin d → ℝ) × (Fin d → ℝ)) :=
  Measure.sum fun r : Fin d → ℕ => Measure.sum fun s : Fin d → ℕ =>
    law.map (fun ω => (tupleIncrement r ω, tupleIncrement s ω))

instance generationPairIntensity_sFinite (d : ℕ) : SFinite (generationPairIntensity d) := by
  unfold generationPairIntensity
  infer_instance

abbrev PathPairIndex (d : ℕ) := (Fin d → ℕ) × (Fin d → ℕ)

def childHeadsEquiv (d : ℕ) :
    ((ℕ × PathPairIndex d) ⊕ (DistinctChildPair × PathPairIndex d)) ≃ PathPairIndex (d + 1) where
  toFun
    | Sum.inl p => (Fin.cons p.1 p.2.1, Fin.cons p.1 p.2.2)
    | Sum.inr p => (Fin.cons p.1.1.1 p.2.1, Fin.cons p.1.1.2 p.2.2)
  invFun p := if h : p.1 0 = p.2 0 then
    Sum.inl (p.1 0, Fin.tail p.1, Fin.tail p.2)
    else Sum.inr (⟨(p.1 0, p.2 0), h⟩, Fin.tail p.1, Fin.tail p.2)
  left_inv p := by
    cases p with
    | inl p => simp
    | inr p => simp [p.1.2]
  right_inv p := by
    dsimp only
    split_ifs with h
    · apply Prod.ext
      · exact Fin.cons_self_tail _
      · change Fin.cons (p.1 0) (Fin.tail p.2) = p.2
        rw [h, Fin.cons_self_tail]
    · simp

noncomputable def sameChildPairIntensity (d : ℕ) :
    Measure ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :=
  Measure.sum fun p : ℕ × PathPairIndex d =>
    law.map (fun ω => (tupleIncrement (Fin.cons p.1 p.2.1) ω,
      tupleIncrement (Fin.cons p.1 p.2.2) ω))

noncomputable def distinctChildPairIntensity (d : ℕ) :
    Measure ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)) :=
  Measure.sum fun p : DistinctChildPair × PathPairIndex d =>
    law.map (fun ω => (tupleIncrement (Fin.cons p.1.1.1 p.2.1) ω,
      tupleIncrement (Fin.cons p.1.1.2 p.2.2) ω))

theorem generationPairIntensity_split (d : ℕ) :
    generationPairIntensity (d + 1) = sameChildPairIntensity d + distinctChildPairIntensity d := by
  unfold generationPairIntensity
  rw [Measure.sum_sum, ← Measure.sum_comp_equiv (childHeadsEquiv d)]
  have he : ((fun p : PathPairIndex (d + 1) => law.map (fun ω =>
      (tupleIncrement p.1 ω, tupleIncrement p.2 ω))) ∘ childHeadsEquiv d) = Sum.elim
    (fun p : ℕ × PathPairIndex d => law.map (fun ω =>
      (tupleIncrement (Fin.cons p.1 p.2.1) ω, tupleIncrement (Fin.cons p.1 p.2.2) ω)))
    (fun p : DistinctChildPair × PathPairIndex d => law.map (fun ω =>
      (tupleIncrement (Fin.cons p.1.1.1 p.2.1) ω,
        tupleIncrement (Fin.cons p.1.1.2 p.2.2) ω))) := by
    funext p
    cases p <;> rfl
  rw [he]
  ext s hs
  simp only [sameChildPairIntensity, distinctChildPairIntensity,
    Measure.sum_apply _ hs, Measure.add_apply]
  exact ENNReal.summable.tsum_sum ENNReal.summable

theorem sameChildPairIntensity_eq (d : ℕ) :
    sameChildPairIntensity d =
      (positiveLebesgue.prod (generationPairIntensity d)).map prependShared := by
  unfold sameChildPairIntensity
  simp_rw [tupleIncrement_same_child_joint_law]
  rw [← Measure.map_sum (measurable_prependShared d).aemeasurable,
    ← Measure.prod_sum (fun i => law.map (rootArrival i))
      (fun p : PathPairIndex d => law.map (fun ω => (tupleIncrement p.1 ω, tupleIncrement p.2 ω))),
    sum_rootArrival_law]
  unfold generationPairIntensity
  rw [Measure.sum_sum]

theorem distinctChildPairIntensity_eq (d : ℕ) :
    distinctChildPairIntensity d =
      ((positiveLebesgue.prod positiveLebesgue).prod
        ((positiveOrthantVolume d).prod (positiveOrthantVolume d))).map prependDistinct := by
  unfold distinctChildPairIntensity
  have he (p : DistinctChildPair × PathPairIndex d) :=
    tupleIncrement_distinct_children_joint_law p.1.2 p.2.1 p.2.2
  simp_rw [he]
  rw [← Measure.map_sum (measurable_prependDistinct d).aemeasurable,
    ← Measure.prod_sum (fun p : DistinctChildPair =>
      law.map (fun ω => (rootArrival p.1.1 ω, rootArrival p.1.2 ω)))
      (fun p : PathPairIndex d =>
        (law.map (tupleIncrement p.1)).prod (law.map (tupleIncrement p.2))),
    ← Measure.prod_sum (fun r : Fin d → ℕ => law.map (tupleIncrement r))
      (fun r : Fin d → ℕ => law.map (tupleIncrement r))]
  change (offspringPairIntensity.prod
    ((generationIncrementIntensity d).prod (generationIncrementIntensity d))).map prependDistinct = _
  rw [generationIncrementIntensity_eq]
  rw [offspringPairIntensity_eq]

/-- The exact recursion for ordered path pairs. The first term keeps their
shared first edge; the second term starts their independent branches. -/
theorem generationPairIntensity_succ (d : ℕ) :
    generationPairIntensity (d + 1) =
      (positiveLebesgue.prod (generationPairIntensity d)).map prependShared +
      ((positiveLebesgue.prod positiveLebesgue).prod
        ((positiveOrthantVolume d).prod (positiveOrthantVolume d))).map prependDistinct := by
  rw [generationPairIntensity_split, sameChildPairIntensity_eq, distinctChildPairIntensity_eq]

/-- Regroup four independent coordinates into the two offspring branches. -/
theorem map_prod_middle_swap {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (κ : Measure C) (ρ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite ρ] :
    ((μ.prod ν).prod (κ.prod ρ)).map
      (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) =
      (μ.prod κ).prod (ν.prod ρ) := by
  have h₁ := measurePreserving_prodAssoc μ ν (κ.prod ρ)
  have h₂ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν κ ρ).symm
  have h₃ := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := κ)).prod (MeasurePreserving.id ρ))
  have h₄ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc κ ν ρ)
  have h₅ := (measurePreserving_prodAssoc μ κ (ν.prod ρ)).symm
  exact (h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))).map_eq

theorem distinctChildPairIntensity_eq_product (d : ℕ) :
    distinctChildPairIntensity d =
      (positiveOrthantVolume (d + 1)).prod (positiveOrthantVolume (d + 1)) := by
  rw [distinctChildPairIntensity_eq, ← positiveOrthantVolume_cons d,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    ← map_prod_middle_swap positiveLebesgue positiveLebesgue
      (positiveOrthantVolume d) (positiveOrthantVolume d),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A common edge followed by either shared descendants or independent paths. -/
theorem generationPairIntensity_succ_product (d : ℕ) :
    generationPairIntensity (d + 1) =
      (positiveLebesgue.prod (generationPairIntensity d)).map prependShared +
      (positiveOrthantVolume (d + 1)).prod (positiveOrthantVolume (d + 1)) := by
  rw [generationPairIntensity_split, sameChildPairIntensity_eq,
    distinctChildPairIntensity_eq_product]

def appendShared {j q : ℕ}
    (p : (Fin j → ℝ) × ((Fin q → ℝ) × (Fin q → ℝ))) :
    (Fin (j + q) → ℝ) × (Fin (j + q) → ℝ) :=
  (Fin.append p.1 p.2.1, Fin.append p.1 p.2.2)

@[fun_prop] theorem measurable_appendShared (j q : ℕ) :
    Measurable (@appendShared j q) := by
  unfold appendShared
  apply Measurable.prodMk <;> apply Measurable.of_eval <;> intro i
  all_goals refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  all_goals simp only [Fin.append_left, Fin.append_right]; fun_prop

/-- The increment-vector measure for a common prefix of length `j` and two
independent suffixes of length `q`. This is not a probability measure. -/
noncomputable def overlapIntensity (j q : ℕ) :
    Measure ((Fin (j + q) → ℝ) × (Fin (j + q) → ℝ)) :=
  ((positiveOrthantVolume j).prod
    ((positiveOrthantVolume q).prod (positiveOrthantVolume q))).map appendShared

abbrev IncrementSequence := ℕ → ℝ

/-- Every coordinate outside the declared depth is zero. -/
def extendVector {d : ℕ} (x : Fin d → ℝ) : IncrementSequence :=
  fun i => if h : i < d then x ⟨i, h⟩ else 0

@[fun_prop] theorem measurable_extendVector (d : ℕ) : Measurable (@extendVector d) := by
  apply Measurable.of_eval
  intro i
  unfold extendVector
  split_ifs <;> fun_prop

theorem extendVector_apply {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    extendVector x i = x i := by simp [extendVector]

theorem restrict_extendVector {d : ℕ} (x : Fin d → ℝ) :
    (fun i : Fin d => extendVector x i) = x := by
  funext i
  exact extendVector_apply x i

theorem extendVector_injective (d : ℕ) : Function.Injective (@extendVector d) := by
  intro x y h
  funext i
  simpa only [extendVector_apply] using congrFun h (i : ℕ)

def extendPair {d : ℕ} (p : (Fin d → ℝ) × (Fin d → ℝ)) :
    IncrementSequence × IncrementSequence :=
  (extendVector p.1, extendVector p.2)

def restrictSequence (d : ℕ) (x : IncrementSequence) : Fin d → ℝ := fun i => x i

def restrictSequencePair (d : ℕ) (p : IncrementSequence × IncrementSequence) :
    (Fin d → ℝ) × (Fin d → ℝ) :=
  (restrictSequence d p.1, restrictSequence d p.2)

@[fun_prop] theorem measurable_restrictSequence (d : ℕ) : Measurable (restrictSequence d) := by
  unfold restrictSequence
  fun_prop

@[fun_prop] theorem measurable_restrictSequencePair (d : ℕ) :
    Measurable (restrictSequencePair d) := by
  unfold restrictSequencePair
  fun_prop

@[fun_prop] theorem measurable_extendPair (d : ℕ) : Measurable (@extendPair d) := by
  unfold extendPair
  fun_prop

def prependSequence (p : ℝ × IncrementSequence) : IncrementSequence
  | 0 => p.1
  | i + 1 => p.2 i

@[fun_prop] theorem measurable_prependSequence : Measurable prependSequence := by
  apply Measurable.of_eval
  intro i
  cases i <;> unfold prependSequence <;> fun_prop

theorem extendVector_cons {d : ℕ} (s : ℝ) (x : Fin d → ℝ) :
    extendVector (Fin.cons s x) = prependSequence (s, extendVector x) := by
  funext i
  cases i with
  | zero => simp [extendVector, prependSequence]
  | succ i =>
    by_cases hi : i < d
    · simp only [extendVector, prependSequence, dite_eq_left hi,
        dite_eq_left (show i + 1 < d + 1 by omega)]
      exact Fin.cons_succ (α := fun _ => ℝ) s x ⟨i, hi⟩
    · simp [extendVector, prependSequence, hi, show ¬i + 1 < d + 1 by omega]

def prependSequencePair (p : ℝ × (IncrementSequence × IncrementSequence)) :
    IncrementSequence × IncrementSequence :=
  (prependSequence (p.1, p.2.1), prependSequence (p.1, p.2.2))

@[fun_prop] theorem measurable_prependSequencePair : Measurable prependSequencePair := by
  unfold prependSequencePair
  fun_prop

noncomputable def extendedGenerationIntensity (d : ℕ) : Measure IncrementSequence :=
  (positiveOrthantVolume d).map extendVector

noncomputable def extendedGenerationPairIntensity (d : ℕ) :
    Measure (IncrementSequence × IncrementSequence) :=
  (generationPairIntensity d).map extendPair

instance extendedGenerationIntensity_sFinite (d : ℕ) :
    SFinite (extendedGenerationIntensity d) := by
  unfold extendedGenerationIntensity
  infer_instance

instance extendedGenerationPairIntensity_sFinite (d : ℕ) :
    SFinite (extendedGenerationPairIntensity d) := by
  unfold extendedGenerationPairIntensity
  infer_instance

/-- The common carrier preserves the complete finite pair intensity. -/
theorem map_extendedGenerationPairIntensity_restrict (d : ℕ) :
    (extendedGenerationPairIntensity d).map (restrictSequencePair d) =
      generationPairIntensity d := by
  unfold extendedGenerationPairIntensity
  rw [Measure.map_map (measurable_restrictSequencePair d) (measurable_extendPair d)]
  have he : restrictSequencePair d ∘ extendPair = id := by
    funext p
    apply Prod.ext <;> funext i <;> exact extendVector_apply _ i
  rw [he, Measure.map_id]

noncomputable def prependPairMeasure (μ : Measure (IncrementSequence × IncrementSequence)) :
    Measure (IncrementSequence × IncrementSequence) :=
  (positiveLebesgue.prod μ).map prependSequencePair

theorem extendedGenerationIntensity_succ (d : ℕ) :
    extendedGenerationIntensity (d + 1) =
      (positiveLebesgue.prod (extendedGenerationIntensity d)).map prependSequence := by
  unfold extendedGenerationIntensity
  rw [← positiveOrthantVolume_cons d, Measure.map_map (by fun_prop) (by fun_prop),
    prod_map_right _ _ (measurable_extendVector d), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  exact extendVector_cons p.1 p.2

theorem extendedGenerationPairIntensity_succ (d : ℕ) :
    extendedGenerationPairIntensity (d + 1) =
      prependPairMeasure (extendedGenerationPairIntensity d) +
        (extendedGenerationIntensity (d + 1)).prod (extendedGenerationIntensity (d + 1)) := by
  unfold extendedGenerationPairIntensity
  rw [generationPairIntensity_succ_product, Measure.map_add _ _ (measurable_extendPair _),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  · unfold prependPairMeasure
    rw [prod_map_right _ _ (measurable_extendPair d), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    simp only [Function.comp_apply, Prod.map, id_eq, extendPair, prependShared,
      prependSequencePair, extendVector_cons]
  · exact (Measure.map_prod_map _ _ (measurable_extendVector _) (measurable_extendVector _)).symm

def appendSequence {j : ℕ} (p : (Fin j → ℝ) × IncrementSequence) : IncrementSequence :=
  fun i => if h : i < j then p.1 ⟨i, h⟩ else p.2 (i - j)

@[fun_prop] theorem measurable_appendSequence (j : ℕ) : Measurable (@appendSequence j) := by
  apply Measurable.of_eval
  intro i
  unfold appendSequence
  split_ifs <;> fun_prop

def appendSequencePair {j : ℕ}
    (p : (Fin j → ℝ) × (IncrementSequence × IncrementSequence)) :
    IncrementSequence × IncrementSequence :=
  (appendSequence (p.1, p.2.1), appendSequence (p.1, p.2.2))

@[fun_prop] theorem measurable_appendSequencePair (j : ℕ) :
    Measurable (@appendSequencePair j) := by
  unfold appendSequencePair
  fun_prop

theorem appendSequence_cons {j : ℕ} (a : ℝ) (x : Fin j → ℝ) (y : IncrementSequence) :
    appendSequence (Fin.cons a x, y) = prependSequence (a, appendSequence (x, y)) := by
  funext i
  cases i with
  | zero => simp [appendSequence, prependSequence]
  | succ i =>
    by_cases hi : i < j
    · simp only [appendSequence, prependSequence, dite_eq_left hi,
        dite_eq_left (show i + 1 < j + 1 by omega)]
      exact Fin.cons_succ (α := fun _ => ℝ) a x ⟨i, hi⟩
    · simp [appendSequence, prependSequence, hi, show ¬i + 1 < j + 1 by omega]

noncomputable def extendedOverlapIntensity (j q : ℕ) :
    Measure (IncrementSequence × IncrementSequence) :=
  ((positiveOrthantVolume j).prod
    ((extendedGenerationIntensity q).prod (extendedGenerationIntensity q))).map appendSequencePair

instance extendedOverlapIntensity_sFinite (j q : ℕ) : SFinite (extendedOverlapIntensity j q) := by
  unfold extendedOverlapIntensity
  infer_instance

theorem extendedOverlapIntensity_zero (q : ℕ) :
    extendedOverlapIntensity 0 q =
      (extendedGenerationIntensity q).prod (extendedGenerationIntensity q) := by
  unfold extendedOverlapIntensity positiveOrthantVolume
  rw [Measure.pi_of_empty _ (fun i : Fin 0 => i.elim0), Measure.dirac_prod,
    Measure.map_map (measurable_appendSequencePair 0) (by fun_prop)]
  convert Measure.map_id using 1
  congr 1

theorem prependPairMeasure_overlap (j q : ℕ) :
    prependPairMeasure (extendedOverlapIntensity j q) = extendedOverlapIntensity (j + 1) q := by
  unfold prependPairMeasure extendedOverlapIntensity
  rw [prod_map_right _ _ (measurable_appendSequencePair j),
    Measure.map_map (measurable_prependSequencePair) (by fun_prop),
    ← positiveOrthantVolume_cons j, prod_map_left _ _ (by fun_prop),
    Measure.map_map (measurable_appendSequencePair (j + 1)) (by fun_prop)]
  rw [← Measure.prodAssoc_prod (μ := positiveLebesgue) (ν := positiveOrthantVolume j)
    (τ := (extendedGenerationIntensity q).prod (extendedGenerationIntensity q)),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  change (prependSequence (p.1.1, appendSequence (p.1.2, p.2.1)),
    prependSequence (p.1.1, appendSequence (p.1.2, p.2.2))) =
      (appendSequence (Fin.cons p.1.1 p.1.2, p.2.1),
        appendSequence (Fin.cons p.1.1 p.1.2, p.2.2))
  rw [appendSequence_cons, appendSequence_cons]

theorem prependPairMeasure_finset_sum {ι : Type*} (s : Finset ι)
    (μ : ι → Measure (IncrementSequence × IncrementSequence)) [∀ i, SFinite (μ i)] :
    prependPairMeasure (∑ i ∈ s, μ i) = ∑ i ∈ s, prependPairMeasure (μ i) := by
  rw [← Measure.sum_coe_finset s μ]
  unfold prependPairMeasure
  rw [Measure.prod_sum_right, Measure.map_sum measurable_prependSequencePair.aemeasurable,
    Measure.sum_coe_finset s (fun i =>
      (positiveLebesgue.prod (μ i)).map prependSequencePair)]

theorem extendedGenerationIntensity_zero :
    extendedGenerationIntensity 0 = Measure.dirac (fun _ : ℕ => (0 : ℝ)) := by
  unfold extendedGenerationIntensity positiveOrthantVolume
  rw [Measure.pi_of_empty _ (fun i : Fin 0 => i.elim0),
    Measure.map_dirac' (measurable_extendVector 0)]
  rfl

theorem generationPairIntensity_zero :
    generationPairIntensity 0 =
      Measure.dirac ((fun i : Fin 0 => i.elim0), (fun i : Fin 0 => i.elim0)) := by
  let r : Fin 0 → ℕ := fun i => i.elim0
  let : Unique (Fin 0 → ℕ) := ⟨⟨r⟩, fun x => funext fun i => i.elim0⟩
  unfold generationPairIntensity
  simp only [Measure.sum_fintype, Finset.univ_unique, Finset.sum_singleton]
  have he (s : Fin 0 → ℕ) (ω : Sample) :
      tupleIncrement s ω = (fun i : Fin 0 => (i.elim0 : ℝ)) := Subsingleton.elim _ _
  simp_rw [he]
  rw [Measure.map_const, measure_univ, one_smul]

theorem extendedGenerationPairIntensity_zero :
    extendedGenerationPairIntensity 0 = extendedOverlapIntensity 0 0 := by
  unfold extendedGenerationPairIntensity
  rw [generationPairIntensity_zero, Measure.map_dirac' (measurable_extendPair 0),
    extendedOverlapIntensity_zero, extendedGenerationIntensity_zero, Measure.dirac_prod_dirac]
  rfl

/-- The full common-ancestor expansion, including the diagonal as the `j=d`
term. All ranks were summed before the independent suffix intensities appeared. -/
theorem extendedGenerationPairIntensity_eq_sum (d : ℕ) :
    extendedGenerationPairIntensity d =
      ∑ j ∈ Finset.range (d + 1), extendedOverlapIntensity j (d - j) := by
  induction d with
  | zero => simpa using extendedGenerationPairIntensity_zero
  | succ d ih =>
    rw [extendedGenerationPairIntensity_succ, ih, prependPairMeasure_finset_sum]
    simp_rw [prependPairMeasure_overlap]
    rw [← extendedOverlapIntensity_zero]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.add_sub_add_right]

theorem extendedOverlapIntensity_diagonal (d : ℕ) :
    extendedOverlapIntensity d 0 =
      (extendedGenerationIntensity d).map (fun x => (x, x)) := by
  unfold extendedOverlapIntensity
  rw [extendedGenerationIntensity_zero, Measure.dirac_prod_dirac, Measure.prod_dirac,
    Measure.map_map (measurable_appendSequencePair d) (by fun_prop)]
  unfold extendedGenerationIntensity
  rw [Measure.map_map (by fun_prop) (measurable_extendVector d)]
  rfl

/-- Exact ordered many-to-two identity with the diagonal written separately. -/
theorem extendedGenerationPairIntensity_manyToTwo (d : ℕ) :
    extendedGenerationPairIntensity d =
      (extendedGenerationIntensity d).map (fun x => (x, x)) +
        ∑ j ∈ Finset.range d, extendedOverlapIntensity j (d - j) := by
  rw [extendedGenerationPairIntensity_eq_sum, Finset.sum_range_succ, Nat.sub_self,
    extendedOverlapIntensity_diagonal, add_comm]

theorem extendVector_append {j q : ℕ} (x : Fin j → ℝ) (y : Fin q → ℝ) :
    extendVector (Fin.append x y) = appendSequence (x, extendVector y) := by
  have hi (i : Fin (j + q)) :
      extendVector (Fin.append x y) i = appendSequence (x, extendVector y) i := by
    rw [extendVector_apply]
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp [Fin.append_left, appendSequence, k.isLt]
    · simp [Fin.append_right, appendSequence, extendVector,
        show ¬j + (k : ℕ) < j by omega]
  funext i
  by_cases h : i < j + q
  · exact hi ⟨i, h⟩
  · have hj : ¬i < j := by omega
    have hq : ¬i - j < q := by omega
    simp [extendVector, appendSequence, h, hj, hq]

/-- Each common-carrier term is exactly the zero-extension of the finite
shared-prefix/suffix increment measure. -/
theorem extendedOverlapIntensity_eq_map (j q : ℕ) :
    extendedOverlapIntensity j q = (overlapIntensity j q).map extendPair := by
  unfold extendedOverlapIntensity extendedGenerationIntensity overlapIntensity
  rw [Measure.map_prod_map _ _ (measurable_extendVector q) (measurable_extendVector q),
    prod_map_right _ _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map, id_eq, extendPair, appendShared,
    appendSequencePair, extendVector_append]

end FreezingGrowth.PWIT
