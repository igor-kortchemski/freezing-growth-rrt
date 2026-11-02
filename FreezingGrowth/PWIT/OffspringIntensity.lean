module

public import FreezingGrowth.PWIT.Increments
public import FreezingGrowth.PWIT.FirstBirth
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Actual offspring arrival intensities

Child label `i` is born after `i + 1` independent exponential waits. Summing
these actual laws gives Lebesgue measure on the nonnegative half-line. The
joint law of two increasing child labels is obtained from disjoint wait
blocks; independence is not asserted for the two cumulative arrival times.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable def positiveLebesgue : Measure ℝ := volume.restrict (Set.Ici 0)

instance positiveLebesgue_sigmaFinite : SigmaFinite positiveLebesgue := by
  unfold positiveLebesgue
  infer_instance

def rootArrival (i : ℕ) (ω : Sample) : ℝ := clockSum (i + 1) ω

theorem rootArrival_eq_childDelay (i : ℕ) (ω : Sample) :
    rootArrival i ω = childDelay ω [] i := rfl

@[fun_prop] theorem measurable_rootArrival (i : ℕ) : Measurable (rootArrival i) :=
  measurable_clockSum (i + 1)

theorem map_rootArrival (i : ℕ) :
    law.map (rootArrival i) = gammaMeasure ((i : ℝ) + 1) 1 := map_clockSum_succ i

theorem tsum_erlangPDF (x : ℝ) :
    (∑' n, erlangPDF n x) = (Set.Ici 0).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hx : 0 ≤ x
  · have hs : HasSum (fun n : ℕ => x ^ n * Real.exp (-x) / n.factorial) 1 := by
      have he := (NormedSpace.expSeries_div_hasSum_exp x).mul_right (Real.exp (-x))
      rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at he
      simpa only [add_neg_cancel, Real.exp_zero, div_mul_eq_mul_div] using he
    simp only [erlangPDF, hx, ite_true]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
      div_nonneg (mul_nonneg (pow_nonneg hx n) (Real.exp_pos _).le) (Nat.cast_nonneg _))
      hs.summable, hs.tsum_eq]
    simp [hx]
  · simp [erlangPDF, hx]

/-- The first factorial intensity of the actual root's offspring process. -/
theorem sum_rootArrival_law :
    Measure.sum (fun i : ℕ => law.map (rootArrival i)) = positiveLebesgue := by
  have he (i : ℕ) : law.map (rootArrival i) = volume.withDensity (erlangPDF i) := by
    rw [map_rootArrival, gammaMeasure]
    congr 1
    exact funext (gammaPDF_nat_succ i)
  simp only [he]
  rw [← withDensity_tsum measurable_erlangPDF]
  have hf : (∑' i, erlangPDF i) = (Set.Ici 0).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    rw [Pi.tsum_apply (Pi.summable.mpr fun _ => ENNReal.summable)]
    exact tsum_erlangPDF x
  rw [hf]
  change volume.withDensity ((Set.Ici (0 : ℝ)).indicator 1) = _
  rw [withDensity_indicator_one measurableSet_Ici]
  rfl

def rootClockBlock (a b : ℕ) (ω : Sample) : ℝ :=
  ∑ j ∈ Finset.range b, ω ([], a + j)

@[fun_prop] theorem measurable_rootClockBlock (a b : ℕ) : Measurable (rootClockBlock a b) := by
  unfold rootClockBlock
  fun_prop

theorem clockSum_add (a b : ℕ) (ω : Sample) :
    clockSum (a + b) ω = clockSum a ω + rootClockBlock a b ω :=
  Finset.sum_range_add _ _ _

theorem map_rootClockBlock_succ (a b : ℕ) :
    law.map (rootClockBlock a (b + 1)) = gammaMeasure ((b : ℝ) + 1) 1 := by
  have hm : law.map (fun (ω : Sample) j => ω ([], a + j)) = rowLaw :=
    Measure.map_infinitePi_infinitePi_of_inj (by
      intro i j h
      have hh : a + i = a + j := congrArg Prod.snd h
      omega)
  rw [← map_row_sum b, ← hm, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem indep_clockSum_rootClockBlock (a b : ℕ) :
    IndepFun (clockSum a) (rootClockBlock a b) law := by
  have hi := indepFun_reindex (fun i : Fin a => ([], (i : ℕ)))
    (fun j : Fin b => ([], a + j)) (by
      intro i j h
      have hh : (i : ℕ) = a + j := congrArg Prod.snd h
      omega)
  have hs := hi.comp
    (show Measurable (fun x : Fin a → ℝ => ∑ i, x i) by fun_prop)
    (show Measurable (fun x : Fin b → ℝ => ∑ i, x i) by fun_prop)
  have h₁ : (fun ω : Sample => ∑ i : Fin a, ω ([], i)) = clockSum a := by
    funext ω
    exact (Finset.sum_range (fun i : ℕ => ω ([], i))).symm
  have h₂ : (fun ω : Sample => ∑ i : Fin b, ω ([], a + i)) = rootClockBlock a b := by
    funext ω
    exact (Finset.sum_range (fun i : ℕ => ω ([], a + i))).symm
  change IndepFun (fun ω : Sample => ∑ i : Fin a, ω ([], i))
    (fun ω : Sample => ∑ i : Fin b, ω ([], a + i)) law at hs
  rwa [h₁, h₂] at hs

theorem rootClockBlocks_joint_law (i m : ℕ) :
    law.map (fun ω => (clockSum (i + 1) ω, rootClockBlock (i + 1) (m + 1) ω)) =
      (gammaMeasure ((i : ℝ) + 1) 1).prod (gammaMeasure ((m : ℝ) + 1) 1) := by
  rw [(indep_clockSum_rootClockBlock (i + 1) (m + 1)).map_prod_eq_prod_map_map
    (measurable_clockSum _).aemeasurable (measurable_rootClockBlock _ _).aemeasurable,
    map_clockSum_succ, map_rootClockBlock_succ]

/-- The second arrival is the first arrival plus an independent Gamma block.
The shapes are `i + 1` and `m + 1` for child labels `i < i + m + 1`. -/
theorem rootArrival_ascending_joint_law (i m : ℕ) :
    law.map (fun ω => (rootArrival i ω, rootArrival (i + m + 1) ω)) =
      ((gammaMeasure ((i : ℝ) + 1) 1).prod (gammaMeasure ((m : ℝ) + 1) 1)).map
        (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) := by
  have he : (fun ω => (rootArrival i ω, rootArrival (i + m + 1) ω)) =
      (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ∘
        (fun ω => (clockSum (i + 1) ω, rootClockBlock (i + 1) (m + 1) ω)) := by
    funext ω
    dsimp only [Function.comp_apply, rootArrival]
    rw [show i + m + 1 + 1 = (i + 1) + (m + 1) by omega]
    exact congrArg (Prod.mk (clockSum (i + 1) ω)) (clockSum_add (i + 1) (m + 1) ω)
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), rootClockBlocks_joint_law]

def ascendingBirthTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}

def descendingBirthTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}

theorem measurableSet_ascendingBirthTriangle : MeasurableSet ascendingBirthTriangle :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_snd)

theorem measurableSet_descendingBirthTriangle : MeasurableSet descendingBirthTriangle :=
  (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)

theorem positiveLebesgue_prod_map_shear :
    (positiveLebesgue.prod positiveLebesgue).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) =
      ((volume : Measure ℝ).prod volume).restrict ascendingBirthTriangle := by
  have hm := (measurePreserving_prod_add (volume : Measure ℝ) volume).restrict_preimage
    measurableSet_ascendingBirthTriangle
  have he : (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ⁻¹' ascendingBirthTriangle =
      Set.Ici 0 ×ˢ Set.Ici 0 := by
    ext p
    change (0 ≤ p.1 ∧ p.1 ≤ p.1 + p.2) ↔ (0 ≤ p.1 ∧ 0 ≤ p.2)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he] at hm
  simpa only [positiveLebesgue, Measure.prod_restrict] using hm.map_eq

theorem ascendingBirthTriangle_map_swap :
    (((volume : Measure ℝ).prod volume).restrict ascendingBirthTriangle).map Prod.swap =
      ((volume : Measure ℝ).prod volume).restrict descendingBirthTriangle := by
  have hm := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).restrict_preimage
    measurableSet_descendingBirthTriangle
  exact hm.map_eq

theorem birthTriangles_add :
    ((volume : Measure ℝ).prod volume).restrict ascendingBirthTriangle +
      ((volume : Measure ℝ).prod volume).restrict descendingBirthTriangle =
      positiveLebesgue.prod positiveLebesgue := by
  have hd : ((volume : Measure ℝ).prod volume) (Set.diagonal ℝ) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    have hs (x : ℝ) : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
      ext y
      change x = y ↔ y = x
      exact eq_comm
    simp_rw [hs, measure_singleton]
    simp
  have hn : ((volume : Measure ℝ).prod volume)
      (ascendingBirthTriangle ∩ descendingBirthTriangle) = 0 := by
    apply measure_mono_null _ hd
    intro p hp
    exact le_antisymm hp.1.2 hp.2.2
  have hu : ascendingBirthTriangle ∪ descendingBirthTriangle = Set.Ici 0 ×ˢ Set.Ici 0 := by
    ext p
    change ((0 ≤ p.1 ∧ p.1 ≤ p.2) ∨ (0 ≤ p.2 ∧ p.2 ≤ p.1)) ↔
      (0 ≤ p.1 ∧ 0 ≤ p.2)
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
    · intro h
      rcases le_total p.1 p.2 with hp | hp
      · exact Or.inl ⟨h.1, hp⟩
      · exact Or.inr ⟨h.2, hp⟩
  have hr := Measure.restrict_union_add_inter
    (μ := (volume : Measure ℝ).prod volume) ascendingBirthTriangle
    measurableSet_descendingBirthTriangle
  rw [hu, Measure.restrict_eq_zero.mpr hn, add_zero] at hr
  simpa only [positiveLebesgue, Measure.prod_restrict] using hr.symm

/-- Sum over both labels of an increasing pair. The rank cancellation occurs
here, after the two independent Gamma shapes have both been summed. -/
theorem sum_ascending_rootArrival_law :
    Measure.sum (fun p : ℕ × ℕ =>
      law.map (fun ω => (rootArrival p.1 ω, rootArrival (p.1 + p.2 + 1) ω))) =
      ((volume : Measure ℝ).prod volume).restrict ascendingBirthTriangle := by
  have he : (fun p : ℕ × ℕ =>
      law.map (fun ω => (rootArrival p.1 ω, rootArrival (p.1 + p.2 + 1) ω))) =
      fun p => ((law.map (rootArrival p.1)).prod (law.map (rootArrival p.2))).map
        (fun q : ℝ × ℝ => (q.1, q.1 + q.2)) := by
    funext p
    rw [rootArrival_ascending_joint_law, map_rootArrival, map_rootArrival]
  rw [he, ← Measure.map_sum (by fun_prop),
    ← Measure.prod_sum (fun i : ℕ => law.map (rootArrival i))
      (fun i : ℕ => law.map (rootArrival i)),
    sum_rootArrival_law, positiveLebesgue_prod_map_shear]

abbrev DistinctChildPair := {p : ℕ × ℕ // p.1 ≠ p.2}

def childPairEquiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ DistinctChildPair where
  toFun
    | Sum.inl p => ⟨(p.1, p.1 + p.2 + 1), by omega⟩
    | Sum.inr p => ⟨(p.1 + p.2 + 1, p.1), by omega⟩
  invFun p := if p.1.1 < p.1.2 then Sum.inl (p.1.1, p.1.2 - p.1.1 - 1)
    else Sum.inr (p.1.2, p.1.1 - p.1.2 - 1)
  left_inv p := by
    cases p with
    | inl p =>
      simp only [show p.1 < p.1 + p.2 + 1 by omega, ite_true]
      congr 2; omega
    | inr p =>
      simp only [show ¬p.1 + p.2 + 1 < p.1 by omega, ite_false]
      congr 2; omega
  right_inv p := by
    dsimp only
    split_ifs with hp
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change p.1.1 + (p.1.2 - p.1.1 - 1) + 1 = p.1.2
        omega
    · apply Subtype.ext
      have hne := p.2
      apply Prod.ext
      · change p.1.2 + (p.1.1 - p.1.2 - 1) + 1 = p.1.1
        omega
      · rfl

noncomputable def offspringPairIntensity : Measure (ℝ × ℝ) :=
  Measure.sum fun p : DistinctChildPair =>
    law.map (fun ω => (rootArrival p.1.1 ω, rootArrival p.1.2 ω))

private theorem measure_sum_sumElim {ι κ α : Type*} [MeasurableSpace α]
    (μ : ι → Measure α) (ν : κ → Measure α) :
    Measure.sum (Sum.elim μ ν) = Measure.sum μ + Measure.sum ν := by
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.add_apply]
  exact ENNReal.summable.tsum_sum ENNReal.summable

/-- Ordered distinct offspring have factorial intensity `ds dt`. This is an
identity of actual laws, rather than a Poisson-process representation premise. -/
theorem offspringPairIntensity_eq :
    offspringPairIntensity = positiveLebesgue.prod positiveLebesgue := by
  let A : Measure (ℝ × ℝ) := Measure.sum (fun p : ℕ × ℕ =>
    law.map (fun ω => (rootArrival p.1 ω, rootArrival (p.1 + p.2 + 1) ω)))
  have ha : A = ((volume : Measure ℝ).prod volume).restrict ascendingBirthTriangle :=
    sum_ascending_rootArrival_law
  have hswap : A.map Prod.swap = Measure.sum (fun p : ℕ × ℕ =>
      law.map (fun ω => (rootArrival (p.1 + p.2 + 1) ω, rootArrival p.1 ω))) := by
    rw [Measure.map_sum (by fun_prop)]
    congr 1
    funext p
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have he : offspringPairIntensity = A + A.map Prod.swap := by
    unfold offspringPairIntensity
    rw [← Measure.sum_comp_equiv childPairEquiv]
    have hf : ((fun p : DistinctChildPair => law.map (fun ω =>
        (rootArrival p.1.1 ω, rootArrival p.1.2 ω))) ∘ childPairEquiv) = Sum.elim
      (fun p : ℕ × ℕ => law.map (fun ω => (rootArrival p.1 ω, rootArrival (p.1 + p.2 + 1) ω)))
      (fun p : ℕ × ℕ => law.map (fun ω => (rootArrival (p.1 + p.2 + 1) ω, rootArrival p.1 ω))) := by
      funext p
      cases p <;> rfl
    rw [hf, measure_sum_sumElim, ← hswap]
  rw [he, ha, ascendingBirthTriangle_map_swap, birthTriangles_add]

theorem map_childSample (i : ℕ) : law.map (fun ω => childSample ω i) = law :=
  Measure.map_infinitePi_infinitePi_of_inj (by
    rintro ⟨v, a⟩ ⟨w, b⟩ h
    simpa using h)

theorem indep_childSamples {i j : ℕ} (hij : i ≠ j) :
    IndepFun (fun ω => childSample ω i) (fun ω => childSample ω j) law :=
  indepFun_reindex (fun c : Coordinate => (i :: c.1, c.2))
    (fun c : Coordinate => (j :: c.1, c.2)) (by
    intro c e h
    exact hij (List.cons.inj (congrArg Prod.fst h)).1)

theorem indep_rootArrival_childSample (i j : ℕ) :
    IndepFun (rootArrival i) (fun ω => childSample ω j) law := by
  have hi := indepFun_reindex (fun k : ℕ => ([], k))
    (fun c : Coordinate => (j :: c.1, c.2)) (by intro k c h; simp at h)
  exact hi.comp (show Measurable (fun x : ℕ → ℝ => ∑ k ∈ Finset.range (i + 1), x k) by
    fun_prop) measurable_id

/-- The complete descendant sample is independent of its root waiting time. -/
theorem rootArrival_childSample_joint_law (i : ℕ) :
    law.map (fun ω => (rootArrival i ω, childSample ω i)) =
      (law.map (rootArrival i)).prod law := by
  rw [(indep_rootArrival_childSample i i).map_prod_eq_prod_map_map
    (measurable_rootArrival i).aemeasurable (measurable_childSample i).aemeasurable,
    map_childSample]

theorem indep_rootArrivalPair_childSamples (i j : ℕ) :
    IndepFun (fun ω => (rootArrival i ω, rootArrival j ω))
      (fun ω => (childSample ω i, childSample ω j)) law := by
  let rest : Coordinate ⊕ Coordinate → Coordinate :=
    Sum.elim (fun c => (i :: c.1, c.2)) (fun c => (j :: c.1, c.2))
  have hi := indepFun_reindex (fun k : ℕ => ([], k)) rest (by
    intro k c h
    cases c <;> simp [rest] at h)
  exact hi.comp
    (show Measurable (fun x : ℕ → ℝ =>
      (∑ k ∈ Finset.range (i + 1), x k, ∑ k ∈ Finset.range (j + 1), x k)) by fun_prop)
    ((Measurable.of_eval fun c => measurable_pi_apply (Sum.inl c)).prodMk
      (Measurable.of_eval fun c => measurable_pi_apply (Sum.inr c)))

/-- Actual joint regrouping for a split into two distinct children. Only the
descendant samples factor; the two cumulative root arrivals retain their joint law. -/
theorem rootArrivals_childSamples_joint_law {i j : ℕ} (hij : i ≠ j) :
    law.map (fun ω => ((rootArrival i ω, rootArrival j ω),
      (childSample ω i, childSample ω j))) =
      (law.map (fun ω => (rootArrival i ω, rootArrival j ω))).prod (law.prod law) := by
  rw [(indep_rootArrivalPair_childSamples i j).map_prod_eq_prod_map_map
    ((measurable_rootArrival i).prodMk (measurable_rootArrival j)).aemeasurable
    ((measurable_childSample i).prodMk (measurable_childSample j)).aemeasurable,
    (indep_childSamples hij).map_prod_eq_prod_map_map
      (measurable_childSample i).aemeasurable (measurable_childSample j).aemeasurable,
    map_childSample, map_childSample]

end FreezingGrowth.PWIT
