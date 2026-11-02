module

public import FreezingGrowth.ProfileCompute
public import FreezingGrowth.FiniteLowProfile
public import FreezingGrowth.FirstPeakDeletion

/-!
# Probability semantics of exact integer profile enumeration

Integer weights count equally likely choice histories. Aggregation preserves
the entire finite measure, including repeated rows. Normalization uses the
total integer weight; the common active population justifies every transition.
-/

@[expose] public section

namespace FreezingGrowth.ProfileCompute

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable def listDiracs {α : Type*} [MeasurableSpace α] (xs : List α) : Measure α :=
  (xs.map Measure.dirac).sum

@[simp] theorem listDiracs_nil {α : Type*} [MeasurableSpace α] :
    listDiracs ([] : List α) = 0 := rfl

@[simp] theorem listDiracs_cons {α : Type*} [MeasurableSpace α] (x : α) (xs : List α) :
    listDiracs (x :: xs) = Measure.dirac x + listDiracs xs := rfl

theorem map_listDiracs {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (xs : List α) :
    (listDiracs xs).map f = listDiracs (xs.map f) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [listDiracs_cons, List.map_cons, Measure.map_add _ _ hf,
      Measure.map_dirac' hf, ih]

theorem ofMultiset_eq_inverse_smul {α : Type*} [MeasurableSpace α]
    (s : Multiset α) :
    Measure.ofMultiset s = (s.card : ℝ≥0∞)⁻¹ • (s.map Measure.dirac).sum := by
  classical
  rw [Measure.ofMultiset, Finset.sum_multiset_map_count, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, div_eq_mul_inv, mul_comm]

/-- Uniform occurrence sampling is exactly the mathematical profile kernel. -/
theorem transition_eq_branch_average (p : ProfileCode) (sign : Bool) :
    HeightProfile.transitionLaw p.decode sign =
      ((p.branches sign).length : ℝ≥0∞)⁻¹ •
        listDiracs ((p.branches sign).map ProfileCode.decode) := by
  by_cases he : p.activeDepths = []
  · have hm : p.decode.activeDepths = 0 := by simp [ProfileCode.decode, he]
    simp [HeightProfile.transitionLaw, hm, ProfileCode.branches_eq_of_empty p sign he]
  · have hm : p.decode.activeDepths ≠ 0 := by
      intro h
      have hc := congrArg Multiset.card h
      have hl : p.activeDepths.length = 0 := by simpa [ProfileCode.decode] using hc
      exact he (List.length_eq_zero_iff.mp hl)
    rw [HeightProfile.transitionLaw, ite_eq_right hm, ofMultiset_eq_inverse_smul,
      Measure.map_smul _ measurable_from_top.aemeasurable]
    change (p.activeDepths.length : ℝ≥0∞)⁻¹ •
      (listDiracs p.activeDepths).map (HeightProfile.step p.decode sign) = _
    rw [map_listDiracs _ measurable_from_top,
      ProfileCode.branches_eq_of_nonempty p sign he]
    simp only [List.length_map, List.map_map, Function.comp_def, ProfileCode.decode_step]

noncomputable def tableMeasure (D : WeightedCounts) : Measure HeightProfile :=
  weightedSum (fun p => Measure.dirac p.decode) D

@[simp] theorem tableMeasure_nil : tableMeasure [] = 0 := rfl

@[simp] theorem tableMeasure_cons (p : ProfileCode) (w : ℕ) (D : WeightedCounts) :
    tableMeasure ((p, w) :: D) = w • Measure.dirac p.decode + tableMeasure D := rfl

theorem tableMeasure_aggregate (D : WeightedCounts) :
    tableMeasure (aggregate D) = tableMeasure D := weightedSum_aggregate _ D

theorem bind_add_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (K : α → Measure β) (hK : Measurable K) :
    (μ + ν).bind K = μ.bind K + ν.bind K := by
  ext s hs
  simp only [Measure.bind_apply hs hK.aemeasurable, Measure.add_apply,
    lintegral_add_measure]

theorem tableMeasure_bind (D : WeightedCounts) (K : HeightProfile → Measure HeightProfile) :
    (tableMeasure D).bind K = weightedSum (fun p => K p.decode) D := by
  induction D with
  | nil => simp [Measure.bind_zero_left]
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    rw [tableMeasure_cons, bind_add_measurable _ _ _ measurable_from_top,
      Measure.bind_smul w _ measurable_from_top.aemeasurable,
      Measure.dirac_bind measurable_from_top, ih, weightedSum_cons]

theorem weightedSum_congr {A : Type*} [AddCommMonoid A] {f g : ProfileCode → A}
    (D : WeightedCounts) (h : ∀ row ∈ D, f row.1 = g row.1) :
    weightedSum f D = weightedSum g D := by
  unfold weightedSum
  congr 1
  exact List.map_congr_left (fun row hr => congrArg (row.2 • ·) (h row hr))

theorem weightedSum_smul (D : WeightedCounts) (c : ℝ≥0∞)
    (f : ProfileCode → Measure HeightProfile) :
    weightedSum (fun p => c • f p) D = c • weightedSum f D := by
  induction D with
  | nil => simp
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    simp only [weightedSum_cons, ih, smul_add, smul_comm c w]

/-- The common branch count permits a single normalization factor for the table. -/
theorem tableMeasure_next (D : WeightedCounts) (sign : Bool) (a : ℕ)
    (hD : ∀ row ∈ D, row.1.activeDepths.length = a) :
    (tableMeasure D).bind (fun p => HeightProfile.transitionLaw p sign) =
      ((max a 1 : ℕ) : ℝ≥0∞)⁻¹ • tableMeasure (next sign D) := by
  rw [tableMeasure_bind]
  simp_rw [transition_eq_branch_average]
  have h := weightedSum_congr D (f := fun p =>
      ((p.branches sign).length : ℝ≥0∞)⁻¹ • listDiracs ((p.branches sign).map ProfileCode.decode))
    (g := fun p => ((max a 1 : ℕ) : ℝ≥0∞)⁻¹ • listDiracs ((p.branches sign).map ProfileCode.decode))
    (by intro row hr; rw [ProfileCode.branches_length, hD row hr])
  rw [h, weightedSum_smul]
  congr 1
  rw [tableMeasure, weightedSum_next]
  simp only [listDiracs, List.map_map, Function.comp_def]

/-- The deterministic active population, with extinction absorbing. -/
def populationStep (a : ℕ) (sign : Bool) : ℕ :=
  if a = 0 then 0 else if sign then a + 1 else a - 1

def population (signs : Word) : ℕ := signs.foldl populationStep 1

@[simp] theorem population_nil : population [] = 1 := rfl

theorem population_append_singleton (signs : Word) (sign : Bool) :
    population (signs ++ [sign]) = populationStep (population signs) sign := by
  simp [population, List.foldl_append]

theorem next_population (D : WeightedCounts) (sign : Bool) (a : ℕ)
    (hD : ∀ row ∈ D, row.1.activeDepths.length = a) :
    ∀ row ∈ next sign D, row.1.activeDepths.length = populationStep a sign := by
  unfold next
  apply property_aggregate (fun p => p.activeDepths.length = populationStep a sign)
  intro row hr
  obtain ⟨old, ho, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  have ha := hD old ho
  by_cases hz : a = 0
  · simpa [populationStep, hz] using
      ProfileCode.branches_active_length_of_zero sign (ha.trans hz) hq
  · have hp : 0 < old.1.activeDepths.length := by omega
    simpa [populationStep, hz, ha] using
      ProfileCode.branches_active_length_of_pos sign hp hq

theorem run_population (signs : Word) :
    ∀ row ∈ run signs, row.1.activeDepths.length = population signs := by
  induction signs using List.reverseRecOn with
  | nil => simp [run, ProfileCode.initial, population]
  | append_singleton signs sign ih =>
    rw [run_append_singleton, population_append_singleton]
    exact next_population _ _ _ ih

theorem weightedSum_const (D : WeightedCounts) (a : ℕ) :
    weightedSum (fun _ => a) D = totalWeight D * a := by
  induction D with
  | nil => simp [totalWeight]
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    simp [weightedSum_cons, totalWeight, ih, add_mul]

theorem totalWeight_next (D : WeightedCounts) (sign : Bool) (a : ℕ)
    (hD : ∀ row ∈ D, row.1.activeDepths.length = a) :
    totalWeight (next sign D) = totalWeight D * max a 1 := by
  rw [totalWeight_eq_weightedSum, weightedSum_next]
  calc
    _ = weightedSum (fun _ => max a 1) D := by
      apply weightedSum_congr
      intro row hr
      simp [ProfileCode.branches_length, hD row hr]
    _ = _ := weightedSum_const D _

/-- Population and the common denominator can be computed without enumerating
any tree profile. The factor is one after extinction, matching absorption. -/
def populationMass (signs : Word) : ℕ × ℕ :=
  signs.foldl (fun q sign => (populationStep q.1 sign, q.2 * max q.1 1)) (1, 1)

theorem populationMass_append_singleton (signs : Word) (sign : Bool) :
    populationMass (signs ++ [sign]) =
      (populationStep (populationMass signs).1 sign,
        (populationMass signs).2 * max (populationMass signs).1 1) := by
  simp [populationMass, List.foldl_append]

theorem populationMass_eq (signs : Word) :
    populationMass signs = (population signs, totalWeight (run signs)) := by
  induction signs using List.reverseRecOn with
  | nil => rfl
  | append_singleton signs sign ih =>
    rw [populationMass_append_singleton, ih, population_append_singleton,
      run_append_singleton, totalWeight_next _ _ _ (run_population signs)]

theorem totalWeight_run_eq_populationMass (signs : Word) :
    totalWeight (run signs) = (populationMass signs).2 :=
  (congrArg Prod.snd (populationMass_eq signs)).symm

theorem totalWeight_run_pos (signs : Word) : 0 < totalWeight (run signs) := by
  induction signs using List.reverseRecOn with
  | nil => simp [run, totalWeight]
  | append_singleton signs sign ih =>
    rw [run_append_singleton, totalWeight_next _ _ _ (run_population signs)]
    exact Nat.mul_pos ih (by omega)

theorem profile_law_congr {x y : SignSequence} {n : ℕ}
    (h : ∀ i < n, x (i + 1) = y (i + 1)) :
    HeightProfile.law x n = HeightProfile.law y n := by
  rw [← HeightProfile.map_treeLaw, ← HeightProfile.map_treeLaw, Forward.treeLaw_congr h]

theorem profile_law_append_singleton (signs : Word) (sign : Bool) :
    HeightProfile.law (Word.toSigns (signs ++ [sign])) (signs ++ [sign]).length =
      (HeightProfile.law signs.toSigns signs.length).bind
        (fun p => HeightProfile.transitionLaw p sign) := by
  simp only [List.length_append, List.length_singleton, HeightProfile.law]
  have hp : HeightProfile.law (Word.toSigns (signs ++ [sign])) signs.length =
      HeightProfile.law signs.toSigns signs.length :=
    profile_law_congr (fun i hi => Word.toSigns_append_left signs [sign] hi)
  have hl := Word.toSigns_append_right signs [sign] 0
  simp only [Nat.add_zero, Word.toSigns_succ, List.getElem?_cons_zero,
    Option.getD_some] at hl
  rw [hp, Word.toSigns_succ, hl]

/-- Exact normalized law of the integer enumeration, including extinct words. -/
theorem run_normalized_law (signs : Word) :
    HeightProfile.law signs.toSigns signs.length =
      (totalWeight (run signs) : ℝ≥0∞)⁻¹ • tableMeasure (run signs) := by
  induction signs using List.reverseRecOn with
  | nil => simp [HeightProfile.law, totalWeight, tableMeasure, weightedSum,
      ProfileCode.decode_initial]
  | append_singleton signs sign ih =>
    rw [profile_law_append_singleton, ih,
      Measure.bind_smul _ _ measurable_from_top.aemeasurable,
      tableMeasure_next _ _ _ (run_population signs), run_append_singleton,
      totalWeight_next _ _ _ (run_population signs), smul_smul, Nat.cast_mul]
    congr 1
    exact (ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))).symm

theorem tableMeasure_integrable (D : WeightedCounts) (f : HeightProfile → ℝ) :
    Integrable f (tableMeasure D) := by
  induction D with
  | nil => simp
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    rw [tableMeasure_cons, ← Nat.cast_smul_eq_nsmul ℝ≥0∞]
    exact ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure ih

theorem tableMeasure_integral (D : WeightedCounts) (f : HeightProfile → ℝ) :
    (∫ p, f p ∂tableMeasure D) = weightedSum (fun p => f p.decode) D := by
  induction D with
  | nil => simp
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    rw [tableMeasure_cons, ← Nat.cast_smul_eq_nsmul ℝ≥0∞,
      integral_add_measure
        ((integrable_dirac (by simp)).smul_measure (by simp))
        (tableMeasure_integrable D f), integral_smul_measure, integral_dirac, ih,
      weightedSum_cons]
    simp [nsmul_eq_mul]

theorem tableMeasure_integral_maximum (D : WeightedCounts) :
    (∫ p, (p.maximum : ℝ) ∂tableMeasure D) = (heightWeight D : ℝ) := by
  rw [tableMeasure_integral]
  simp [weightedSum, heightWeight, ProfileCode.decode, nsmul_eq_mul, Function.comp_def]

/-- A certified integer computation gives the actual expected tree height. -/
theorem expectedHeight_eq_integer_ratio (signs : Word) :
    signs.expectedHeight =
      (heightWeight (run signs) : ℝ) / (totalWeight (run signs) : ℝ) := by
  unfold Word.expectedHeight Word.heightLaw
  rw [← HeightProfile.map_law_maximum,
    integral_map measurable_from_top.aemeasurable
      measurable_from_top.aestronglyMeasurable,
    run_normalized_law, integral_smul_measure, tableMeasure_integral_maximum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- Use a checked simultaneous count/height statistic without recomputing it. -/
theorem expectedHeight_eq_of_statistics (signs : Word) (mass weighted : ℕ)
    (h : statistics (run signs) = (mass, weighted)) :
    signs.expectedHeight = (weighted : ℝ) / (mass : ℝ) := by
  rw [statistics_eq] at h
  have hm : totalWeight (run signs) = mass := congrArg Prod.fst h
  have hw : heightWeight (run signs) = weighted := congrArg Prod.snd h
  rw [expectedHeight_eq_integer_ratio, hw, hm]

end FreezingGrowth.ProfileCompute
