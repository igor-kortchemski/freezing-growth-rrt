module

public import FreezingGrowth.ReverseDelayedLongerLaw
public import FreezingGrowth.ReverseHistoryPair

/-! The genuine pending-pair metadata. After first use its old indices are
discarded; before first use they remain the original positive positions. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

abbrev PendingTag := Option (ℕ × ℕ)

instance : MeasurableSpace PendingTag := ⊤
instance : DiscreteMeasurableSpace PendingTag := ⟨fun _ => trivial⟩

def pendingTag (z : InitializationSample) : PendingTag :=
  if z.used then none else some z.delayedPair

def freshPendingTag (p : ℕ × ℕ) : PendingTag :=
  if p.1 = 0 ∨ p.2 = 0 then none else some p

def positivePositions (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).erase 0

theorem mem_positivePositions {N a : ℕ} :
    a ∈ positivePositions N ↔ 0 < a ∧ a ≤ N := by
  simp only [positivePositions, Finset.mem_erase, Finset.mem_range]
  omega

theorem positivePositions_eq_Icc (N : ℕ) : positivePositions N = Finset.Icc 1 N := by
  ext a
  rw [mem_positivePositions, Finset.mem_Icc]
  omega

@[simp] theorem positivePositions_card (N : ℕ) : (positivePositions N).card = N := by
  rw [positivePositions, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega))]
  simp

noncomputable def positivePairLaw (N : ℕ) : Measure (ℕ × ℕ) :=
  uniformRootPair (positivePositions N)

def lowerPair (p : ℕ × ℕ) : ℕ × ℕ := (p.1 - 1, p.2 - 1)

theorem positivePairLaw_lowerPair (N : ℕ) :
    (positivePairLaw N).map lowerPair = uniformRootPair (Finset.range N) := by
  have hinj : Set.InjOn lowerPair (positivePositions N).offDiag := by
    intro p hp q hq he
    obtain ⟨hpa, hpb, _⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hqa, hqb, _⟩ := Finset.mem_offDiag.mp hq
    have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    have hpa' := (mem_positivePositions.mp hpa).1
    have hpb' := (mem_positivePositions.mp hpb).1
    have hqa' := (mem_positivePositions.mp hqa).1
    have hqb' := (mem_positivePositions.mp hqb).1
    apply Prod.ext <;> dsimp [lowerPair] at ha hb ⊢ <;> omega
  have himage : ((positivePositions N).offDiag.image lowerPair) = (Finset.range N).offDiag := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hq
      have ha' := mem_positivePositions.mp ha
      have hb' := mem_positivePositions.mp hb
      apply Finset.mem_offDiag.mpr
      simp only [lowerPair, Finset.mem_range]
      omega
    · intro hp
      obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      refine Finset.mem_image.mpr ⟨(p.1 + 1, p.2 + 1), ?_, ?_⟩
      · apply Finset.mem_offDiag.mpr
        simp only [mem_positivePositions]
        omega
      · simp [lowerPair]
  unfold positivePairLaw uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _) hinj, himage]

noncomputable def freshPendingLaw (N : ℕ) : Measure PendingTag :=
  (uniformRootPair (Finset.range N)).map freshPendingTag

/-- The avoidance weight of a fresh pair in an N-component forest. -/
noncomputable def pendingWeight (N : ℕ) : ℝ≥0∞ :=
  ((N - 2 : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)

theorem uniformPositionPair_avoid_mass (N : ℕ) (hN : 2 ≤ N) :
    (uniformRootPair (Finset.range N)) (avoidsDistinguished 0) = pendingWeight N := by
  rw [uniformRootPair, Measure.uniformOfFinset_apply,
    offDiag_filter_avoidsDistinguished,
    offDiag_erase_card_ratio _ (Finset.mem_range.mpr (by omega)) (by simpa using hN)]
  simp only [Finset.card_range, pendingWeight]

theorem pendingWeight_le_one (N : ℕ) (hN : 2 ≤ N) : pendingWeight N ≤ 1 := by
  let := uniformRootPair_isProbabilityMeasure (Finset.range N) (by simpa using hN)
  rw [← uniformPositionPair_avoid_mass N hN]
  exact prob_le_one

/-- The full fresh flag/pair law, including zero pending mass at N=2. -/
theorem freshPendingLaw_eq (N : ℕ) (hN : 2 ≤ N) :
    freshPendingLaw N =
      (1 - pendingWeight N) • Measure.dirac none +
        pendingWeight N • (positivePairLaw (N - 1)).map some := by
  let μ := uniformRootPair (Finset.range N)
  let A : Set (ℕ × ℕ) := avoidsDistinguished 0
  let := uniformRootPair_isProbabilityMeasure (Finset.range N) (by simpa using hN)
  have hμ : μ A = pendingWeight N := uniformPositionPair_avoid_mass N hN
  have hrestrict : μ.restrict A = pendingWeight N • positivePairLaw (N - 1) := by
    have hh := uniformRootPair_restrict_avoidsDistinguished (Finset.range N)
      (Finset.mem_range.mpr (by omega : 0 < N)) (by simpa using hN)
    simpa only [Finset.card_range, pendingWeight, positivePairLaw, positivePositions,
      show N - 1 + 1 = N by omega] using hh
  have hused : (μ.restrict Aᶜ).map freshPendingTag =
      (1 - pendingWeight N) • Measure.dirac none := by
    have he : (μ.restrict Aᶜ).map freshPendingTag =
        (μ.restrict Aᶜ).map (fun _ => (none : PendingTag)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (MeasurableSet.of_discrete : MeasurableSet Aᶜ)] with p hp
      have hp' : p.1 = 0 ∨ p.2 = 0 := by
        simpa only [A, avoidsDistinguished, Set.mem_compl_iff, Set.mem_ofPred_eq,
          not_and_or, not_not] using hp
      simp only [freshPendingTag, ite_eq_left hp']
    rw [he, Measure.map_const, Measure.restrict_apply_univ,
      measure_compl MeasurableSet.of_discrete (measure_ne_top μ A), hμ]
    simp only [μ, measure_univ]
  have hpending : (μ.restrict A).map freshPendingTag =
      pendingWeight N • (positivePairLaw (N - 1)).map some := by
    have he : (μ.restrict A).map freshPendingTag = (μ.restrict A).map some := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (MeasurableSet.of_discrete : MeasurableSet A)] with p hp
      have hp' : ¬(p.1 = 0 ∨ p.2 = 0) := by
        simpa only [A, avoidsDistinguished, Set.mem_ofPred_eq, not_or] using hp
      simp only [freshPendingTag, ite_eq_right hp']
    rw [he, hrestrict, Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  calc
    freshPendingLaw N = (μ.restrict Aᶜ + μ.restrict A).map freshPendingTag := by
      rw [Measure.restrict_compl_add_restrict MeasurableSet.of_discrete]
      rfl
    _ = _ := by rw [Measure.map_add _ _ (measurable_of_countable _), hused, hpending]

theorem pendingTag_initializationChoice (F : Forest) (i : ℕ)
    (p : Fin (prependLabel F i).forest.roots.card × Fin (prependLabel F i).forest.roots.card) :
    pendingTag (initializationChoice F i p) = freshPendingTag (p.1.val, p.2.val) := by
  simp [pendingTag, initializationChoice, freshPendingTag]

theorem initializationLaw_pendingTag (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    (initializationLaw F i).map pendingTag = freshPendingLaw (F.forest.roots.card + 1) := by
  rw [initializationLaw, Measure.map_map measurable_from_top (measurable_of_countable _)]
  have he : pendingTag ∘ initializationChoice F i =
      freshPendingTag ∘ ReverseHeightList.finPairValues := by
    funext p
    exact pendingTag_initializationChoice F i p
  rw [he, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ReverseHeightList.map_uniformRootPair_finPairValues, prependLabel_roots_card F hi]
  rfl

/-- The initial shorter forest is fixed while its fresh pending metadata has
the actual finite-pair law. This independence is derived from the sampler. -/
theorem initializationLaw_shorter_pendingTag (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) :
    (initializationLaw F i).map (fun z => (z.shorter, pendingTag z)) =
      (freshPendingLaw (F.forest.roots.card + 1)).map (fun q => (F, q)) := by
  rw [← initializationLaw_pendingTag F hi,
    Measure.map_map (measurable_of_countable _) measurable_from_top]
  apply Measure.map_congr
  unfold initializationLaw
  apply (ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

end FreezingGrowth.ReverseOrdered
