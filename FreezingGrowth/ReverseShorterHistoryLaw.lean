module

public import FreezingGrowth.ReverseShorterView

/-! The full shorter-history/pending-pair product invariant. Independence
is proved relative to the shorter history, never to the full coupled past. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory
open scoped Classical ENNReal

private theorem bind_add_left_discrete {α β : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (K : α → Measure β) :
    (μ + ν).bind K = μ.bind K + ν.bind K := by
  ext s hs
  simp only [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.add_apply, lintegral_add_measure]

private theorem bind_add_right_discrete {α β : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (K L : α → Measure β) :
    μ.bind (fun a => K a + L a) = μ.bind K + μ.bind L := by
  ext s hs
  simp only [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, Measure.add_apply]
  exact lintegral_add_left Measurable.of_discrete _

private theorem bind_smul_right_discrete {α β : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (c : ℝ≥0∞) (K : α → Measure β) :
    μ.bind (fun a => c • K a) = c • μ.bind K := by
  ext s hs
  simp only [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    Measure.smul_apply, smul_eq_mul]
  exact lintegral_const_mul c Measurable.of_discrete

noncomputable def taggedHistoryLaw (ν : Measure (FiniteMarkov.History Forest))
    (η : Measure PendingTag) : Measure ShorterView :=
  ν.bind (fun h => η.map (fun q => (⟨h, q⟩ : ShorterView)))

noncomputable def pendingMetadataLaw (N : ℕ) (a b : ℝ≥0∞) : Measure PendingTag :=
  a • Measure.dirac none + b • (positivePairLaw N).map some

theorem pendingMetadataLaw_step (N : ℕ) (hN : 2 ≤ N) (a b : ℝ≥0∞) :
    a • Measure.dirac none + b • freshPendingLaw N =
      pendingMetadataLaw (N - 1)
        (a + b * (1 - pendingWeight N)) (b * pendingWeight N) := by
  rw [freshPendingLaw_eq N hN]
  simp only [pendingMetadataLaw, smul_add, smul_smul, add_smul, add_assoc]

theorem taggedHistoryLaw_add (ν : Measure (FiniteMarkov.History Forest))
    (η θ : Measure PendingTag) :
    taggedHistoryLaw ν (η + θ) = taggedHistoryLaw ν η + taggedHistoryLaw ν θ := by
  unfold taggedHistoryLaw
  simp only [Measure.map_add _ _ (measurable_of_countable _)]
  exact bind_add_right_discrete ν _ _

theorem taggedHistoryLaw_smul (ν : Measure (FiniteMarkov.History Forest))
    (c : ℝ≥0∞) (η : Measure PendingTag) :
    taggedHistoryLaw ν (c • η) = c • taggedHistoryLaw ν η := by
  unfold taggedHistoryLaw
  simp only [Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  exact bind_smul_right_discrete ν c _

theorem taggedHistoryLaw_none (ν : Measure (FiniteMarkov.History Forest)) :
    taggedHistoryLaw ν (Measure.dirac none) = ν.map (fun h => (⟨h, none⟩ : ShorterView)) := by
  unfold taggedHistoryLaw
  simp only [Measure.map_dirac' (measurable_of_countable _)]
  exact Measure.bind_dirac_eq_map ν measurable_from_top

theorem taggedHistoryLaw_bind_none (ν : Measure (FiniteMarkov.History Forest)) (N : ℕ)
    (hN : 2 ≤ N) (hc : ∀ᵐ h ∂ν, h.current.forest.roots.card = N) :
    (taggedHistoryLaw ν (Measure.dirac none)).bind (shorterViewStep N) =
      taggedHistoryLaw (ν.bind shorterHistoryStep) (Measure.dirac none) := by
  rw [taggedHistoryLaw_none,
    Measure.bind_map (m := ν) (f := fun h => (⟨h, none⟩ : ShorterView))
      (g := shorterViewStep N) measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    taggedHistoryLaw_none,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hc] with h hh
  simp only [shorterViewStep, shorterHistoryStep,
    Measure.map_map measurable_from_top measurable_from_top]
  rw [← joinPositions_orderedLaw h.current (by omega), hh,
    Measure.map_map measurable_from_top (measurable_of_countable _)]
  rfl

theorem taggedHistoryLaw_bind_pending (ν : Measure (FiniteMarkov.History Forest)) (N : ℕ)
    (hN : 2 ≤ N) (hc : ∀ᵐ h ∂ν, h.current.forest.roots.card = N) :
    (taggedHistoryLaw ν ((positivePairLaw N).map some)).bind (shorterViewStep N) =
      taggedHistoryLaw (ν.bind shorterHistoryStep) (freshPendingLaw N) := by
  unfold taggedHistoryLaw
  rw [Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hc] with h hh
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change ((positivePairLaw N).map (fun p => (⟨h, some p⟩ : ShorterView))).bind
    (shorterViewStep N) = _
  rw [Measure.bind_map (m := positivePairLaw N)
      (f := fun p => (⟨h, some p⟩ : ShorterView)) (g := shorterViewStep N)
      (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  change (positivePairLaw N).bind (fun p => (freshPendingLaw N).map
    (fun q => (⟨h.push (joinPositions h.current (lowerPair p)), q⟩ : ShorterView))) = _
  rw [← positivePairLaw_shorterHistoryStep N hN h hh,
    Measure.bind_map (m := positivePairLaw N)
      (f := fun p => h.push (joinPositions h.current (lowerPair p)))
      (g := fun h : FiniteMarkov.History Forest =>
        (freshPendingLaw N).map (fun q => (⟨h, q⟩ : ShorterView)))
      (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]

/-- Both branches update the complete shorter history by the same ordinary
join law; only the independent metadata mixture changes. -/
theorem taggedHistoryLaw_step (ν : Measure (FiniteMarkov.History Forest)) (N : ℕ)
    (hN : 2 ≤ N) (hc : ∀ᵐ h ∂ν, h.current.forest.roots.card = N) (a b : ℝ≥0∞) :
    (taggedHistoryLaw ν (pendingMetadataLaw N a b)).bind (shorterViewStep N) =
      taggedHistoryLaw (ν.bind shorterHistoryStep)
        (pendingMetadataLaw (N - 1)
          (a + b * (1 - pendingWeight N)) (b * pendingWeight N)) := by
  rw [← pendingMetadataLaw_step N hN a b]
  unfold pendingMetadataLaw
  rw [taggedHistoryLaw_add, taggedHistoryLaw_smul, taggedHistoryLaw_smul,
    bind_add_left_discrete, Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    taggedHistoryLaw_bind_none ν N hN hc, taggedHistoryLaw_bind_pending ν N hN hc,
    taggedHistoryLaw_add, taggedHistoryLaw_smul, taggedHistoryLaw_smul]

noncomputable def shorterCoalescentHistoryLaw (F : Forest) (t : ℕ) :
    Measure (FiniteMarkov.History Forest) :=
  FiniteMarkov.historyLaw (Measure.dirac F) (fun _ => joinLaw) t

theorem shorterCoalescentHistoryLaw_succ (F : Forest) (t : ℕ) :
    shorterCoalescentHistoryLaw F (t + 1) =
      (shorterCoalescentHistoryLaw F t).bind shorterHistoryStep := rfl

theorem shorterCoalescentHistoryLaw_ae_card (F : Forest) (t : ℕ)
    (ht : t ≤ F.forest.roots.card - 1) :
    ∀ᵐ h ∂shorterCoalescentHistoryLaw F t,
      h.current.forest.roots.card = F.forest.roots.card - t := by
  induction t with
  | zero =>
    simp only [shorterCoalescentHistoryLaw, FiniteMarkov.historyLaw,
      Measure.map_dirac' measurable_from_top, FiniteMarkov.History.start, Nat.sub_zero]
    exact (ae_dirac_iff MeasurableSet.of_discrete).mpr rfl
  | succ t ih =>
    rw [ae_iff, shorterCoalescentHistoryLaw_succ,
      Measure.bind_apply MeasurableSet.of_discrete measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [ih (by omega)] with h hh
    have hcard : 2 ≤ h.current.forest.roots.card := by omega
    have hv := h.current.forest.joinLaw_roots_card hcard
    rw [← map_joinLaw h.current] at hv
    have hv' := (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hv
    have he : ∀ᵐ G ∂joinLaw h.current,
        G.forest.roots.card = F.forest.roots.card - (t + 1) := by
      filter_upwards [hv'] with G hG
      omega
    have he' : ∀ᵐ g ∂shorterHistoryStep h,
        g.current.forest.roots.card = F.forest.roots.card - (t + 1) := by
      unfold shorterHistoryStep
      exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mpr he
    simpa only [Pi.zero_apply] using ae_iff.mp he'

/-- The metadata weights are deterministic functions of the starting count
and elapsed time. No coupled-history coordinate enters this recursion. -/
noncomputable def delayedMetadataWeights (k : ℕ) : ℕ → ℝ≥0∞ × ℝ≥0∞
  | 0 => (1 - pendingWeight (k + 1), pendingWeight (k + 1))
  | t + 1 =>
      let w := delayedMetadataWeights k t
      (w.1 + w.2 * (1 - pendingWeight (k - t)), w.2 * pendingWeight (k - t))

theorem delayedMetadataWeights_sum (k : ℕ) (hk : 1 ≤ k) (t : ℕ) (ht : t ≤ k - 1) :
    (delayedMetadataWeights k t).1 + (delayedMetadataWeights k t).2 = 1 := by
  induction t with
  | zero => exact tsub_add_cancel_of_le (pendingWeight_le_one (k + 1) (by omega))
  | succ t ih =>
    have hw := pendingWeight_le_one (k - t) (by omega)
    change (_ + _ * (1 - pendingWeight (k - t))) + _ * pendingWeight (k - t) = 1
    rw [add_assoc, ← mul_add, tsub_add_cancel_of_le hw, mul_one]
    exact ih (by omega)

noncomputable def delayedMetadataLaw (k t : ℕ) : Measure PendingTag :=
  pendingMetadataLaw (k - t) (delayedMetadataWeights k t).1 (delayedMetadataWeights k t).2

theorem delayedMetadataLaw_zero (k : ℕ) (hk : 1 ≤ k) :
    delayedMetadataLaw k 0 = freshPendingLaw (k + 1) := by
  rw [freshPendingLaw_eq (k + 1) (by omega)]
  simp only [delayedMetadataLaw, delayedMetadataWeights, Nat.sub_zero,
    Nat.add_sub_cancel, pendingMetadataLaw]

theorem delayedMetadataLaw_succ (k : ℕ) (t : ℕ) (ht : t + 1 ≤ k - 1) :
    delayedMetadataLaw k (t + 1) =
      (delayedMetadataWeights k t).1 • Measure.dirac none +
        (delayedMetadataWeights k t).2 • freshPendingLaw (k - t) := by
  rw [pendingMetadataLaw_step (k - t) (by omega)]
  have he : k - t - 1 = k - (t + 1) := by omega
  simp only [delayedMetadataLaw, delayedMetadataWeights, he]

theorem delayedMetadataLaw_probability (k : ℕ) (hk : 1 ≤ k) (t : ℕ)
    (ht : t ≤ k - 1) : IsProbabilityMeasure (delayedMetadataLaw k t) := by
  cases t with
  | zero =>
    rw [delayedMetadataLaw_zero k hk]
    let := uniformRootPair_isProbabilityMeasure (Finset.range (k + 1)) (by simpa using (show 2 ≤ k + 1 by omega))
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  | succ t =>
    rw [delayedMetadataLaw_succ k t ht]
    let := uniformRootPair_isProbabilityMeasure (Finset.range (k - t)) (by simpa using (show 2 ≤ k - t by omega))
    have hη : IsProbabilityMeasure (freshPendingLaw (k - t)) :=
      Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
    constructor
    simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      using delayedMetadataWeights_sum k hk t (by omega)

/-- Exact joint law of the complete shorter history and its pending metadata.
This supplies the corrected history-independence claim in Algorithm 3. -/
theorem projectedShorterHistoryLaw_eq (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card)
    (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    projectedShorterHistoryLaw F i t =
      taggedHistoryLaw (shorterCoalescentHistoryLaw F t)
        (delayedMetadataLaw F.forest.roots.card t) := by
  induction t with
  | zero =>
    rw [projectedShorterHistoryLaw_zero F hi, delayedMetadataLaw_zero _ hF]
    simp only [shorterCoalescentHistoryLaw, FiniteMarkov.historyLaw,
      Measure.map_dirac' measurable_from_top, taggedHistoryLaw,
      Measure.dirac_bind measurable_from_top]
  | succ t ih =>
    rw [projectedShorterHistoryLaw_succ F hi t ht, ih (by omega)]
    change (taggedHistoryLaw (shorterCoalescentHistoryLaw F t)
      (pendingMetadataLaw _ _ _)).bind _ = _
    rw [taggedHistoryLaw_step _ _ (by omega)
      (shorterCoalescentHistoryLaw_ae_card F t (by omega)),
      ← shorterCoalescentHistoryLaw_succ]
    have he : F.forest.roots.card - t - 1 = F.forest.roots.card - (t + 1) := by omega
    simp only [delayedMetadataLaw, delayedMetadataWeights, he]

theorem taggedHistoryLaw_history (ν : Measure (FiniteMarkov.History Forest))
    (η : Measure PendingTag) [IsProbabilityMeasure η] :
    (taggedHistoryLaw ν η).map ShorterView.history = ν := by
  rw [taggedHistoryLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  simp only [Measure.map_map measurable_from_top (measurable_of_countable _), Function.comp_def]
  have he : (fun h : FiniteMarkov.History Forest => η.map (fun _ => h)) = Measure.dirac := by
    funext h
    simp only [Measure.map_const, measure_univ, one_smul]
  rw [he, Measure.bind_dirac]

theorem taggedHistoryLaw_pair (ν : Measure (FiniteMarkov.History Forest))
    (η : Measure PendingTag) [SFinite η] :
    (taggedHistoryLaw ν η).map (fun v => (v.history, v.tag)) = ν.prod η := by
  rw [taggedHistoryLaw,
    Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    Measure.prod_eq_of_sfinite]
  congr 1
  funext h
  rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
  rfl

/-- Genuine independence from the entire shorter history. The metadata law
retains the original uniform positive pair only before first use. -/
theorem delayedHistoryLaw_shorter_pendingTag (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card)
    (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    (delayedHistoryLaw F i t).map (fun h =>
      (FiniteMarkov.History.map InitializationSample.shorter h, pendingTag h.current)) =
      (shorterCoalescentHistoryLaw F t).prod (delayedMetadataLaw F.forest.roots.card t) := by
  let := delayedMetadataLaw_probability F.forest.roots.card hF t ht
  have hh := congrArg (fun μ : Measure ShorterView => μ.map (fun v => (v.history, v.tag)))
    (projectedShorterHistoryLaw_eq F hi hF t ht)
  rw [taggedHistoryLaw_pair, projectedShorterHistoryLaw,
    Measure.map_map measurable_from_top measurable_from_top] at hh
  exact hh

/-- Source C5 for the complete post-initialization comparison history, in
the common label space. Identifying the shortened word's relabelled tail is
a separate source interface. -/
theorem delayedHistoryLaw_shorter (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card)
    (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    (delayedHistoryLaw F i t).map (FiniteMarkov.History.map InitializationSample.shorter) =
      shorterCoalescentHistoryLaw F t := by
  let := delayedMetadataLaw_probability F.forest.roots.card hF t ht
  have hh := congrArg (fun μ : Measure ShorterView => μ.map ShorterView.history)
    (projectedShorterHistoryLaw_eq F hi hF t ht)
  rw [taggedHistoryLaw_history, projectedShorterHistoryLaw,
    Measure.map_map measurable_from_top measurable_from_top] at hh
  exact hh

end FreezingGrowth.ReverseOrdered
