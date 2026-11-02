module

public import FreezingGrowth.PairMaximumStatistics
public import FreezingGrowth.ReversePositionPairs

/-! The complete persistent tree and an ordered pair of its actual vertex IDs.
Only active/frozen status is forgotten by the skeleton projection. -/

@[expose] public section
namespace FreezingGrowth.Forward

open MeasureTheory
open scoped Classical ENNReal ProbabilityTheory

structure TreeSkeleton where
  vertices : Finset ℕ
  graph : SimpleGraph ℕ
  parent : ℕ → ℕ
  height : ℕ → ℕ

instance : MeasurableSpace TreeSkeleton := ⊤
instance : DiscreteMeasurableSpace TreeSkeleton := ⟨fun _ => trivial⟩

def State.skeleton (s : State) : TreeSkeleton :=
  ⟨s.vertices, s.graph, s.parent, s.height⟩

@[simp] theorem skeleton_freeze (s : State) (t v : ℕ) :
    (freeze s t v).skeleton = s.skeleton := rfl

structure TreePairSample where
  tree : TreeSkeleton
  first : ℕ
  second : ℕ

instance : MeasurableSpace TreePairSample := ⊤
instance : DiscreteMeasurableSpace TreePairSample := ⟨fun _ => trivial⟩

def treePairSample (s : State) (p : ℕ × ℕ) : TreePairSample :=
  ⟨s.skeleton, p.1, p.2⟩

noncomputable def activePairSkeletonMean (s : State) (F : TreePairSample → ℝ) : ℝ :=
  FiniteAveraging.distinctPairMean s.active
    (fun u v => if u = v then 0 else F (treePairSample s (u, v)))

theorem average_activePairSkeletonMean_freeze {s : State} (hs : 3 ≤ s.active.card)
    (t : ℕ) (F : TreePairSample → ℝ) :
    (∑ v ∈ s.active, activePairSkeletonMean (freeze s t v) F) / s.active.card =
      activePairSkeletonMean s F := by
  simpa only [activePairSkeletonMean, treePairSample, State.skeleton, freeze] using
    FiniteAveraging.average_distinctPairMean_erase s.active
      (fun u v => if u = v then 0 else F (treePairSample s (u, v)))
      hs (by intros; simp)

theorem transitionLaw_activePairSkeletonMean_freeze {s : State}
    (hs : 3 ≤ s.active.card) (t : ℕ) (F : TreePairSample → ℝ) :
    (∫ s', activePairSkeletonMean s' F ∂transitionLaw s t false) =
      activePairSkeletonMean s F := by
  rw [transitionLaw_integral s t false (Finset.card_pos.mp (by omega))]
  convert average_activePairSkeletonMean_freeze hs t F using 1
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp [step, hv]

theorem treeLaw_activePairSkeletonMean_freeze (x : SignSequence) (n : ℕ)
    (hx : x (n + 1) = false) (hc : ∀ᵐ s ∂treeLaw x n, 3 ≤ s.active.card)
    (F : TreePairSample → ℝ) :
    (∫ s, activePairSkeletonMean s F ∂treeLaw x (n + 1)) =
      ∫ s, activePairSkeletonMean s F ∂treeLaw x n := by
  rw [treeLaw_integral_succ_state, hx]
  apply integral_congr_ae
  filter_upwards [hc] with s hs
  exact transitionLaw_activePairSkeletonMean_freeze hs _ F

theorem activePairSkeletonMean_eq_integral (s : State) (hs : 2 ≤ s.active.card)
    (F : TreePairSample → ℝ) :
    activePairSkeletonMean s F = ∫ p, F (treePairSample s p) ∂uniformRootPair s.active := by
  have he : s.active.offDiag =
      (s.active ×ˢ s.active).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsum : (∑ p ∈ s.active.offDiag, F (treePairSample s p)) =
      FiniteAveraging.pairSum s.active
        (fun u v => if u = v then 0 else F (treePairSample s (u, v))) := by
    rw [he, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases huv : u = v <;> simp [huv]
  unfold activePairSkeletonMean FiniteAveraging.distinctPairMean
  rw [← hsum, ← card_offDiag_real s.active (by omega)]
  unfold uniformRootPair Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro p _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    exact ENNReal.inv_ne_top.mpr (by
      exact_mod_cast (offDiag_nonempty_of_two_le_card hs).card_pos.ne')

noncomputable def activeTreePairLaw (s : State) : Measure TreePairSample :=
  (uniformRootPair s.active).map (treePairSample s)

noncomputable def treePairLaw (x : SignSequence) (n : ℕ) : Measure TreePairSample :=
  (treeLaw x n).bind activeTreePairLaw

theorem treePairLaw_probability (x : SignSequence) (n : ℕ)
    (hc : ∀ᵐ s ∂treeLaw x n, 2 ≤ s.active.card) : IsProbabilityMeasure (treePairLaw x n) := by
  unfold treePairLaw
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [hc] with s hs
  let := uniformRootPair_isProbabilityMeasure s.active hs
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr
    inferInstance

theorem treePairLaw_ae (x : SignSequence) (n : ℕ) (P : TreePairSample → Prop)
    (hP : ∀ᵐ s ∂treeLaw x n, ∀ p ∈ s.active.offDiag, P (treePairSample s p)) :
    ∀ᵐ z ∂treePairLaw x n, P z := by
  rw [ae_iff, treePairLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [hP] with s hs
  rw [activeTreePairLaw, Measure.map_apply (measurable_of_countable _) (by trivial)]
  change (uniformRootPair s.active) {p | ¬P (treePairSample s p)} = 0
  apply ae_iff.mp
  exact (ReverseHeightList.uniformRootPair_ae_offDiag s.active).mono (fun p hp => hs p hp)

noncomputable def reachableTreePairs (x : SignSequence) (n : ℕ) : Finset TreePairSample :=
  (reachableStates x n).biUnion fun s => s.active.offDiag.image (treePairSample s)

theorem treePairLaw_ae_reachable (x : SignSequence) (n : ℕ) :
    ∀ᵐ z ∂treePairLaw x n, z ∈ reachableTreePairs x n := by
  apply treePairLaw_ae
  filter_upwards [treeLaw_ae_reachable x n] with s hs
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

theorem treePairLaw_integrable (x : SignSequence) (n : ℕ)
    (hc : ∀ᵐ s ∂treeLaw x n, 2 ≤ s.active.card) (F : TreePairSample → ℝ) :
    Integrable F (treePairLaw x n) := by
  let := treePairLaw_probability x n hc
  let C : ℝ := ∑ z ∈ reachableTreePairs x n, |F z|
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treePairLaw_ae_reachable x n] with z hz
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun z _ => abs_nonneg (F z)) hz

theorem treePairLaw_integral (x : SignSequence) (n : ℕ)
    (hc : ∀ᵐ s ∂treeLaw x n, 2 ≤ s.active.card) (F : TreePairSample → ℝ) :
    (∫ z, F z ∂treePairLaw x n) = ∫ s, activePairSkeletonMean s F ∂treeLaw x n := by
  let K : ProbabilityTheory.Kernel State TreePairSample :=
    ⟨activeTreePairLaw, measurable_from_top⟩
  have hi := treePairLaw_integrable x n hc F
  have hi' : Integrable F ((K ∘ₖ ProbabilityTheory.Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, treePairLaw, ProbabilityTheory.Kernel.coe_mk,
      ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hi
  have hh := ProbabilityTheory.Kernel.integral_comp hi'
  have he : (∫ z, F z ∂treePairLaw x n) =
      ∫ s, (∫ z, F z ∂activeTreePairLaw s) ∂treeLaw x n := by
    simpa only [K, treePairLaw, ProbabilityTheory.Kernel.coe_mk,
      ProbabilityTheory.Kernel.comp_apply, ProbabilityTheory.Kernel.const_apply] using hh
  rw [he]
  apply integral_congr_ae
  filter_upwards [hc] with s hs
  rw [activeTreePairLaw, integral_map (measurable_of_countable _).aemeasurable
    measurable_from_top.aestronglyMeasurable]
  exact (activePairSkeletonMean_eq_integral s hs F).symm

end FreezingGrowth.Forward
